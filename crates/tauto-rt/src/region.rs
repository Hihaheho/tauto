//! Regions: the memory of `Region(S)` and `RcRegion(S)` and the values put
//! in them (`std/builtin/region.taut`).
//!
//! This is the one module of the runtime that writes unsafe code. What it
//! exports is sound for any safe caller. A value put in a region holds the
//! region's memory through its `Place`, so it points to live memory however
//! long it lives: a hole in the checker of tauto cannot turn into a read of
//! freed memory, and rustc checks the code around it as any other code.
//! (An answer of an effect is handed over as `dyn Any`, which holds no
//! borrow, so a place cannot carry the lifetime of its region's borrow.)
//!
//! A region made by `Region::bump` cuts its blocks from chunks it gets from
//! the global allocator, one block after the other, and gives all its chunks
//! back when it and the values in it are gone. A region made by
//! `Region::heap` puts each value in a `Box`. Dropping a `Placed` drops the
//! value it holds; only its memory waits for the region.
//!
//! A counted region (`RcRegion`) is the same region: it already lives until
//! its last copy and the last value in it are gone. Its values are
//! `RcPlaced`, which borrow nothing (`'static`). The free of a bump region
//! keeps its state, as `BumpPolicy` says, so a dead value's block stays cut
//! until the region goes.

use std::alloc::{self, Layout};
use std::cell::{Cell, RefCell};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;
use std::rc::Rc;

/// A scoped region. Each value put in it holds the region's memory too
/// (through its `Place`), so the memory goes back when the region and every
/// value in it are gone: a value that outlives its region in the program
/// still points to live memory. A copy is the same region: the handler of
/// `place` holds one.
#[derive(Clone)]
pub struct Region {
    arena: Rc<Arena>,
}

struct Arena {
    bump: Option<Bump>,
}

/// The chunks of a bump region. The last one is cut from `next` to `end`.
struct Bump {
    chunks: RefCell<Vec<(NonNull<u8>, Layout)>>,
    next: Cell<usize>,
    end: Cell<usize>,
    step: usize,
}

/// The alignment of each chunk.
const CHUNK_ALIGN: usize = 16;

impl Region {
    /// A bump region whose first chunk has `size` bytes and that grows by
    /// chunks of at least `step` bytes.
    pub fn bump(size: usize, step: usize) -> Region {
        let b = Bump {
            chunks: RefCell::new(Vec::new()),
            next: Cell::new(0),
            end: Cell::new(0),
            step: step.max(1),
        };
        if size > 0 {
            b.grow(size);
        }
        Region {
            arena: Rc::new(Arena { bump: Some(b) }),
        }
    }

    /// A region that puts every value on the heap.
    pub fn heap() -> Region {
        Region {
            arena: Rc::new(Arena { bump: None }),
        }
    }

    /// Where a value of `T` goes: a block of this region, new for each value.
    pub fn place<T>(&self) -> Place<T> {
        Place {
            arena: self.arena.clone(),
            _t: PhantomData,
        }
    }

    /// The bytes of the chunks this region holds.
    pub fn reserved(&self) -> usize {
        self.arena
            .bump
            .as_ref()
            .map_or(0, |b| b.chunks.borrow().iter().map(|(_, l)| l.size()).sum())
    }
}

impl Bump {
    /// Adds a chunk of at least `size` bytes and cuts the next blocks from it.
    fn grow(&self, size: usize) {
        let layout = Layout::from_size_align(size.max(1), CHUNK_ALIGN)
            .unwrap_or_else(|_| alloc::handle_alloc_error(Layout::new::<u8>()));
        // SAFETY: `layout` has a size of at least one byte.
        let p = unsafe { alloc::alloc(layout) };
        let Some(p) = NonNull::new(p) else {
            alloc::handle_alloc_error(layout)
        };
        self.chunks.borrow_mut().push((p, layout));
        let start = p.as_ptr() as usize;
        self.next.set(start);
        self.end.set(start + layout.size());
    }

    /// A block for `layout` that no other block overlaps.
    fn alloc(&self, layout: Layout) -> NonNull<u8> {
        if let Some(p) = self.cut(layout) {
            return p;
        }
        let need = layout.size() + layout.align();
        self.grow(need.max(self.step));
        self.cut(layout)
            .expect("a new chunk holds a block of its size")
    }

    fn cut(&self, layout: Layout) -> Option<NonNull<u8>> {
        let chunks = self.chunks.borrow();
        let (base, _) = chunks.last()?;
        let start = self.next.get().checked_next_multiple_of(layout.align())?;
        let stop = start.checked_add(layout.size())?;
        if stop > self.end.get() {
            return None;
        }
        self.next.set(stop);
        let offset = start - base.as_ptr() as usize;
        // SAFETY: `start..stop` lies inside the last chunk, so the offset
        // stays in the allocation `base` points to. Deriving the pointer from
        // `base` keeps its provenance.
        Some(unsafe { base.add(offset) })
    }
}

impl Drop for Bump {
    fn drop(&mut self) {
        for (p, layout) in self.chunks.get_mut().drain(..) {
            // SAFETY: each chunk was allocated by `grow` with this layout and
            // is given back once. No value is left in it: each holds the
            // arena, so the arena is dropped after the last of them.
            unsafe { alloc::dealloc(p.as_ptr(), layout) };
        }
    }
}

impl fmt::Debug for Region {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(if self.arena.bump.is_some() {
            "Region(bump)"
        } else {
            "Region(heap)"
        })
    }
}

/// A counted region: the same region, whose places borrow nothing.
pub type RcRegion = Region;

/// Where a value of `T` goes in a counted region or on the heap.
pub type RcPlace<T> = Place<T>;

/// A value of `T` in a counted region or on the heap.
pub type RcPlaced<T> = Placed<'static, T>;

/// Where a value of `T` goes: a block of a region, new for each value put.
pub struct Place<T> {
    arena: Rc<Arena>,
    _t: PhantomData<fn() -> T>,
}

impl<T> Clone for Place<T> {
    fn clone(&self) -> Self {
        Place {
            arena: self.arena.clone(),
            _t: PhantomData,
        }
    }
}

impl<T> PartialEq for Place<T> {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.arena, &other.arena)
    }
}

impl<T> Eq for Place<T> {}

impl<T> Hash for Place<T> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        Rc::as_ptr(&self.arena).hash(h)
    }
}

impl<T> fmt::Debug for Place<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(if self.arena.bump.is_some() {
            "Place(bump)"
        } else {
            "Place(heap)"
        })
    }
}

impl<T> Place<T> {
    /// Each value put here goes on the heap.
    pub fn heap() -> Place<T> {
        Region::heap().place()
    }

    /// Puts `x` in a new block of the region.
    pub fn put<'r>(self, x: T) -> Placed<'r, T> {
        let slot = Slot { value: x, at: self };
        let ptr = match &slot.at.arena.bump {
            Some(b) => {
                let p = b.alloc(Layout::new::<Slot<T>>()).cast::<Slot<T>>();
                // SAFETY: `p` is aligned for `Slot<T>` and points to a block
                // of its size that nothing else uses.
                unsafe { p.as_ptr().write(slot) };
                p
            }
            None => NonNull::from(Box::leak(Box::new(slot))),
        };
        Placed {
            ptr,
            _own: PhantomData,
        }
    }
}

/// What a `Placed` points to: the value and where it is.
pub struct Slot<T> {
    pub value: T,
    pub at: Place<T>,
}

/// A value of `T` in a block of a region. It is the one holder of the value:
/// dropping it drops the value, and the block's memory goes back with the
/// region. It reads as its `Slot` (`Deref`, `DerefMut`), so `p.value` is the
/// value. `'r` is the borrow of the region the checker sees.
pub struct Placed<'r, T> {
    ptr: NonNull<Slot<T>>,
    _own: PhantomData<(Slot<T>, &'r ())>,
}

impl<'r, T> Placed<'r, T> {
    /// `x` put where `at` says.
    pub fn new(value: T, at: Place<T>) -> Self {
        at.put(value)
    }

    /// Moves the value and its place out. The block stays with the region.
    pub fn into_slot(self) -> Slot<T> {
        let this = std::mem::ManuallyDrop::new(self);
        // SAFETY: the slot is read once: `this` is never dropped.
        let slot = unsafe { this.ptr.as_ptr().read() };
        if slot.at.arena.bump.is_none() {
            // SAFETY: a heap slot is the `Box` `put` leaked, whose value was
            // just moved out; the `MaybeUninit` frees it without a drop.
            drop(unsafe {
                Box::from_raw(this.ptr.as_ptr().cast::<std::mem::MaybeUninit<Slot<T>>>())
            });
        }
        slot
    }

    pub fn into_inner(self) -> T {
        self.into_slot().value
    }
}

impl<T> Drop for Placed<'_, T> {
    fn drop(&mut self) {
        // Moving the slot out first keeps the arena (in `at`) alive until the
        // block is no longer touched.
        let this = Placed {
            ptr: self.ptr,
            _own: PhantomData::<(Slot<T>, &())>,
        };
        drop(this.into_slot());
    }
}

impl<T> Deref for Placed<'_, T> {
    type Target = Slot<T>;
    fn deref(&self) -> &Slot<T> {
        // SAFETY: `ptr` points to a live slot this `Placed` owns, and the
        // shared borrow of `self` keeps it from being changed.
        unsafe { self.ptr.as_ref() }
    }
}

impl<T> DerefMut for Placed<'_, T> {
    fn deref_mut(&mut self) -> &mut Slot<T> {
        // SAFETY: as in `deref`, and the borrow of `self` is unique.
        unsafe { self.ptr.as_mut() }
    }
}

/// A copy is a new value in a new block of the same region.
impl<T: Clone> Clone for Placed<'_, T> {
    fn clone(&self) -> Self {
        self.at.clone().put(self.value.clone())
    }
}

impl<T: PartialEq> PartialEq for Placed<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<T: Eq> Eq for Placed<'_, T> {}

impl<T: Hash> Hash for Placed<'_, T> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.value.hash(h)
    }
}

impl<T: fmt::Debug> fmt::Debug for Placed<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.value.fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bump_values_read_back() {
        let r = Region::bump(64, 64);
        let p = r.place::<u64>();
        let xs: Vec<Placed<'_, u64>> = (0..100).map(|i| p.clone().put(i)).collect();
        for (i, x) in xs.iter().enumerate() {
            assert_eq!(x.value, i as u64);
        }
        assert!(r.reserved() >= 1600);
    }

    #[test]
    fn mixed_alignments_do_not_overlap() {
        let r = Region::bump(8, 8);
        let a = r.place::<u8>().put(1);
        let b = r.place::<u128>().put(2);
        let mut c = r.place::<[u8; 3]>().put([3, 4, 5]);
        let d = r.place::<()>().put(());
        c.value[1] = 9;
        assert_eq!((a.value, b.value, c.value, d.value), (1, 2, [3, 9, 5], ()));
        assert_eq!(
            &b.value as *const u128 as usize % std::mem::align_of::<u128>(),
            0
        );
    }

    #[test]
    fn a_value_bigger_than_the_step_gets_its_own_chunk() {
        let r = Region::bump(0, 4);
        let x = r.place::<[u64; 32]>().put([7; 32]);
        assert_eq!(x.value[31], 7);
    }

    #[test]
    fn drops_run_once() {
        let n = Rc::new(());
        for r in [Region::bump(16, 16), Region::heap()] {
            let p = r.place::<Rc<()>>();
            let a = p.clone().put(n.clone());
            let b = a.clone();
            let c = p.put(n.clone());
            assert_eq!(Rc::strong_count(&n), 4);
            drop(a);
            let inner = c.into_inner();
            assert_eq!(Rc::strong_count(&n), 3);
            drop((b, inner));
            assert_eq!(Rc::strong_count(&n), 1);
        }
    }

    #[test]
    fn a_value_outlives_its_region() {
        let x = {
            let r = Region::bump(16, 16);
            r.place::<Vec<u8>>().put(vec![1, 2, 3])
        };
        assert_eq!(x.value, [1, 2, 3]);
    }

    #[test]
    fn a_counted_value_outlives_every_copy_of_its_region() {
        let x: RcPlaced<Vec<u8>> = {
            let r = RcRegion::bump(16, 16);
            let p: RcPlace<Vec<u8>> = r.clone().place();
            drop(r);
            p.put(vec![4, 5])
        };
        assert_eq!(x.value, [4, 5]);
        let h: RcPlaced<u64> = RcPlace::heap().put(3);
        assert_eq!(h.value, 3);
    }

    #[test]
    fn a_tree_of_placed_values() {
        enum Tree<'a> {
            Leaf,
            Branch(Placed<'a, Tree<'a>>, u64, Placed<'a, Tree<'a>>),
        }
        fn build<'a>(p: &Place<Tree<'a>>, n: u64) -> Tree<'a> {
            if n == 0 {
                Tree::Leaf
            } else {
                Tree::Branch(
                    p.clone().put(build(p, n - 1)),
                    n,
                    p.clone().put(build(p, n - 1)),
                )
            }
        }
        fn sum(t: &Tree<'_>) -> u64 {
            match t {
                Tree::Leaf => 0,
                Tree::Branch(l, v, r) => sum(&l.value) + v + sum(&r.value),
            }
        }
        for r in [Region::bump(256, 256), Region::heap()] {
            let t = build(&r.place(), 6);
            assert_eq!(sum(&t), 120);
        }
    }
}
