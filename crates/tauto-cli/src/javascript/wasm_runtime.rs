// Private Wasm ABI. Addresses never leave the instance. Every escaped view
// retains the loans of all borrowed arguments, following Nib's single lifetime.
use serde_json::{Value, json};
use std::{
    any::Any,
    cell::{Cell as AbiCount, RefCell as AbiCell, UnsafeCell},
    collections::BTreeMap,
    rc::Rc as HandleRc,
};
struct Entry {
    // Drop the referent (including opaque view destructors) before its parents.
    id: u32,
    value: Box<dyn Any>,
    address: Box<dyn Any>,
    is_view: bool,
    parents: Vec<HandleRc<Loan>>,
    loans: AbiCount<i32>,
    mutable: bool,
}
struct Pointer<T: ?Sized>(*mut T);
struct Allocation<T> {
    value: UnsafeCell<Option<T>>,
}
struct Loan {
    entry: HandleRc<Entry>,
    mutable: bool,
}
impl Drop for Loan {
    fn drop(&mut self) {
        self.entry.loans.set(if self.mutable {
            0
        } else {
            self.entry.loans.get() - 1
        });
    }
}
#[derive(Default)]
struct Frame {
    loans: AbiCell<Vec<HandleRc<Loan>>>,
    scoped: bool,
    views: AbiCell<Vec<u32>>,
}
impl Drop for Frame {
    fn drop(&mut self) {
        if self.scoped {
            for id in self.views.get_mut().drain(..).rev() {
                retire(id);
            }
        }
    }
}
impl Frame {
    fn scoped() -> Self {
        {
            let mut frame = Self::default();
            frame.scoped = true;
            frame
        }
    }
    fn acquire(&self, v: &Value, mutable: bool) -> HandleRc<Entry> {
        let entry = handle(v);
        assert!(
            !mutable || entry.mutable,
            "cannot mutate a shared wasm view"
        );
        let count = entry.loans.get();
        assert!(
            if mutable { count == 0 } else { count >= 0 },
            "conflicting wasm borrow"
        );
        entry.loans.set(if mutable {
            -1
        } else {
            count.checked_add(1).expect("too many wasm borrows")
        });
        self.loans.borrow_mut().push(HandleRc::new(Loan {
            entry: entry.clone(),
            mutable,
        }));
        entry
    }
    fn read<T: 'static>(&self, v: &Value) -> &T {
        let h = self.acquire(v, false);
        // SAFETY: this frame owns the shared loan until all returned references
        // are dead. Owned allocations cannot move while loaned; view allocations
        // retain their ancestors. Only this module can manufacture Pointer<T>.
        unsafe { &*pointer::<T>(&h) }
    }
    fn write<T: 'static>(&self, v: &Value) -> &mut T {
        let h = self.acquire(v, true);
        // SAFETY: acquire granted the only mutable loan; see read above.
        unsafe { &mut *pointer::<T>(&h) }
    }
    fn slice<T: 'static>(&self, v: &Value) -> &[T] {
        let h = self.acquire(v, false);
        unsafe {
            if let Some(p) = h.address.downcast_ref::<Pointer<[T]>>() {
                &*p.0
            } else {
                (&*pointer::<Vec<T>>(&h)).as_slice()
            }
        }
    }
    fn slice_mut<T: 'static>(&self, v: &Value) -> &mut [T] {
        let h = self.acquire(v, true);
        unsafe {
            if let Some(p) = h.address.downcast_ref::<Pointer<[T]>>() {
                &mut *p.0
            } else {
                (&mut *pointer::<Vec<T>>(&h)).as_mut_slice()
            }
        }
    }
}
// SAFETY: callers acquire a compatible loan before dereferencing this pointer.
unsafe fn pointer<T: 'static>(h: &Entry) -> *mut T {
    h.address
        .downcast_ref::<Pointer<T>>()
        .expect("wrong wasm handle type")
        .0
}

thread_local! {
    static INPUT: AbiCell<Vec<u8>> = const { AbiCell::new(Vec::new()) };
    static OUTPUT: AbiCell<Vec<u8>> = const { AbiCell::new(Vec::new()) };
    static HANDLES: AbiCell<BTreeMap<u32, HandleRc<Entry>>> = const { AbiCell::new(BTreeMap::new()) };
    static CALL_RESULTS: AbiCell<BTreeMap<u32,Value>> = const {AbiCell::new(BTreeMap::new())};
    static CALLBACK_RESULTS: AbiCell<BTreeMap<u32,Value>> = const {AbiCell::new(BTreeMap::new())};
    static NEXT: AbiCount<u32> = const { AbiCount::new(1) };
}
fn insert_entry(
    value: Box<dyn Any>,
    address: Box<dyn Any>,
    parents: Vec<HandleRc<Loan>>,
    mutable: bool,
    is_view: bool,
) -> u32 {
    let id = NEXT.with(|n| {
        let id = n.get();
        n.set(id.checked_add(1).expect("wasm handle space exhausted"));
        id
    });
    HANDLES.with(|h| {
        h.borrow_mut().insert(
            id,
            HandleRc::new(Entry {
                id,
                value,
                address,
                is_view,
                parents,
                loans: AbiCount::new(0),
                mutable,
            }),
        );
    });
    id
}
fn insert<T: 'static>(value: Box<T>, parents: Vec<HandleRc<Loan>>, mutable: bool) -> u32 {
    // The allocation is stable before its pointer is taken. Moving an Rc never
    // moves or retags its referent. All subsequent access goes through this
    // UnsafeCell, guarded by the entry's loans.
    let allocation = HandleRc::new(Allocation {
        value: UnsafeCell::new(Some(*value)),
    });
    let ptr = Pointer(unsafe { &mut *allocation.value.get() }.as_mut().unwrap() as *mut T);
    insert_entry(Box::new(allocation), Box::new(ptr), parents, mutable, false)
}
fn descends(entry: &Entry, id: u32) -> bool {
    entry.id == id || entry.parents.iter().any(|p| descends(&p.entry, id))
}
fn retire(id: u32) {
    // Callback references point into a live Rust stack. Remove every derived
    // view before that stack resumes, including opaque views with destructors.
    let removed = HANDLES.with(|h| {
        let mut h = h.borrow_mut();
        let ids = h
            .iter()
            .filter_map(|(key, e)| descends(e, id).then_some(*key))
            .collect::<Vec<_>>();
        ids.into_iter()
            .filter_map(|key| h.remove(&key))
            .collect::<Vec<_>>()
    });
    drop(removed);
}
fn store<T: 'static>(value: T, name: &str) -> Value {
    json!({"kind":"Opaque","handle":insert(Box::new(value),vec![],true),"name":name,"resource":true})
}
/// A handle number from the host; one past `u32` is refused, not cut to another handle.
fn handle_id(v: &Value) -> u32 {
    v["handle"]
        .as_u64()
        .and_then(|n| u32::try_from(n).ok())
        .expect("invalid wasm handle")
}
fn handle(v: &Value) -> HandleRc<Entry> {
    HANDLES.with(|h| {
        h.borrow()
            .get(&handle_id(v))
            .expect("released wasm handle")
            .clone()
    })
}
fn take<T: 'static>(v: &Value, frame: &Frame) -> T {
    let h = handle(v);
    assert_eq!(h.loans.get(), 0, "cannot move a borrowed wasm value");
    assert!(!h.is_view, "cannot move out of a wasm view");
    frame.loans.borrow_mut().extend(h.parents.iter().cloned());
    // SAFETY: no loans exist and no reference to the allocation can escape
    // without a loan. Removing the owned box leaves every stale handle empty.
    let allocation = h
        .value
        .downcast_ref::<HandleRc<Allocation<T>>>()
        .expect("wrong wasm handle type");
    let value = unsafe { &mut *allocation.value.get() }
        .take()
        .expect("consumed wasm handle");
    release(handle_id(v));
    value
}
fn shared<T: Clone + 'static>(v: &Value, frame: &Frame) -> T {
    frame.read::<T>(v).clone()
}
// SAFETY: generated call sites only pass references derived from stable input
// allocations or 'static data. Callback references use scoped views instead.
unsafe fn view<T: ?Sized + 'static>(
    ptr: *mut T,
    mutable: bool,
    codec: u32,
    opaque: bool,
    frame: &Frame,
) -> Value {
    let id = insert_entry(
        Box::new(()),
        Box::new(Pointer(ptr)),
        frame.loans.borrow().clone(),
        mutable,
        true,
    );
    if frame.scoped {
        frame.views.borrow_mut().push(id);
    }
    json!({"kind":"View","handle":id,"mutable":mutable,"codec":codec,"opaque":opaque,"resource":true})
}
fn ctor(owner: &str, tag: &str, names: Value, fields: Value, is_struct: bool) -> Value {
    json!({"owner":owner,"tag":tag,"names":names,"fields":fields,"struct":is_struct})
}
fn input() -> Value {
    INPUT.with(|v| serde_json::from_slice(&v.borrow()).expect("invalid wasm input"))
}
fn output(v: Value) {
    OUTPUT.with(|b| *b.borrow_mut() = serde_json::to_vec(&v).expect("invalid wasm output"));
}
#[cfg(target_family = "wasm")]
#[link(wasm_import_module = "tauto")]
unsafe extern "C" {
    fn callback(id: u32, request: u32);
    fn callback_drop(id: u32);
}
#[cfg(not(target_family = "wasm"))]
unsafe fn callback(_: u32, _: u32) {
    unreachable!("host callback in arena test")
}
#[cfg(not(target_family = "wasm"))]
unsafe fn callback_drop(_: u32) {
    unreachable!("host callback in arena test")
}
struct Callback(u32);
impl Callback {
    fn call(&self, args: Value) -> Value {
        host_call(self.0, args)
    }
}
impl Drop for Callback {
    fn drop(&mut self) {
        unsafe { callback_drop(self.0) }
    }
}
fn host_call(id: u32, args: Value) -> Value {
    let request = NEXT.with(|n| {
        let id = n.get();
        n.set(id.checked_add(1).expect("wasm request space exhausted"));
        id
    });
    output(args);
    unsafe { callback(id, request) };
    CALLBACK_RESULTS.with(|r| {
        r.borrow_mut()
            .remove(&request)
            .expect("missing callback response")
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn callback_result(request: u32) {
    let value = input();
    CALLBACK_RESULTS.with(|r| {
        r.borrow_mut().insert(request, value);
    });
}
#[unsafe(no_mangle)]
pub extern "C" fn result_take(ticket: u32) {
    let value = CALL_RESULTS.with(|r| r.borrow_mut().remove(&ticket).expect("missing wasm result"));
    output(value);
}

#[unsafe(no_mangle)]
pub extern "C" fn input_clear() {
    INPUT.with(|b| b.borrow_mut().clear());
}
#[unsafe(no_mangle)]
pub extern "C" fn input_byte(b: u32) {
    INPUT.with(|v| v.borrow_mut().push(u8::try_from(b).expect("invalid byte")));
}
#[unsafe(no_mangle)]
pub extern "C" fn output_len() -> u32 {
    OUTPUT.with(|v| v.borrow().len().try_into().expect("wasm output too large"))
}
#[unsafe(no_mangle)]
pub extern "C" fn output_byte(i: u32) -> u32 {
    OUTPUT.with(|v| u32::from(v.borrow()[i as usize]))
}
#[unsafe(no_mangle)]
pub extern "C" fn release(id: u32) {
    let removed = HANDLES.with(|h| h.borrow_mut().remove(&id));
    drop(removed);
}
#[unsafe(no_mangle)]
pub extern "C" fn root_ready(id: u32) -> u32 {
    HANDLES.with(|h| u32::from(h.borrow().get(&id).is_some_and(|v| v.loans.get() == 0)))
}
#[unsafe(no_mangle)]
pub extern "C" fn dispose() {
    let entries = HANDLES.with(|h| std::mem::take(&mut *h.borrow_mut()));
    drop(entries);
    INPUT.with(|b| b.borrow_mut().clear());
    OUTPUT.with(|b| b.borrow_mut().clear());
}
#[unsafe(no_mangle)]
pub extern "C" fn invoke(index: u32, ticket: u32) {
    let args = input();
    let value = dispatch(index, &args);
    CALL_RESULTS.with(|r| {
        r.borrow_mut().insert(ticket, value);
    });
}
#[unsafe(no_mangle)]
pub extern "C" fn access(codec: u32, action: u32, ticket: u32) {
    let args = input();
    let value = access_value(codec, action, &args);
    CALL_RESULTS.with(|r| {
        r.borrow_mut().insert(ticket, value);
    });
}
