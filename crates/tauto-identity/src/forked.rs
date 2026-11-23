//! Maps and sets that a copy writes to and hands back what it wrote.
//!
//! Files that do not import one another are declared side by side, each on a
//! copy of one environment, and what each copy wrote is taken back into it.
//! What a copy hands back is what it wrote — added, changed or removed —
//! not what its table holds that the table it was copied from does not: a
//! spelling the library already had and a file gave another meaning is a
//! write as much as a new one is, and taking it back makes it mean what
//! declaring the files in turn makes it mean.
//!
//! Two copies that wrote the same key are not taken in silently: which
//! write would win depends on which copy finished first, not on the order
//! of the files. [`ForkedMap::absorb`] says so, and the files are then
//! declared in turn.
//!
//! What a copy wrote is told apart by when it was written: every write
//! carries the [`generation`] it was made in, and a copy is made in a
//! generation of its own ([`next_generation`]), so that what it hands back
//! is what it wrote since then, whatever was cloned how in between.

use std::collections::hash_map::{Entry, RandomState};
use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasher, Hash};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

static GENERATION: AtomicU64 = AtomicU64::new(1);

/// The generation writes are made in now.
pub fn generation() -> u64 {
    GENERATION.load(Ordering::Relaxed)
}

/// Starts a new generation for a copy made now, and gives the one before
/// it: what the copy writes from now on is what it wrote since then
/// (`subtract(since)`).
pub fn next_generation() -> u64 {
    GENERATION.fetch_add(1, Ordering::Relaxed)
}

/// When each key was last taken in from a copy, by the number of copies
/// taken in so far.
#[derive(Debug)]
struct Taken<K> {
    clock: u64,
    at: Arc<HashMap<K, u64>>,
}

impl<K> Default for Taken<K> {
    fn default() -> Self {
        Self {
            clock: 0,
            at: Arc::default(),
        }
    }
}

impl<K> Clone for Taken<K> {
    fn clone(&self) -> Self {
        Self {
            clock: self.clock,
            at: self.at.clone(),
        }
    }
}

impl<K: Eq + Hash + Clone> Taken<K> {
    /// Notes that `key` is taken in from `copy`, made when `copy` copies
    /// were taken in; false when another copy taken in since wrote it too.
    fn take(&mut self, key: &K, copy: u64) -> bool {
        let at = Arc::make_mut(&mut self.at);
        let alone = at.get(key).is_none_or(|&t| t <= copy);
        at.insert(key.clone(), self.clock);
        alone
    }
}

/// A map whose copies hand back what they wrote (the module comment).
#[derive(Debug)]
pub struct ForkedMap<K, V, S = RandomState> {
    map: HashMap<K, V, S>,
    /// The generation each key was last written in.
    written: HashMap<K, u64>,
    taken: Taken<K>,
}

impl<K, V, S: Default> Default for ForkedMap<K, V, S> {
    fn default() -> Self {
        Self {
            map: HashMap::default(),
            written: HashMap::new(),
            taken: Taken::default(),
        }
    }
}

impl<K: Clone, V: Clone, S: Clone> Clone for ForkedMap<K, V, S> {
    fn clone(&self) -> Self {
        Self {
            map: self.map.clone(),
            written: self.written.clone(),
            taken: self.taken.clone(),
        }
    }
}

impl<K, V, S> std::ops::Deref for ForkedMap<K, V, S> {
    type Target = HashMap<K, V, S>;
    fn deref(&self) -> &HashMap<K, V, S> {
        &self.map
    }
}

impl<K: Eq + Hash, V, S: BuildHasher + Default> From<HashMap<K, V, S>> for ForkedMap<K, V, S> {
    fn from(map: HashMap<K, V, S>) -> Self {
        Self {
            map,
            written: HashMap::new(),
            taken: Taken::default(),
        }
    }
}

impl<K: Eq + Hash, V, S: BuildHasher + Default> FromIterator<(K, V)> for ForkedMap<K, V, S> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        HashMap::from_iter(iter).into()
    }
}

impl<'a, K, V, S> IntoIterator for &'a ForkedMap<K, V, S> {
    type Item = (&'a K, &'a V);
    type IntoIter = std::collections::hash_map::Iter<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.map.iter()
    }
}

impl<K: Eq + Hash + Clone, V, S: BuildHasher> ForkedMap<K, V, S> {
    fn wrote(&mut self, key: K) {
        self.written.insert(key, generation());
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.wrote(key.clone());
        self.map.insert(key, value)
    }

    /// Makes `key` mean `value`, writing it only when that changes it.
    pub fn put(&mut self, key: K, value: V)
    where
        V: PartialEq,
    {
        if self.map.get(&key) != Some(&value) {
            self.insert(key, value);
        }
    }

    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: std::borrow::Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let (key, value) = self.map.remove_entry(key)?;
        self.wrote(key);
        Some(value)
    }

    /// The value of `key` to change in place: counted as written.
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: std::borrow::Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let owned = self.map.get_key_value(key)?.0.clone();
        self.wrote(owned);
        self.map.get_mut(key)
    }

    /// The entry of `key`: counted as written, since what is done with it
    /// is not seen here.
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        self.wrote(key.clone());
        self.map.entry(key)
    }

    pub fn retain(&mut self, mut keep: impl FnMut(&K, &mut V) -> bool) {
        let (written, now) = (&mut self.written, generation());
        self.map.retain(|k, v| {
            let kept = keep(k, v);
            if !kept {
                written.insert(k.clone(), now);
            }
            kept
        });
    }

    pub fn clear(&mut self) {
        let now = generation();
        self.written.extend(self.map.drain().map(|(k, _)| (k, now)));
    }

    /// Gives every key the key `rename` makes of it, keeping the values.
    /// A key that stays as it is is not written.
    pub fn rename_keys(&mut self, mut rename: impl FnMut(&K) -> K) {
        let renamed: Vec<(K, K)> = self
            .map
            .keys()
            .filter_map(|k| {
                let to = rename(k);
                (to != *k).then(|| (k.clone(), to))
            })
            .collect();
        let moved: Vec<(K, V)> = renamed
            .into_iter()
            .filter_map(|(from, to)| self.remove(&from).map(|v| (to, v)))
            .collect();
        for (k, v) in moved {
            self.insert(k, v);
        }
    }

    /// Changes each value in place with `change`, which says whether it
    /// changed it: only those are written.
    pub fn change_values(&mut self, mut change: impl FnMut(&K, &mut V) -> bool) {
        let now = generation();
        for (k, v) in self.map.iter_mut() {
            if change(k, v) {
                self.written.insert(k.clone(), now);
            }
        }
    }

    /// Makes this map `to`, writing only the keys whose values change.
    pub fn set_to(&mut self, mut to: HashMap<K, V, S>)
    where
        V: PartialEq,
    {
        let gone: Vec<K> = self
            .map
            .keys()
            .filter(|k| !to.contains_key(*k))
            .cloned()
            .collect();
        for k in gone {
            self.remove(&k);
        }
        for (k, v) in to.drain() {
            if self.map.get(&k) != Some(&v) {
                self.insert(k, v);
            }
        }
    }

    /// The keys written after generation `since`.
    pub fn written_since(&self, since: u64) -> impl Iterator<Item = &K> {
        self.written
            .iter()
            .filter(move |(_, g)| **g > since)
            .map(|(k, _)| k)
    }

    /// The map itself, for a reader that wants it whole.
    pub fn into_map(self) -> HashMap<K, V, S> {
        self.map
    }

    /// Leaves in this copy only what it wrote after generation `since`
    /// ([`next_generation`]), so that it is small while it waits to be
    /// taken in.
    pub fn subtract(&mut self, since: u64) {
        self.written.retain(|_, g| *g > since);
        let written = &self.written;
        self.map.retain(|k, _| written.contains_key(k));
        self.taken.at = Arc::default();
    }

    /// Takes in what `copy`, a clone of this map left by
    /// [`Self::subtract`], wrote: added and changed keys become what the copy
    /// made them, removed ones are removed. False when a copy taken in since
    /// `copy` was made wrote one of the same keys to something else: two
    /// copies that wrote the same value agree, as declaring them in turn does.
    pub fn absorb(&mut self, copy: Self) -> bool
    where
        V: PartialEq,
    {
        self.absorb_with(copy, |mine, theirs| mine == theirs)
    }

    /// [`Self::absorb`] for values that cannot be compared: any key a copy
    /// taken in since wrote too is said.
    pub fn absorb_any(&mut self, copy: Self) -> bool {
        self.absorb_with(copy, |_, _| false)
    }

    fn absorb_with(&mut self, copy: Self, same: impl Fn(Option<&V>, Option<&V>) -> bool) -> bool {
        let ForkedMap {
            mut map,
            written,
            taken,
        } = copy;
        let made = taken.clock;
        self.taken.clock += 1;
        let mut alone = true;
        for (key, _) in written {
            let value = map.remove(&key);
            if !self.taken.take(&key, made) && !same(self.map.get(&key), value.as_ref()) {
                alone = false;
            }
            match value {
                Some(value) => {
                    self.map.insert(key, value);
                }
                None => {
                    self.map.remove(&key);
                }
            }
        }
        alone
    }
}

impl<K: Eq + Hash + Clone, V, S: BuildHasher> Extend<(K, V)> for ForkedMap<K, V, S> {
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

/// A set whose copies hand back what they wrote (the module comment).
#[derive(Debug)]
pub struct ForkedSet<K, S = RandomState> {
    map: ForkedMap<K, (), S>,
    set: HashSet<K, S>,
}

impl<K, S: Default> Default for ForkedSet<K, S> {
    fn default() -> Self {
        Self {
            map: ForkedMap::default(),
            set: HashSet::default(),
        }
    }
}

impl<K: Clone, S: Clone> Clone for ForkedSet<K, S> {
    fn clone(&self) -> Self {
        Self {
            map: self.map.clone(),
            set: self.set.clone(),
        }
    }
}

impl<K, S> std::ops::Deref for ForkedSet<K, S> {
    type Target = HashSet<K, S>;
    fn deref(&self) -> &HashSet<K, S> {
        &self.set
    }
}

impl<K: Eq + Hash, S: BuildHasher + Default> From<HashSet<K, S>> for ForkedSet<K, S> {
    fn from(set: HashSet<K, S>) -> Self {
        Self {
            map: ForkedMap::default(),
            set,
        }
    }
}

impl<'a, K, S> IntoIterator for &'a ForkedSet<K, S> {
    type Item = &'a K;
    type IntoIter = std::collections::hash_set::Iter<'a, K>;
    fn into_iter(self) -> Self::IntoIter {
        self.set.iter()
    }
}

impl<K: Eq + Hash + Clone, S: BuildHasher + Default> FromIterator<K> for ForkedSet<K, S> {
    fn from_iter<I: IntoIterator<Item = K>>(iter: I) -> Self {
        let mut set = Self::default();
        set.set = HashSet::from_iter(iter);
        set
    }
}

impl<K: Eq + Hash + Clone, S: BuildHasher + Default> ForkedSet<K, S> {
    pub fn insert(&mut self, key: K) -> bool {
        self.map.wrote(key.clone());
        self.set.insert(key)
    }

    pub fn remove<Q>(&mut self, key: &Q) -> bool
    where
        K: std::borrow::Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        match self.set.take(key) {
            Some(key) => {
                self.map.wrote(key);
                true
            }
            None => false,
        }
    }

    pub fn retain(&mut self, mut keep: impl FnMut(&K) -> bool) {
        let (written, now) = (&mut self.map.written, generation());
        self.set.retain(|k| {
            let kept = keep(k);
            if !kept {
                written.insert(k.clone(), now);
            }
            kept
        });
    }

    pub fn clear(&mut self) {
        let now = generation();
        self.map.written.extend(self.set.drain().map(|k| (k, now)));
    }

    /// Makes every element the one `rename` makes of it. An element that
    /// stays as it is is not written.
    pub fn rename(&mut self, mut rename: impl FnMut(&K) -> K) {
        let renamed: Vec<(K, K)> = self
            .set
            .iter()
            .filter_map(|k| {
                let to = rename(k);
                (to != *k).then(|| (k.clone(), to))
            })
            .collect();
        for (from, to) in renamed {
            self.remove(&from);
            self.insert(to);
        }
    }

    /// [`ForkedMap::subtract`].
    pub fn subtract(&mut self, since: u64) {
        self.map.written.retain(|_, g| *g > since);
        let written = &self.map.written;
        self.set.retain(|k| written.contains_key(k));
        self.map.taken.at = Arc::default();
    }

    /// [`ForkedMap::absorb`].
    pub fn absorb(&mut self, copy: Self) -> bool {
        let ForkedSet { map, set } = copy;
        let made = map.taken.clock;
        self.map.taken.clock += 1;
        let mut alone = true;
        for (key, _) in map.written {
            let theirs = set.contains(&key);
            if !self.map.taken.take(&key, made) && self.set.contains(&key) != theirs {
                alone = false;
            }
            if theirs {
                self.set.insert(key);
            } else {
                self.set.remove(&key);
            }
        }
        alone
    }
}

impl<K: Eq + Hash + Clone, S: BuildHasher + Default> Extend<K> for ForkedSet<K, S> {
    fn extend<I: IntoIterator<Item = K>>(&mut self, iter: I) {
        for k in iter {
            self.insert(k);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_copy_hands_back_a_change_to_a_key_it_was_made_with() {
        let mut map: ForkedMap<&str, u32> = ForkedMap::default();
        map.insert("Text", 1);
        let since = next_generation();
        let mut copy = map.clone();
        copy.insert("Text", 2);
        copy.insert("Bytes", 3);
        copy.subtract(since);
        assert!(map.absorb(copy));
        assert_eq!(map.get("Text"), Some(&2));
        assert_eq!(map.get("Bytes"), Some(&3));
    }

    #[test]
    fn a_copy_hands_back_what_it_removed() {
        let mut set: ForkedSet<&str> = ForkedSet::default();
        set.insert("a");
        let since = next_generation();
        let mut copy = set.clone();
        copy.remove("a");
        copy.subtract(since);
        assert!(set.absorb(copy));
        assert!(!set.contains("a"));
    }

    #[test]
    fn copies_that_wrote_the_same_value_agree() {
        let mut map: ForkedMap<&str, u32> = ForkedMap::default();
        let since = next_generation();
        let (mut a, mut b) = (map.clone(), map.clone());
        a.insert("x", 1);
        b.insert("x", 1);
        a.subtract(since);
        b.subtract(since);
        assert!(map.absorb(a));
        assert!(map.absorb(b));
    }

    #[test]
    fn a_key_two_copies_wrote_is_said() {
        let mut map: ForkedMap<&str, u32> = ForkedMap::default();
        let since = next_generation();
        let (mut a, mut b) = (map.clone(), map.clone());
        a.insert("x", 1);
        b.insert("x", 2);
        a.subtract(since);
        b.subtract(since);
        assert!(map.absorb(a));
        assert!(!map.absorb(b));
    }

    #[test]
    fn a_copy_made_after_another_was_taken_in_may_write_its_keys() {
        let mut map: ForkedMap<&str, u32> = ForkedMap::default();
        let since = next_generation();
        let mut a = map.clone();
        a.insert("x", 1);
        a.subtract(since);
        assert!(map.absorb(a));
        let since_b = next_generation();
        let mut b = map.clone();
        b.insert("x", 2);
        b.subtract(since_b);
        assert!(map.absorb(b));
        assert_eq!(map.get("x"), Some(&2));
    }

    #[test]
    fn a_copy_hands_back_only_what_it_wrote_since_it_was_made() {
        let mut map: ForkedMap<&str, u32> = ForkedMap::default();
        map.insert("prelude", 0);
        let since = next_generation();
        let mut copy = map.clone();
        copy.insert("x", 1);
        copy.subtract(since);
        assert_eq!(copy.len(), 1);
        assert!(map.absorb(copy));
    }

    #[test]
    fn copies_that_write_different_keys_are_taken_in_alone() {
        let mut map: ForkedMap<&str, u32> = ForkedMap::default();
        let since = next_generation();
        let (mut a, mut b) = (map.clone(), map.clone());
        a.insert("x", 1);
        b.insert("y", 2);
        a.subtract(since);
        b.subtract(since);
        assert!(map.absorb(a));
        assert!(map.absorb(b));
    }
}
