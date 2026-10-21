//! Pure index logic of `PubkeyCache`.
//!
//! Aeneas translates this module for the proofs in `consensus/types/proofs`. The map is a
//! trait, so the proofs only assume the get and insert laws of a finite map.

/// The map from a key to a validator index.
pub trait IndexMap<K> {
    fn get_index(&self, key: &K) -> Option<usize>;
    fn insert_index(&mut self, key: K, index: usize);
}

/// Adds `key` at `index` if `index` is the next index. Returns the new length, or `None` when
/// the index is not the next one or the length overflows. Then the map does not change.
pub fn insert<K, M: IndexMap<K>>(map: &mut M, len: usize, key: K, index: usize) -> Option<usize> {
    if index != len {
        return None;
    }
    match len.checked_add(1) {
        Some(new_len) => {
            map.insert_index(key, index);
            Some(new_len)
        }
        None => None,
    }
}
