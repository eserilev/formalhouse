use super::pubkey_index::{self, IndexMap};
use bls::PublicKeyBytes;
use rpds::HashTrieMapSync as HashTrieMap;

type ValidatorIndex = usize;

#[allow(clippy::len_without_is_empty)]
#[derive(Debug, PartialEq, Clone, Default)]
pub struct PubkeyCache {
    /// Maintain the number of keys added to the map. It is not sufficient to just use the
    /// HashTrieMap len, as it does not increase when duplicate keys are added. Duplicate keys are
    /// used during testing.
    len: usize,
    map: HashTrieMap<PublicKeyBytes, ValidatorIndex>,
}

impl PubkeyCache {
    /// Returns the number of validator indices added to the map so far.
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> ValidatorIndex {
        self.len
    }

    /// Inserts a validator index into the map.
    ///
    /// The added index must equal the number of validators already added to the map. This ensures
    /// that an index is never skipped.
    pub fn insert(&mut self, pubkey: PublicKeyBytes, index: ValidatorIndex) -> bool {
        match pubkey_index::insert(&mut self.map, self.len, pubkey, index) {
            Some(len) => {
                self.len = len;
                true
            }
            None => false,
        }
    }

    /// Looks up a validator index's by their public key.
    pub fn get(&self, pubkey: &PublicKeyBytes) -> Option<ValidatorIndex> {
        self.map.get_index(pubkey)
    }
}

impl IndexMap<PublicKeyBytes> for HashTrieMap<PublicKeyBytes, ValidatorIndex> {
    fn get_index(&self, key: &PublicKeyBytes) -> Option<ValidatorIndex> {
        self.get(key).copied()
    }

    fn insert_index(&mut self, key: PublicKeyBytes, index: ValidatorIndex) {
        self.insert_mut(key, index);
    }
}

#[cfg(feature = "arbitrary")]
impl arbitrary::Arbitrary<'_> for PubkeyCache {
    fn arbitrary(_u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<Self> {
        Ok(Self::default())
    }
}
