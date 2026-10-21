use ethereum_hashing::hash_fixed;

/// A 32-byte hash function for the shuffle.
pub trait ShuffleHash {
    /// Returns the hash of `input`.
    fn hash(input: &[u8]) -> [u8; 32];
}

/// SHA-256, the hash function of the specification.
pub struct Sha256Hash;

impl ShuffleHash for Sha256Hash {
    fn hash(input: &[u8]) -> [u8; 32] {
        hash_fixed(input)
    }
}
