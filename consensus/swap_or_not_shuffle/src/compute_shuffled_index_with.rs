//! `compute_shuffled_index` for a 32-byte seed, with the hash function as a type parameter.
//!
//! Aeneas translates this module for the proofs in `consensus/state_processing/proofs`. So it
//! uses `while` loops and fixed-size buffers.

use crate::ShuffleHash;

/// Returns the 8 little-endian bytes of `digest[0..8]` as a `u64`.
fn first_u64(digest: &[u8; 32]) -> u64 {
    (digest[0] as u64)
        | (digest[1] as u64) << 8
        | (digest[2] as u64) << 16
        | (digest[3] as u64) << 24
        | (digest[4] as u64) << 32
        | (digest[5] as u64) << 40
        | (digest[6] as u64) << 48
        | (digest[7] as u64) << 56
}

/// Returns `seed + [round]`.
fn pivot_preimage(seed: &[u8; 32], round: u8) -> [u8; 33] {
    let mut buf = [0u8; 33];
    let mut k = 0;
    while k < 32 {
        buf[k] = seed[k];
        k += 1;
    }
    buf[32] = round;
    buf
}

/// Returns `seed + [round] + uint_to_bytes(Uint32(bucket))`.
fn source_preimage(seed: &[u8; 32], round: u8, bucket: usize) -> [u8; 37] {
    let mut buf = [0u8; 37];
    let mut k = 0;
    while k < 32 {
        buf[k] = seed[k];
        k += 1;
    }
    buf[32] = round;
    buf[33] = bucket as u8;
    buf[34] = (bucket >> 8) as u8;
    buf[35] = (bucket >> 16) as u8;
    buf[36] = (bucket >> 24) as u8;
    buf
}

/// One round of the shuffle on `index`.
fn shuffle_round<H: ShuffleHash>(
    seed: &[u8; 32],
    index: usize,
    round: u8,
    list_size: usize,
) -> usize {
    let pivot = (first_u64(&H::hash(&pivot_preimage(seed, round))) % list_size as u64) as usize;
    let flip = (pivot + (list_size - index)) % list_size;
    let position = if index < flip { flip } else { index };
    let source = H::hash(&source_preimage(seed, round, position >> 8));
    let byte = source[(position % 256) / 8];
    if (byte >> (position % 8)) % 2 == 1 {
        flip
    } else {
        index
    }
}

/// Returns `compute_shuffled_index(index, list_size, seed)` with `H` as the hash function.
///
/// Returns `None` under the same conditions as `compute_shuffled_index`.
pub fn compute_shuffled_index_with<H: ShuffleHash>(
    index: usize,
    list_size: usize,
    seed: &[u8; 32],
    shuffle_round_count: u8,
) -> Option<usize> {
    if list_size == 0 || index >= list_size || list_size > usize::MAX / 2 || list_size > 1 << 24 {
        return None;
    }

    let mut index = index;
    let mut round = 0u8;
    while round < shuffle_round_count {
        index = shuffle_round::<H>(seed, index, round, list_size);
        round += 1;
    }
    Some(index)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Sha256Hash, compute_shuffled_index};

    #[test]
    fn matches_compute_shuffled_index() {
        for list_size in [1, 2, 3, 7, 255, 256, 257, 1000] {
            for seed_byte in [0u8, 1, 42, 255] {
                let seed = [seed_byte; 32];
                for rounds in [0u8, 1, 10, 90] {
                    for index in 0..list_size {
                        assert_eq!(
                            compute_shuffled_index_with::<Sha256Hash>(
                                index, list_size, &seed, rounds
                            ),
                            compute_shuffled_index(index, list_size, &seed, rounds)
                        );
                    }
                }
            }
        }
    }
}
