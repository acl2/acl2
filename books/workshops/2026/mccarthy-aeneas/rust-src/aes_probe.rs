//@ [!lean] skip
//! Probe of the AES constructs that matter for extraction, so we can tell
//! first-order vs higher-order concretely (not by guessing).
//! (1) const S-box table + lookup, (2) in-place fixed-array element write,
//! (3) rotate_left, (4) array xor round.

// (1) const lookup table indexed by a byte
const SBOX: [u8; 4] = [0x63, 0x7c, 0x77, 0x7b];
pub fn sub(x: u8) -> u8 {
    SBOX[(x & 3) as usize]
}

// (2) in-place write into a &mut fixed array (the AES pattern:
//     block[i] = something) -- does this become UpdateAtIndex (first-order)
//     or a backward function (HO)?
pub fn xor_into(block: &mut [u8; 4], k: [u8; 4]) {
    let mut i = 0usize;
    while i < 4 {
        block[i] ^= k[i];
        i += 1;
    }
}

// (3) rotate_left (used in the AES key schedule / MixColumns)
pub fn rotl(x: u32, n: u32) -> u32 {
    x.rotate_left(n)
}

// (4) functional (non-mutating) array round: returns a new array
pub fn add_round_key(s: [u8; 4], k: [u8; 4]) -> [u8; 4] {
    [s[0] ^ k[0], s[1] ^ k[1], s[2] ^ k[2], s[3] ^ k[3]]
}

// (5) GF(2^8) multiply-by-x (xtime) -- the MixColumns core. Pure u8
//     shift/xor/mul, NO cast: does the GF math extract first-order?
pub fn xtime(x: u8) -> u8 {
    let hi = x >> 7;
    (x << 1) ^ (hi * 0x1b)
}

// (6) general GF(2^8) multiply (Russian-peasant) -- loop + in-place locals.
pub fn gmul(a: u8, b: u8) -> u8 {
    let mut p = 0u8;
    let mut a = a;
    let mut b = b;
    let mut i = 0u32;
    while i < 8 {
        if b & 1 == 1 {
            p ^= a;
        }
        let hi = a >> 7;
        a <<= 1;
        if hi == 1 {
            a ^= 0x1b;
        }
        b >>= 1;
        i += 1;
    }
    p
}
