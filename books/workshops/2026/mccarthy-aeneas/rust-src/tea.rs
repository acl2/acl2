//@ [!lean] skip
//! TEA (Tiny Encryption Algorithm) — a crypto demo for the ACL2 backend.
//! Array-free and state-free: only wrapping add/sub, shifts, and xor on
//! u32, so it fits the ACL2 backend's v0 envelope. The target theorem is
//! decrypt(encrypt(v, k), k) == v.

const DELTA: u32 = 0x9E3779B9;

pub fn encrypt(v0: u32, v1: u32, k0: u32, k1: u32, k2: u32, k3: u32) -> (u32, u32) {
    let mut y = v0;
    let mut z = v1;
    let mut sum: u32 = 0;
    let mut i: u32 = 0;
    while i < 32 {
        sum = sum.wrapping_add(DELTA);
        y = y.wrapping_add(
            ((z << 4).wrapping_add(k0)) ^ (z.wrapping_add(sum)) ^ ((z >> 5).wrapping_add(k1)),
        );
        z = z.wrapping_add(
            ((y << 4).wrapping_add(k2)) ^ (y.wrapping_add(sum)) ^ ((y >> 5).wrapping_add(k3)),
        );
        i += 1;
    }
    (y, z)
}

pub fn decrypt(v0: u32, v1: u32, k0: u32, k1: u32, k2: u32, k3: u32) -> (u32, u32) {
    let mut y = v0;
    let mut z = v1;
    // sum starts at DELTA*32 mod 2^32
    let mut sum: u32 = DELTA.wrapping_mul(32);
    let mut i: u32 = 0;
    while i < 32 {
        z = z.wrapping_sub(
            ((y << 4).wrapping_add(k2)) ^ (y.wrapping_add(sum)) ^ ((y >> 5).wrapping_add(k3)),
        );
        y = y.wrapping_sub(
            ((z << 4).wrapping_add(k0)) ^ (z.wrapping_add(sum)) ^ ((z >> 5).wrapping_add(k1)),
        );
        sum = sum.wrapping_sub(DELTA);
        i += 1;
    }
    (y, z)
}
