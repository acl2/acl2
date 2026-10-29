//@ [!lean] skip
//! Array-signature TEA: same cipher as tea.rs, but with the block and key
//! passed as fixed-size arrays [u32; 2] / [u32; 4] and the block returned
//! as [u32; 2] -- matching the Kestrel spec's array API. Exercises the
//! ACL2 backend's array/slice support.

const DELTA: u32 = 0x9E3779B9;

pub fn encrypt(v: [u32; 2], k: [u32; 4]) -> [u32; 2] {
    let mut y = v[0];
    let mut z = v[1];
    let mut sum: u32 = 0;
    let mut i: u32 = 0;
    while i < 32 {
        sum = sum.wrapping_add(DELTA);
        y = y.wrapping_add(
            ((z << 4).wrapping_add(k[0])) ^ (z.wrapping_add(sum)) ^ ((z >> 5).wrapping_add(k[1])),
        );
        z = z.wrapping_add(
            ((y << 4).wrapping_add(k[2])) ^ (y.wrapping_add(sum)) ^ ((y >> 5).wrapping_add(k[3])),
        );
        i += 1;
    }
    [y, z]
}

pub fn decrypt(v: [u32; 2], k: [u32; 4]) -> [u32; 2] {
    let mut y = v[0];
    let mut z = v[1];
    let mut sum: u32 = DELTA.wrapping_mul(32);
    let mut i: u32 = 0;
    while i < 32 {
        z = z.wrapping_sub(
            ((y << 4).wrapping_add(k[2])) ^ (y.wrapping_add(sum)) ^ ((y >> 5).wrapping_add(k[3])),
        );
        y = y.wrapping_sub(
            ((z << 4).wrapping_add(k[0])) ^ (z.wrapping_add(sum)) ^ ((z >> 5).wrapping_add(k[1])),
        );
        sum = sum.wrapping_sub(DELTA);
        i += 1;
    }
    [y, z]
}
