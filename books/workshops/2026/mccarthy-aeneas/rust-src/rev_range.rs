//! Reversed-range iteration (`for i in (a..b).rev()`) -- the upstream
//! memshift32 shape.  Regression crate for Rev<Range<usize>> extraction.
pub fn sum_rev(a: [u32; 8]) -> u32 {
    let mut acc: u32 = 0;
    for i in (0..8usize).rev() {
        acc = acc.wrapping_add(a[i]);
    }
    acc
}
/// upstream memshift32's exact shape: copy [s,s+8) to [s+8,s+16), descending.
pub fn shift_up(buf: &mut [u32; 24], start: usize) {
    for i in (start..start + 8).rev() {
        buf[i + 8] = buf[i];
    }
}
