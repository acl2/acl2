//@ [!lean] skip
//! Vec iteration: sum a Vec<u32> with wrapping add, via an indexed loop.
//! Exercises shared Vec indexing inside a loop -- first-order, provable
//! equal to a fold. Also a mutable-index case to probe the frontier.
use std::vec::Vec;

pub fn sum(v: &Vec<u32>) -> u32 {
    let mut s: u32 = 0;
    let mut i: usize = 0;
    while i < v.len() {
        s = s.wrapping_add(v[i]);
        i += 1;
    }
    s
}

// Mutable Vec index (backward function) -- expected to be rejected in v0.
pub fn double_first(v: &mut Vec<u32>) {
    if v.len() > 0 {
        v[0] = v[0].wrapping_add(v[0]);
    }
}
