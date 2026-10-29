//@ [!lean] skip
//! Minimal Vec exercise for the ACL2 backend: build, push, index, len.
use std::vec::Vec;

pub fn build_pair(a: u32, b: u32) -> Vec<u32> {
    let mut v: Vec<u32> = Vec::new();
    v.push(a);
    v.push(b);
    v
}

pub fn get0(v: &Vec<u32>) -> u32 {
    v[0]
}

pub fn len_of(v: &Vec<u32>) -> usize {
    v.len()
}
