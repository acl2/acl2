//@ [!lean] skip
//! Range for-loops (`for i in 0..n`) -- supported by the ACL2 backend via
//! synthesized Range::next / into_iter. Two fixslice shapes: array indexing in
//! a range loop, and an accumulating range loop. Both range over usize (a
//! single Range monomorphization; see the note in the ACL2 backend about the
//! ExtractBase name clash when several Range<T> instances coexist).

// in-place array update in a range for-loop (the AddRoundKey shape)
pub fn add_rk(state: &mut [u32; 8], rk: [u32; 8]) {
    for i in 0..8 {
        state[i] ^= rk[i];
    }
}

// accumulating range for-loop, provable against a fold spec. `i as u32`
// also exercises the integer-cast support.
pub fn sum_to(n: usize) -> u32 {
    let mut s = 0u32;
    for i in 0..n {
        s = s.wrapping_add(i as u32);
    }
    s
}
