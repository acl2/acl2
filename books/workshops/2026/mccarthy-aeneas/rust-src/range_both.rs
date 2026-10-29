//! Repro for the extraction naming bug: instantiating BOTH Range<usize> and
//! Range<i32> in one crate collides in the name registration (the type
//! argument was not part of the registered key).
pub fn sum_usize(a: [u32; 4]) -> u32 {
    let mut acc: u32 = 0;
    for i in 0..4usize {
        acc = acc.wrapping_add(a[i]);
    }
    acc
}
pub fn count_i32() -> i32 {
    let mut acc: i32 = 0;
    for j in 1..5 {
        acc += j;
    }
    acc
}
