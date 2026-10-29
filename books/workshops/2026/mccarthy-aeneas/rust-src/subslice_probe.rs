// Probe: mutable and shared subslice borrows through function calls
// (de-vendoring roadmap item 7 -- &mut rkeys[a..b] passed to &mut [u32] ops).

fn bump(s: &mut [u32]) {
    s[0] = s[0].wrapping_add(1);
    s[3] = s[3].wrapping_add(2);
}

pub fn go(a: [u32; 8]) -> [u32; 8] {
    let mut a = a;
    bump(&mut a[2..6]);
    a
}

fn peek(s: &[u32]) -> u32 {
    s[1]
}

pub fn rd(a: [u32; 8]) -> u32 {
    peek(&a[2..6])
}

pub fn len_of(a: [u32; 8]) -> usize {
    let s = &a[2..6];
    s.len()
}

fn set0(s: &mut [u32]) {
    s[0] = 7;
}

pub fn coerce(a: [u32; 8]) -> [u32; 8] {
    let mut a = a;
    set0(&mut a);
    a
}

pub fn stepby(a: [u32; 8]) -> u32 {
    let mut acc = 0u32;
    for i in (0..8).step_by(4) {
        acc = acc.wrapping_add(a[i]);
    }
    acc
}
