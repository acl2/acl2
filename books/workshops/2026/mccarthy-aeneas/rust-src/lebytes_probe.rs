// Probe: the upstream bitslice/inv_bitslice byte plumbing
// (de-vendoring roadmap item 6 -- from_le_bytes + try_into and
// to_le_bytes + copy_from_slice, both through subslices).

pub fn ld(x: [u8; 8]) -> u32 {
    u32::from_le_bytes(x[2..6].try_into().unwrap())
}

pub fn st(w: u32) -> [u8; 8] {
    let mut out = [0u8; 8];
    out[2..6].copy_from_slice(&w.to_le_bytes());
    out
}

pub fn st2(w: u32) -> [[u8; 8]; 2] {
    let mut out = [[0u8; 8]; 2];
    out[1][2..6].copy_from_slice(&w.to_le_bytes());
    out
}
