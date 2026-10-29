// Probe: what the pipeline emits for Rust `as` integer casts
// (de-vendoring roadmap item 5 -- truncating cast semantics).

pub fn c_u32_u8(x: u32) -> u8 {
    x as u8
}
pub fn c_u32_u16(x: u32) -> u16 {
    x as u16
}
pub fn c_u8_u32(x: u8) -> u32 {
    x as u32
}
pub fn c_u32_i8(x: u32) -> i8 {
    x as i8
}
pub fn c_i32_u8(x: i32) -> u8 {
    x as u8
}
