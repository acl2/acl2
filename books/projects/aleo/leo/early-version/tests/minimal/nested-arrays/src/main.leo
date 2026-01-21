// The 'nested-arrays' main function.
function main(a: u8) -> u8 {
    // a can be 0 or 1.  It is an error if a is 2.
    let c: u8 = array_3x2_nested()[2][a];
    return c;
}

function array_3x2_nested() -> [u8; (3, 2)] {
    return [1u8; (3, 2)];
}
