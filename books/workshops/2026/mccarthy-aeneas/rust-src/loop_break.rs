// Regression probe for the upstream-fixslice round-loop shape (de-vendoring
// roadmap item 3): a bare `loop { ... if k == N { break; } ... }` with a
// mutated integer counter, a break in the MIDDLE of the body, and factored
// &mut-state ops that also consume the counter (as aes128_encrypt's
// add_round_key consumes rk_off).  Known-answer proofs: loop_break-proofs.lisp.

fn step_a(s: &mut [u32; 4], k: usize) {
    let i = k % 4;
    let x = s[i];
    s[i] = x.wrapping_add(1);
}

fn step_b(s: &mut [u32; 4], k: usize) {
    let i = k % 4;
    let x = s[i];
    s[i] = x.wrapping_add(1);
}

pub fn run(mut s: [u32; 4]) -> [u32; 4] {
    let mut k = 1;
    loop {
        step_a(&mut s, k);
        k += 1;

        if k == 8 {
            break;
        }

        step_b(&mut s, k);
        k += 1;
    }
    s
}
