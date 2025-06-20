// The 'fill-function-output-type' main function.
function main(n: u8) -> u8 {
    let circ = C { m: n };
    circ.incm();
    show_C_m(circ);
    circ.m += 1;
    show_C_m(circ);
    return circ.m;
}

// There are two functions with unspecified output types:
// (1) the circuit function incm and
// (2) the regular function show_C_m
// Note, I did not see a functional use for unspecified output type
// in a non-circuit function.  For example, if you have this:
// function call_C_incm_twice(c: C) {
//   c.incm();
//   c.incm();
// }
// Then the circuit is passed by value.
// (That is the current semantics.)
//
// So for now the regular function unspecified output type is just for logging.

circuit C {
  m: u8,
  function incm(mut self) {
    self.m += 1;
  }
}

function show_C_m(c: C) {
  console.log("circuit's m = {}", c.m);
}
