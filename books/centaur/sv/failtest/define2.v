// This test shows that default values are processed literally
// and cannot depend on other arguments.

`define foo(a, b=a) b

module top ;

   wire w1;
   wire w2 = `foo(w1);  // oops, other tools die here, saying that A is not defined.

endmodule
