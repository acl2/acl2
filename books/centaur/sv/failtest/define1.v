// oops, equal sign with a right paren right afterwards
`define foo (x =) x

module top ;

   wire w1;
   wire w2 = `foo(w1);

endmodule
