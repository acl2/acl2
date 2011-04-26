// BOZO this should not be here.

module VL_SIMPLE_LATCH(out, in, en) ;

   output out;
   input in;
   input en;

   reg out;

   always @(in or en)
     if (en) out = in;

endmodule
