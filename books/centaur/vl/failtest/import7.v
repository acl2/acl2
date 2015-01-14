package p1 ;

  wire foo = 1;

endpackage


package p2 ;

  wire foo = 0;

endpackage


module top (output topout, input topin);

  import p1::*;
  import p2::*;

  wire bar = foo;  // we shouldn't tolerate this

endmodule
