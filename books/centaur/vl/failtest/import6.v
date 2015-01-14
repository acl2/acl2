package p1 ;

  wire foo;

endpackage


package p2 ;

  import p1::foo;

endpackage


import p2::*;


module top (output topout, input topin);

  assign bar = foo;    // imports must not be inherited, so this should be an error

endmodule
