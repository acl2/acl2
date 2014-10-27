package p1 ;

  wire foo = 1;

endpackage


package p2 ;

  wire foo = 0;

endpackage

import p1::*;
import p2::*;

module top ;

  wire bar = foo;  // we shouldn't tolerate this

endmodule
