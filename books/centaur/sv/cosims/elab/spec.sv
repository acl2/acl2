


parameter foo = 5;

typedef logic [foo-1 : 0] bar_t;

// package p;

   parameter bar_t br = $clog2(foo);

  typedef bar_t [br : 0] buz_t;

   parameter buz_t bz = $bits(buz_t) + $bits(br);

// endpackage





module spec (input logic [127:0] in,
	     output wire [127:0] out);

   typedef buz_t [bz-1:0] goz_t;

   localparam goz_t gz = $bits(goz_t);

   assign out = gz;

endmodule // spec

