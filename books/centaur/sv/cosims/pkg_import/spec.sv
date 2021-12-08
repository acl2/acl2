// PLACEHOLDER for Intel copyright header

package mypkg;
   localparam WIDTH = 4;
   typedef logic [WIDTH-1:0] mytype;
   function automatic mytype myfun (logic [WIDTH-1:0] in);
      myfun = in+1;
   endfunction
endpackage // mypkg

module sub
  import mypkg::*;
   (input mytype in,
    input [WIDTH-1:-0] in2,
    output 	       mytype out);

   assign out = myfun(in) + myfun(in2);

endmodule // sub

module spec (input logic [127:0] in,
	     output wire [127:0] out);

   genvar 			 i;

   for (i=0; i*8<127; i++) begin: blk
      sub mysub (in[i*8+:4], in[i*8+4+:4], out[i*4+:4]);
   end
endmodule
   
