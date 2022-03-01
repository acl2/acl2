// SV - Symbolic Vector Hardware Analysis Framework
//
// INTEL TEMPORARY COPYRIGHT HEADER --
// Not for public distribution until this is replaced with a proper license!
//
// Original author: Sol Swords <sol.swords@intel.com>

module spec (input logic [127:0] in,
	     output logic [127:0] out);

   logic [31:0] 		  foo;
   logic [31:0] 		  bar;


   assign foo[7:0] = in[7:0];

   assign foo[31:16] = in[31:16];

   always_comb bar[7:0] = in[7:0];
   always_comb bar[31:16] = in[31:16];

   assign out[31:0] = foo;

   assign out[95:64] = bar;

endmodule // spec
