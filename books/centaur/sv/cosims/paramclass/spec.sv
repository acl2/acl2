// SV - Symbolic Vector Hardware Analysis Framework
//
// INTEL TEMPORARY COPYRIGHT HEADER --
// Not for public distribution until this is replaced with a proper license!
//
// Original author: Sol Swords <sol.swords@intel.com>

virtual class myfns
  #( parameter WIDTH = 8 );

   static function logic [WIDTH-1:0] plusone (logic [WIDTH-1:0] in);
      plusone = in+1;
   endfunction : plusone

endclass // myfns




module spec (input logic [127:0] in,
	     output logic [127:0] out);

   assign out[7:0]    = myfns::plusone(in[7:0]);
   assign out[15:8]   = '0;   
   assign out[31:16]  = myfns#(16)::plusone(in[31:16]);
   assign out[63:32]  = '0;
   assign out[95:64]  = myfns#(.WIDTH(32))::plusone(in[95:64]);
   assign out[127:96] = '0;
   
endmodule
