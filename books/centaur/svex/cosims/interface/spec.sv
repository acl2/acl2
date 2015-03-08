


interface alu_iface ();
  logic [3:0] a;
  logic [3:0] b;
  logic [3:0] op;
  logic [3:0] out;
endinterface

module alu (alu_iface aif);

   assign aif.out = aif.op[1] ?
		    aif.op[0] ? aif.a + aif.b : aif.a - aif.b :
		    aif.op[0] ? aif.a & aif.b : aif.a | aif.b;

endmodule // sub

module spec (input logic [127:0] in,
	     output wire [127:0] out);

   alu_iface aif ();
   assign {aif.a, aif.b, aif.op} = in;
   
   alu aluinst (aif);

   assign out = aif.out;

endmodule // spec
