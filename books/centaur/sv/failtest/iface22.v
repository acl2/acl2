interface alu_iface ();
  logic [3:0] a;
  logic [3:0] b;
  logic [3:0] op;
  logic [3:0] out1;
  logic [3:0] out2;
endinterface

module alu1 (alu_iface aif);

   assign aif.out1 = aif.op[1] ?
		     aif.op[0] ? aif.a + aif.b : aif.a - aif.b :
		     aif.op[0] ? aif.a & aif.b : aif.a | aif.b;

endmodule

module alu2 (alu_iface aif);

  assign aif.out2 = ~aif.out1;

endmodule


alu_iface aif ();  // Oops, not allowed to do this.

module spec (input logic [127:0] in,
	     output wire [127:0] out);

  alu1 aluinst1 (aif);
  alu2 aluinst2 (aif);

  assign {aif.a, aif.b, aif.op} = in;

  assign out = { aif.a, aif.b, aif.op, aif.out1, aif.out2 };

endmodule // spec
