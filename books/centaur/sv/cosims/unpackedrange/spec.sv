


typedef struct packed {
  logic [3:0] a;
  logic [3:0] b;
  logic [3:0] op;
} alu_in;

module sub (input alu_in ain [1:0],
	    output logic [3:0] res [1:0]);

   assign res[0] = ain[0].op[1] ?
		   ain[0].op[0] ? ain[0].a + ain[0].b : ain[0].a - ain[0].b :
		   ain[0].op[0] ? ain[0].a & ain[0].b : ain[0].a | ain[0].b;

   assign res[1] = ain[1].op[1] ?
		   ain[1].op[0] ? ain[1].a + ain[1].b : ain[1].a - ain[1].b :
		   ain[1].op[0] ? ain[1].a & ain[1].b : ain[1].a | ain[1].b;

endmodule // sub

module spec (input logic [127:0] in,
	     output wire [127:0] out);

   alu_in ain [3:0];
   assign { ain[0].a, ain[0].b, ain[0].op,
	    ain[1].a, ain[1].b, ain[1].op
	    } = in;

  logic [3:0] o [1:0];
   assign out = {o[1], o[0]};

   sub subinst (.ain(ain[1:0]), .res(o));

endmodule // spec
