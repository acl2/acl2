/*


Copyright (C) 2013 David L. Rager

*/



// add.v
//
// This is a simple 1, 2, 3, and 4 bit adder.

module add1 (
  output [0:0] out,
  input [0:0] abus,
  input [0:0] bbus
);
assign out = abus + bbus;
endmodule

module add2 (
  output [1:0] out,
  input [1:0] abus,
  input [1:0] bbus
);
assign out = abus + bbus;
endmodule

module add3 (
  output [2:0] out,
  input [2:0] abus,
  input [2:0] bbus
);
assign out = abus + bbus;
endmodule

module add4 (
  output [3:0] out,
  input [3:0] abus,
  input [3:0] bbus
);
assign out = abus + bbus;
endmodule

module add8 (
  output [7:0] out,
  input [7:0] abus,
  input [7:0] bbus
);
assign out = abus + bbus;
endmodule

module add16 (
  output [15:0] out,
  input [15:0] abus,
  input [15:0] bbus
);
assign out = abus + bbus;
endmodule

module add32 (
  output [31:0] out,
  input [31:0] abus,
  input [31:0] bbus
);
assign out = abus + bbus;
endmodule

module add64 (
  output [63:0] out,
  input [63:0] abus,
  input [63:0] bbus
);
assign out = abus + bbus;
endmodule

module add128 (
  output [127:0] out,
  input [127:0] abus,
  input [127:0] bbus
);
assign out = abus + bbus;
endmodule

module add256 (
  output [255:0] out,
  input [255:0] abus,
  input [255:0] bbus
);
assign out = abus + bbus;
endmodule

module add512 (
  output [511:0] out,
  input [511:0] abus,
  input [511:0] bbus
);
assign out = abus + bbus;
endmodule

module add1024 (
  output [1023:0] out,
  input [1023:0] abus,
  input [1023:0] bbus
);
assign out = abus + bbus;
endmodule

