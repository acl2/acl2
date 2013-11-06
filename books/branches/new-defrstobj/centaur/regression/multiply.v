/*


Copyright (C) 2013 David L. Rager

*/



// multiply.v
//
// These are simple multipliers.

module multiply1 (
  output [0:0] out,
  input [0:0] abus,
  input [0:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply2 (
  output [1:0] out,
  input [1:0] abus,
  input [1:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply3 (
  output [2:0] out,
  input [2:0] abus,
  input [2:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply4 (
  output [3:0] out,
  input [3:0] abus,
  input [3:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply8 (
  output [7:0] out,
  input [7:0] abus,
  input [7:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply10 (
  output [9:0] out,
  input [9:0] abus,
  input [9:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply12 (
  output [11:0] out,
  input [11:0] abus,
  input [11:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply16 (
  output [15:0] out,
  input [15:0] abus,
  input [15:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply32 (
  output [31:0] out,
  input [31:0] abus,
  input [31:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply64 (
  output [63:0] out,
  input [63:0] abus,
  input [63:0] bbus
);
assign out = abus * bbus;
endmodule

/*
 module multiply128 (
  output [127:0] out,
  input [127:0] abus,
  input [127:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply256 (
  output [255:0] out,
  input [255:0] abus,
  input [255:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply512 (
  output [511:0] out,
  input [511:0] abus,
  input [511:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply1024 (
  output [1023:0] out,
  input [1023:0] abus,
  input [1023:0] bbus
);
assign out = abus * bbus;
endmodule

*/
