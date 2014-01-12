/*


Copyright (C) 2013 David L. Rager

*/



// divide.v
//
// These are simple dividers.

module divide1 (
  output [0:0] out,
  input [0:0] abus,
  input [0:0] bbus
);
assign out = abus / bbus;
endmodule

module divide2 (
  output [1:0] out,
  input [1:0] abus,
  input [1:0] bbus
);
assign out = abus / bbus;
endmodule

module divide3 (
  output [2:0] out,
  input [2:0] abus,
  input [2:0] bbus
);
assign out = abus / bbus;
endmodule

module divide4 (
  output [3:0] out,
  input [3:0] abus,
  input [3:0] bbus
);
assign out = abus / bbus;
endmodule

module divide8 (
  output [7:0] out,
  input [7:0] abus,
  input [7:0] bbus
);
assign out = abus / bbus;
endmodule

module divide10 (
  output [9:0] out,
  input [9:0] abus,
  input [9:0] bbus
);
assign out = abus / bbus;
endmodule

module divide12 (
  output [11:0] out,
  input [11:0] abus,
  input [11:0] bbus
);
assign out = abus / bbus;
endmodule

module divide16 (
  output [15:0] out,
  input [15:0] abus,
  input [15:0] bbus
);
assign out = abus / bbus;
endmodule

module divide32 (
  output [31:0] out,
  input [31:0] abus,
  input [31:0] bbus
);
assign out = abus / bbus;
endmodule

module divide64 (
  output [63:0] out,
  input [63:0] abus,
  input [63:0] bbus
);
assign out = abus / bbus;
endmodule

/*
 module divide128 (
  output [127:0] out,
  input [127:0] abus,
  input [127:0] bbus
);
assign out = abus / bbus;
endmodule

module divide256 (
  output [255:0] out,
  input [255:0] abus,
  input [255:0] bbus
);
assign out = abus / bbus;
endmodule

module divide512 (
  output [511:0] out,
  input [511:0] abus,
  input [511:0] bbus
);
assign out = abus / bbus;
endmodule

module divide1024 (
  output [1023:0] out,
  input [1023:0] abus,
  input [1023:0] bbus
);
assign out = abus / bbus;
endmodule

*/
