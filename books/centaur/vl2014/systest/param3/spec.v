// VL 2014 -- Verilog Toolkit, 2014 Edition
// Copyright (C) 2008-2015 Centaur Technology
//
// Contact:
//   Centaur Technology Formal Verification Group
//   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
//   http://www.centtech.com/
//
// License: (An MIT/X11-style license)
//
//   Permission is hereby granted, free of charge, to any person obtaining a
//   copy of this software and associated documentation files (the "Software"),
//   to deal in the Software without restriction, including without limitation
//   the rights to use, copy, modify, merge, publish, distribute, sublicense,
//   and/or sell copies of the Software, and to permit persons to whom the
//   Software is furnished to do so, subject to the following conditions:
//
//   The above copyright notice and this permission notice shall be included in
//   all copies or substantial portions of the Software.
//
//   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
//   THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.
//
// Original author: Jared Davis <jared@centtech.com>

// basic tests of parameter handling

`ifdef SYSTEM_VERILOG_MODE

typedef struct { integer a; integer b; } mytype_t;

module MA (out, in);     // Extremely basic parameterized module
  parameter type foo_t = integer;
  parameter size = 4;
  output [size-1:0] out;
  input [size-1:0]  in;
  assign out = ~in;
endmodule

module MB (out, in);     // Increment unsigned by plain parameter
  parameter inc = 1;
  output [3:0] out;
  input  [3:0] in;
  assign out = in + inc;
endmodule

module MC (out, in);     // Increment signed by plain parameter
  parameter inc = 1;
  output [3:0] out;
  input  [3:0] in;
  wire signed [3:0] sin = in;
  assign out = sin + inc;
endmodule

module MD (out, in);     // Increment unsigned by signed parameter
  parameter signed inc = 1;
  output [3:0] out;
  input  [3:0] in;
  assign out = in + inc;
endmodule

module ME (out, in);     // Increment signed by signed parameter
  parameter signed inc = 1;
  output [3:0] out;
  input  [3:0] in;
  wire signed [3:0] sin = in;
  assign out = sin + inc;
endmodule

module MF (out, in);     // Increment unsigned by ranged parameter
  parameter [3:0] inc = 1;
  output [3:0] out;
  input  [3:0] in;
  assign out = in + inc;
endmodule

module MG (out, in);     // Increment signed by ranged parameter
  parameter [3:0] inc = 1;
  output [3:0] out;
  input  [3:0] in;
  wire signed [3:0] sin = in;
  assign out = sin + inc;
endmodule

module MH (out, in);     // Increment unsigned by signed, ranged parameter
  parameter signed [3:0] inc = 1;
  output [3:0] out;
  input  [3:0] in;
  assign out = in + inc;
endmodule

module MI (out, in);     // Increment signed by signed, ranged parameter
  parameter signed [3:0] inc = 1;
  output [3:0] out;
  input  [3:0] in;
  wire signed [3:0] sin = in;
  assign out = sin + inc;
endmodule


module dut (

in1, in2,

aout1, aout2, aout3,
bout1, bout2, bout3, bout4, bout5, bout6, bout7,
cout1, cout2, cout3, cout4, cout5, cout6, cout7,
dout1, dout2, dout3, dout4, dout5, dout6, dout7,
eout1, eout2, eout3, eout4, eout5, eout6, eout7,
fout1, fout2, fout3, fout4, fout5, fout6, fout7,
gout1, gout2, gout3, gout4, gout5, gout6, gout7,
hout1, hout2, hout3, hout4, hout5, hout6, hout7,
iout1, iout2, iout3, iout4, iout5, iout6, iout7


);

  parameter size = 1;
  wire [size-1:0] make_size_matter;

  input [3:0] 	   in1, in2;


  output [3:0] 	   aout1, aout2, aout3;
  MA ainst1 (aout1, in1);
  assign aout2[3] = in2[3];
  MA #(.size(3)) ainst2 (aout2[2:0], in1[2:0]);
  assign aout3[3:2] = in2[3:2];
  MA #(.foo_t(integer), .size(2)) ainst3 (aout3[1:0], in1[1:0]);

  output [3:0] 	   bout1, bout2, bout3, bout4, bout5, bout6, bout7;
  MB binst1 (bout1, in1);
  MB #(.inc(2)) binst2 (bout2, in1);
  MB #(.inc(-1)) binst3 (bout3, in1);
  MB #(.inc(4'd3)) binst4 (bout4, in1);
  MB #(.inc(-4'd1)) binst5 (bout5, in1);
  MB #(.inc(4'sd3)) binst6 (bout6, in1);
  MB #(.inc(-4'sd1)) binst7 (bout7, in1);

  output [3:0] 	   cout1, cout2, cout3, cout4, cout5, cout6, cout7;
  MC cinst1 (cout1, in1);
  MC #(.inc(2)) cinst2 (cout2, in1);
  MC #(.inc(-1)) cinst3 (cout3, in1);
  MC #(.inc(4'd3)) cinst4 (cout4, in1);
  MC #(.inc(-4'd1)) cinst5 (cout5, in1);
  MC #(.inc(4'sd3)) cinst6 (cout6, in1);
  MC #(.inc(-4'sd1)) cinst7 (cout7, in1);

  output [3:0] 	   dout1, dout2, dout3, dout4, dout5, dout6, dout7;
  MD dinst1 (dout1, in1);
  MD #(.inc(2)) dinst2 (dout2, in1);
  MD #(.inc(-1)) dinst3 (dout3, in1);
  MD #(.inc(4'd3)) dinst4 (dout4, in1);
  MD #(.inc(-4'd1)) dinst5 (dout5, in1);
  MD #(.inc(4'sd3)) dinst6 (dout6, in1);
  MD #(.inc(-4'sd1)) dinst7 (dout7, in1);

  output [3:0] 	   eout1, eout2, eout3, eout4, eout5, eout6, eout7;
  ME einst1 (eout1, in1);
  ME #(.inc(2)) einst2 (eout2, in1);
  ME #(.inc(-1)) einst3 (eout3, in1);
  ME #(.inc(4'd3)) einst4 (eout4, in1);
  ME #(.inc(-4'd1)) einst5 (eout5, in1);
  ME #(.inc(4'sd3)) einst6 (eout6, in1);
  ME #(.inc(-4'sd1)) einst7 (eout7, in1);

  output [3:0] 	   fout1, fout2, fout3, fout4, fout5, fout6, fout7;
  MF finst1 (fout1, in1);
  MF #(.inc(2)) finst2 (fout2, in1);
  MF #(.inc(-1)) finst3 (fout3, in1);
  MF #(.inc(4'd3)) finst4 (fout4, in1);
  MF #(.inc(-4'd1)) finst5 (fout5, in1);
  MF #(.inc(4'sd3)) finst6 (fout6, in1);
  MF #(.inc(-4'sd1)) finst7 (fout7, in1);

  output [3:0] 	   gout1, gout2, gout3, gout4, gout5, gout6, gout7;
  MG ginst1 (gout1, in1);
  MG #(.inc(2)) ginst2 (gout2, in1);
  MG #(.inc(-1)) ginst3 (gout3, in1);
  MG #(.inc(4'd3)) ginst4 (gout4, in1);
  MG #(.inc(-4'd1)) ginst5 (gout5, in1);
  MG #(.inc(4'sd3)) ginst6 (gout6, in1);
  MG #(.inc(-4'sd1)) ginst7 (gout7, in1);

  output [3:0] 	   hout1, hout2, hout3, hout4, hout5, hout6, hout7;
  MH hinst1 (hout1, in1);
  MH #(.inc(2)) hinst2 (hout2, in1);
  MH #(.inc(-1)) hinst3 (hout3, in1);
  MH #(.inc(4'd3)) hinst4 (hout4, in1);
  MH #(.inc(-4'd1)) hinst5 (hout5, in1);
  MH #(.inc(4'sd3)) hinst6 (hout6, in1);
  MH #(.inc(-4'sd1)) hinst7 (hout7, in1);

  output [3:0] 	   iout1, iout2, iout3, iout4, iout5, iout6, iout7;
  MI iinst1 (iout1, in1);
  MI #(.inc(2)) iinst2 (iout2, in1);
  MI #(.inc(-1)) iinst3 (iout3, in1);
  MI #(.inc(4'd3)) iinst4 (iout4, in1);
  MI #(.inc(-4'd1)) iinst5 (iout5, in1);
  MI #(.inc(4'sd3)) iinst6 (iout6, in1);
  MI #(.inc(-4'sd1)) iinst7 (iout7, in1);

endmodule


/*+VL

module make_tests () ;

wire [3:0] in1, in2,
 aout1, aout2, aout3,
 bout1, bout2, bout3, bout4, bout5, bout6, bout7,
 cout1, cout2, cout3, cout4, cout5, cout6, cout7,
 dout1, dout2, dout3, dout4, dout5, dout6, dout7,
 eout1, eout2, eout3, eout4, eout5, eout6, eout7,
 fout1, fout2, fout3, fout4, fout5, fout6, fout7,
 gout1, gout2, gout3, gout4, gout5, gout6, gout7,
 hout1, hout2, hout3, hout4, hout5, hout6, hout7,
 iout1, iout2, iout3, iout4, iout5, iout6, iout7;

 dut #(1) dir_test_1 ( in1, in2,
 aout1, aout2, aout3,
 bout1, bout2, bout3, bout4, bout5, bout6, bout7,
 cout1, cout2, cout3, cout4, cout5, cout6, cout7,
 dout1, dout2, dout3, dout4, dout5, dout6, dout7,
 eout1, eout2, eout3, eout4, eout5, eout6, eout7,
 fout1, fout2, fout3, fout4, fout5, fout6, fout7,
 gout1, gout2, gout3, gout4, gout5, gout6, gout7,
 hout1, hout2, hout3, hout4, hout5, hout6, hout7,
 iout1, iout2, iout3, iout4, iout5, iout6, iout7
 );

endmodule

*/


`endif
