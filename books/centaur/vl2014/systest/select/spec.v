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


// basic tests of dynamic bitselects

module select_tests (
  in,
  sel,

  // Outputs:  out_f*_s* means "from f-bit wire, select s-bits"
  out_f1_s1, out_f1_s2, out_f1_s3, out_f1_s4, out_f1_s5, out_f1_s6,
  out_f2_s1, out_f2_s2, out_f2_s3, out_f2_s4, out_f2_s5, out_f2_s6,
  out_f3_s1, out_f3_s2, out_f3_s3, out_f3_s4, out_f3_s5, out_f3_s6,
  out_f4_s1, out_f4_s2, out_f4_s3, out_f4_s4, out_f4_s5, out_f4_s6,
  out_f5_s1, out_f5_s2, out_f5_s3, out_f5_s4, out_f5_s5, out_f5_s6,
  out_f6_s1, out_f6_s2, out_f6_s3, out_f6_s4, out_f6_s5, out_f6_s6,
  out_f7_s1, out_f7_s2, out_f7_s3, out_f7_s4, out_f7_s5, out_f7_s6
);

parameter foo = 1;
wire pretend_to_use_foo = foo;

input [6:0] in;
input [6:0] sel;

output out_f1_s1, out_f1_s2, out_f1_s3, out_f1_s4, out_f1_s5, out_f1_s6;
output out_f2_s1, out_f2_s2, out_f2_s3, out_f2_s4, out_f2_s5, out_f2_s6;
output out_f3_s1, out_f3_s2, out_f3_s3, out_f3_s4, out_f3_s5, out_f3_s6;
output out_f4_s1, out_f4_s2, out_f4_s3, out_f4_s4, out_f4_s5, out_f4_s6;
output out_f5_s1, out_f5_s2, out_f5_s3, out_f5_s4, out_f5_s5, out_f5_s6;
output out_f6_s1, out_f6_s2, out_f6_s3, out_f6_s4, out_f6_s5, out_f6_s6;
output out_f7_s1, out_f7_s2, out_f7_s3, out_f7_s4, out_f7_s5, out_f7_s6;

wire [0:0] from1 = in[0];
wire [1:0] from2 = in[1:0];
wire [2:0] from3 = in[2:0];
wire [3:0] from4 = in[3:0];
wire [4:0] from5 = in[4:0];
wire [5:0] from6 = in[5:0];
wire [6:0] from7 = in[6:0];

wire [0:0] sel1 = sel[0];
wire [1:0] sel2 = sel[1:0];
wire [2:0] sel3 = sel[2:0];
wire [3:0] sel4 = sel[3:0];
wire [4:0] sel5 = sel[4:0];
wire [5:0] sel6 = sel[5:0];

assign out_f1_s1 = from1[sel1];
assign out_f1_s2 = from1[sel2];
assign out_f1_s3 = from1[sel3];
assign out_f1_s4 = from1[sel4];
assign out_f1_s5 = from1[sel5];
assign out_f1_s6 = from1[sel6];

assign out_f2_s1 = from2[sel1];
assign out_f2_s2 = from2[sel2];
assign out_f2_s3 = from2[sel3];
assign out_f2_s4 = from2[sel4];
assign out_f2_s5 = from2[sel5];
assign out_f2_s6 = from2[sel6];

assign out_f3_s1 = from3[sel1];
assign out_f3_s2 = from3[sel2];
assign out_f3_s3 = from3[sel3];
assign out_f3_s4 = from3[sel4];
assign out_f3_s5 = from3[sel5];
assign out_f3_s6 = from3[sel6];

assign out_f4_s1 = from4[sel1];
assign out_f4_s2 = from4[sel2];
assign out_f4_s3 = from4[sel3];
assign out_f4_s4 = from4[sel4];
assign out_f4_s5 = from4[sel5];
assign out_f4_s6 = from4[sel6];

assign out_f5_s1 = from5[sel1];
assign out_f5_s2 = from5[sel2];
assign out_f5_s3 = from5[sel3];
assign out_f5_s4 = from5[sel4];
assign out_f5_s5 = from5[sel5];
assign out_f5_s6 = from5[sel6];

assign out_f6_s1 = from6[sel1];
assign out_f6_s2 = from6[sel2];
assign out_f6_s3 = from6[sel3];
assign out_f6_s4 = from6[sel4];
assign out_f6_s5 = from6[sel5];
assign out_f6_s6 = from6[sel6];

assign out_f7_s1 = from7[sel1];
assign out_f7_s2 = from7[sel2];
assign out_f7_s3 = from7[sel3];
assign out_f7_s4 = from7[sel4];
assign out_f7_s5 = from7[sel5];
assign out_f7_s6 = from7[sel6];

endmodule

/*+VL

module make_tests () ;

  wire [6:0] in, sel;

  select_tests #(1) blah (in, sel,
  out_f1_s1, out_f1_s2, out_f1_s3, out_f1_s4, out_f1_s5, out_f1_s6,
  out_f2_s1, out_f2_s2, out_f2_s3, out_f2_s4, out_f2_s5, out_f2_s6,
  out_f3_s1, out_f3_s2, out_f3_s3, out_f3_s4, out_f3_s5, out_f3_s6,
  out_f4_s1, out_f4_s2, out_f4_s3, out_f4_s4, out_f4_s5, out_f4_s6,
  out_f5_s1, out_f5_s2, out_f5_s3, out_f5_s4, out_f5_s5, out_f5_s6,
  out_f6_s1, out_f6_s2, out_f6_s3, out_f6_s4, out_f6_s5, out_f6_s6,
  out_f7_s1, out_f7_s2, out_f7_s3, out_f7_s4, out_f7_s5, out_f7_s6);

endmodule

*/
