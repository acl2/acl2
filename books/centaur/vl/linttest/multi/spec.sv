// VL Verilog Toolkit
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

module sub1 (output logic o, input logic a);
  assign o = a;
endmodule


module m0 (input normal_i1, multi_i1);

  // Some very basic cases.

  wire clk;

  wire [3:0] normal_a1;
  assign normal_a1 = 0;

  // This one should NOT be considered multiply driven because both writes
  // happen within the same always block.
  logic [3:0] normal_a2;
  always @(posedge clk)
  begin
    normal_a2 = 1;
    normal_a2 = 0;
  end

  wire normal_a3;
  buf(normal_a3, clk);

  wire normal_a4;
  sub1 sub4a (normal_a4, clk);


  wire [3:0] multi_a1;
  assign multi_a1 = 0;
  assign multi_a1 = 1;

  // This one should be multiply driven because it is driven by separate
  // blocks.
  logic [3:0] multi_a2;
  always @(posedge clk) multi_a2 = 1;
  always @(posedge clk) multi_a2 = 0;

  wire multi_a3;
  buf(multi_a3, 1'b1);
  xor(multi_a3, 1'b1, clk);

  wire multi_a4;
  sub1 sub4b (multi_a4, clk);
  assign multi_a4 = 0;

  // Driving an input should be considered a multiple driver.
  assign multi_i1 = 0;


endmodule


module m1 ;

  // Some fancy net types.
  //
  // These should not be regarded as multiply driven since they have special
  // resolution functions.

  tri normal_a1;
  assign normal_a1 = 1'b1;
  assign normal_a1 = 1'b0;

  wor  normal_a2;
  assign normal_a2 = 1'b1;
  assign normal_a2 = 1'b0;

  wand normal_a3;
  assign normal_a3 = 1'b1;
  assign normal_a3 = 1'b0;

  trior normal_a4;
  assign normal_a4 = 1'b1;
  assign normal_a4 = 1'b0;

  triand normal_a5;
  assign normal_a5 = 1'b1;
  assign normal_a5 = 1'b0;

  tri1 normal_a6;
  assign normal_a6 = 1'b1;
  assign normal_a6 = 1'b0;

  tri0 normal_a7;
  assign normal_a7 = 1'b1;
  assign normal_a7 = 1'b0;

  trireg normal_a8;
  assign normal_a8 = 1'b1;
  assign normal_a8 = 1'b0;

  supply1 normal_a9;
  assign normal_a9 = 1'b1;
  assign normal_a9 = 1'b0;

  supply0 normal_a10;
  assign normal_a10 = 1'b1;
  assign normal_a10 = 1'b0;

  wire 	 multi_a1;
  assign multi_a1 = 1'b1;
  assign multi_a1 = 1'b0;

  uwire	 multi_a2;
  assign multi_a2 = 1'b1;
  assign multi_a2 = 1'b0;

  logic	 multi_a3;
  assign multi_a3 = 1'b1;
  assign multi_a3 = 1'b0;

endmodule


module m2 ;

  // Some fancy transistor-level gates.  If we can see that a wire is being
  // involved in some sea of transistors, we should assume it is a
  // transistor-level thing and that multiple drivers are OK.

  wire multi_a1;
  buf(multi_a1, 1'b0);
  assign multi_a1 = 1'b1;

  wire normal_a1;
  pmos(normal_a1, 1'b0, 1'b1);
  assign normal_a1 = 1'b1;

  wire normal_a2, wna2;
  pmos(wna2, normal_a2, 1'b1);
  assign normal_a2 = 1'b1;

  wire normal_a3, wna3;
  pmos(wna3, 1'b1, normal_a3);
  assign normal_a3 = 1'b1;

  wire normal_b1;
  assign normal_b1 = 1'bz;
  assign normal_b1 = 1'b0;
  assign normal_b1 = 1'b1;

  wire normal_b2;
  assign normal_b2 = multi_a1 ? 1'bz : 1'b0;
  assign normal_b2 = 1'b0;

  wire normal_b3;
  assign normal_b3 = multi_a1 ? 1'b1 : 1'bz;
  assign normal_b3 = 1'b0;

endmodule




typedef struct packed { logic [3:0] a, b; } foo_t;

module m3 ;

  // Some basic tests of structure handling.

  foo_t normal_f1;
  assign normal_f1 = 0;

  foo_t normal_f2;
  assign normal_f2.a = 0;
  assign normal_f2.b = 1;

  foo_t multi_f1;
  assign multi_f1 = 0;
  assign multi_f1 = 1;

  foo_t multi_f2;
  assign multi_f2.a = 0;
  assign multi_f2.a = 1;

endmodule

module m4;

  wire [3:0] normal_a1;
  assign normal_a1[0] = 1;
  assign normal_a1[1] = 1;
  assign normal_a1[2] = 1;
  assign normal_a1[3] = 1;

  wire [3:0] normal_a2;
  assign normal_a2[0] = 1;
  assign normal_a2[2:1] = 1;
  assign normal_a2[3] = 1;

  wire [3:0] multi_a1;
  assign multi_a1 = 0;
  assign multi_a1[1] = 1;

  wire [3:0] multi_a2;
  assign multi_a2[3] = 1;
  assign multi_a2[2:0] = 1;
  assign multi_a2[1] = 1;

  wire [3:0] multi_a3;
  assign multi_a3[3] = 1;
  assign multi_a3[2] = 1;
  assign multi_a3[1] = 1;
  assign multi_a3[0] = 1;
  assign multi_a3[1] = 1;

  wire [3:0] multi_a4;
  assign multi_a4[3] = 1;
  assign multi_a4[2] = 1;
  assign multi_a4[1:0] = 1;
  assign multi_a4[0] = 1;
  assign multi_a4[1] = 1;

endmodule


interface Protocol;
  logic        req;
  logic        ack;
  logic [63:0] dat;
endinterface

module m5 (Protocol normal_p1);

  wire multi_a0;
  assign multi_a0 = 1;
  assign multi_a0 = 0;

  assign normal_p1.req = 1;
  assign normal_p1.ack = 1;
  assign normal_p1.dat = 0;

  Protocol normal_p2();
  assign normal_p2.req = 1;

  Protocol multi_p1();
  assign multi_p1.req = 1;
  assign multi_p1.req = 0;

endmodule


module m6 ;

  logic [3:0][4:0] normal_a1;
  assign normal_a1[0] = 0;
  assign normal_a1[1] = 1;
  assign normal_a1[2] = 2;
  assign normal_a1[3] = 3;

  logic [3:0][4:0] multi_a1;
  assign multi_a1[0] = 0;
  assign multi_a1[0] = 1;

endmodule




// BOZO more things to eventually support and check
//  - more testing of structures/fields
//  - array types and structure arrays
//  - module instance arrays
