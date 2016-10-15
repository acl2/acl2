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

module sub (output o, input a, input b);
  assign o = a & b;
endmodule

interface mybus (input clk);
  logic [3:0] foo;
endinterface

module top ;

  wire a, b;

  wire w1_dupe;
  assign w1_dupe = a & b;
  assign w1_dupe = a & b;

  wire w1_nodupe = a ^ b;

  wire w2_dupe;
  and (w2_dupe, a, b);
  and (w2_dupe, a, b);

  wire w2a_nodupe, w2b_nodupe;
  and a1 (w2a_nodupe, a, b);
  and a2 (w2b_nodupe, a, b);

  wire w3a_dupe, w3b_dupe;
  alias w3a_dupe = w3b_dupe;
  alias w3a_dupe = w3b_dupe;

  wire w3a_nodupe, w3b_nodupe, w3c_nodupe;
  alias w3a_nodupe = w3b_nodupe;
  alias w3c_nodupe = w3b_nodupe;

  wire w4a_dupe, w4b_dupe, w4c_dupe;
  sub s1a_dupe(w4a_dupe, w4b_dupe, w4c_dupe);
  sub s1b_dupe(w4a_dupe, w4b_dupe, w4c_dupe);

  wire w4a_nodupe, w4b_nodupe, w4c_nodupe, w4d_nodupe, w4e_nodupe, w4f_nodupe;
  sub s1a_nodupe(w4a_nodupe, w4b_nodupe, w4c_nodupe);
  sub s1b_nodupe(w4d_nodupe, w4e_nodupe, w4f_nodupe);

  logic w5_dupe, w5_nodupe;
  initial begin
    w5_dupe = a & b;
  end
  initial begin
    w5_dupe = a & b;
  end
  initial begin
    w5_nodupe = a & b;
  end

  logic w6_dupe, w6_nodupe;
  final w6_dupe = a & b;
  final w6_dupe = a & b;
  final w6_nodupe = a & b;

  logic w7_dupe, w7_nodupe, clk;
  always @(posedge clk) w7_dupe <= a & b;
  always @(posedge clk) w7_dupe <= a & b;
  always @(posedge clk) w7_nodupe <= a & b;

  wire w8_dupe, w8_nodupe;
  assert property (@(posedge clk) always w8_dupe);
  assert property (@(posedge clk) always w8_dupe);
  assert property (@(posedge clk) always w8_nodupe);

  wire w9_dupe, w9_nodupe;
  assert #0 (!a || w9_dupe);
  assert #0 (!a || w9_dupe);
  assert #0 (!a || w9_nodupe);

  wire w10_dupe, w10_nodupe;
  sequence s1;
    w10_dupe ##1 a;
  endsequence
  sequence s1;
    w10_dupe ##1 a;
  endsequence
  sequence s2;
    w10_nodupe ##1 a;
  endsequence

  wire w11_dupe, w11_nodupe;
  property p1;
    always w11_dupe ##1 a;
  endproperty
  property p1;
    always w11_dupe ##1 a;
  endproperty
  property p2;
    always w11_nodupe ##1 a;
  endproperty

  // We originally warned about this because it looked like module
  // instances with the same ports.  But that's silly because it's an
  // interface and of course it's OK to have more than one of them.
  wire busclk;
  mybus bus1(busclk);
  mybus bus2(busclk);



  // We want to make sure not to warn about these since they're in different
  // branches of generates.
  parameter size = 4;
  wire w12_nodupe;
  if (size == 0)
  begin
    buf(w12_nodupe, a);
  end
  else
  begin
    buf(w12_nodupe, a);
  end

  // We want to make sure not to warn about these since they're in different
  // branches of generates.
  wire w13_nodupe;
  if (size == 0)
  begin
    sub mysub13 (w13_nodupe, a, a);
  end
  else
  begin
    sub mysub13 (w13_nodupe, a, a);
  end


endmodule
