// SV - Symbolic Vector Hardware Analysis Framework
// Copyright (C) 2014-2015 Centaur Technology
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
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.
//
// Original author: Jared Davis <jared@centtech.com>

module subassign2 (input [1:0] out, output [1:0] in) ; // NOTE: directions intentionally wrong!!
  assign out = in;
endmodule

module spec (input logic [127:0] in, output wire [127:0] out);

  wire       a1 = in;
  wire [1:0] a2 = in;
  wire [2:0] a3 = in;
  wire [3:0] a4 = in;
  wire [5:0] a5 = in;
  wire [6:0] a6 = in;
  wire [7:0] a7 = in;

  // Instances with correct output size, but varying input size
  wire [1:0] xx1; subassign2 ininst1 (xx1, a1);
  wire [1:0] xx2; subassign2 ininst2 (xx2, a2);
  wire [1:0] xx3; subassign2 ininst3 (xx3, a3);
  wire [1:0] xx4; subassign2 ininst4 (xx4, a4);
  wire [1:0] xx5; subassign2 ininst5 (xx5, a5);
  wire [1:0] xx6; subassign2 ininst6 (xx6, a6);
  wire [1:0] xx7; subassign2 ininst7 (xx7, a7);

  // Instances with correct input size, but varying output size
  wire       yy1; subassign2 outinst1 (yy1, a2);
  wire [1:0] yy2; subassign2 outinst2 (yy2, a2);
  wire [2:0] yy3; subassign2 outinst3 (yy3, a2);
  wire [3:0] yy4; subassign2 outinst4 (yy4, a2);
  wire [4:0] yy5; subassign2 outinst5 (yy5, a2);
  wire [5:0] yy6; subassign2 outinst6 (yy6, a2);
  wire [6:0] yy7; subassign2 outinst7 (yy7, a2);

  assign out = {xx7, xx6, xx5, xx4, xx3, xx2, xx1,
                yy7, yy6, yy5, yy4, yy3, yy2, yy1 };

endmodule
