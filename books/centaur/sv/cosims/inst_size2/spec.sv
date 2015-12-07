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

module sub (output [2:0] out, input [2:0] a, input [2:0] b) ;
  assign out = a + b;
endmodule

module spec (input logic [127:0] in, output wire [127:0] out);

  wire       a1, b1; assign {a1, b1} = in;
  wire [1:0] a2, b2; assign {a2, b2} = in;
  wire [2:0] a3, b3; assign {a3, b3} = in;
  wire [3:0] a4, b4; assign {a4, b4} = in;
  wire [4:0] a5, b5; assign {a5, b5} = in;
  wire [5:0] a6, b6; assign {a6, b6} = in;
  wire [6:0] a7, b7; assign {a7, b7} = in;

  // Instances with correct output size, but varying input size
  wire [1:0] xx1; sub ininst1 (xx1, a1, b1);
  wire [1:0] xx2; sub ininst2 (xx2, a2, b2);
  wire [1:0] xx3; sub ininst3 (xx3, a3, b3);
  wire [1:0] xx4; sub ininst4 (xx4, a4, b4);
  wire [1:0] xx5; sub ininst5 (xx5, a5, b5);
  wire [1:0] xx6; sub ininst6 (xx6, a6, b6);
  wire [1:0] xx7; sub ininst7 (xx7, a7, b7);

  // Instances with correct input size, but varying output size
  wire       yy1; sub outinst1 (yy1, a3, b3);
  wire [1:0] yy2; sub outinst2 (yy2, a3, b3);
  wire [2:0] yy3; sub outinst3 (yy3, a3, b3);
  wire [3:0] yy4; sub outinst4 (yy4, a3, b3);
  wire [4:0] yy5; sub outinst5 (yy5, a3, b3);
  wire [5:0] yy6; sub outinst6 (yy6, a3, b3);
  wire [6:0] yy7; sub outinst7 (yy7, a3, b3);

  assign out = {xx7, xx6, xx5, xx4, xx3, xx2, xx1,
                yy7, yy6, yy5, yy4, yy3, yy2, yy1 };

endmodule
