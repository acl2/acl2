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

module spec (input logic [127:0] in,
	     output wire [127:0] out);

  // 45 bits of A wires.
  wire [8:0] a9;
  wire [7:0] a8;
  wire [6:0] a7;
  wire [5:0] a6;
  wire [4:0] a5;
  wire [3:0] a4;
  wire [2:0] a3;
  wire [1:0] a2;
  wire 	     a1;

  // 45 bits of B wires.
  wire signed [8:0] b9;
  wire signed [7:0] b8;
  wire signed [6:0] b7;
  wire signed [5:0] b6;
  wire signed [4:0] b5;
  wire signed [3:0] b4;
  wire signed [2:0] b3;
  wire signed [1:0] b2;
  wire signed 	    b1;

  wire [8:0] oa9 = ~a9;
  wire [7:0] oa8 = ~a8;
  wire [6:0] oa7 = ~a7;
  wire [5:0] oa6 = ~a6;
  wire [4:0] oa5 = ~a5;
  wire [3:0] oa4 = ~a4;
  wire [2:0] oa3 = ~a3;
  wire [1:0] oa2 = ~a2;
  wire 	     oa1 = ~a1;

  wire [8:0] ob9 = ~b9;
  wire [7:0] ob8 = ~b8;
  wire [6:0] ob7 = ~b7;
  wire [5:0] ob6 = ~b6;
  wire [4:0] ob5 = ~b5;
  wire [3:0] ob4 = ~b4;
  wire [2:0] ob3 = ~b3;
  wire [1:0] ob2 = ~b2;
  wire 	     ob1 = ~b1;

  wire [5:0] oc1 = ~a9; // signed and unsigned truncation
  wire [5:0] oc2 = ~a9;
  wire [5:0] oc3 = ~a3; // signed and unsigned extension
  wire [5:0] oc4 = ~b3;
  wire [5:0] oc5 = ~a1; // signed and unsigned extension of 1 bit
  wire [5:0] oc6 = ~b1;

  assign { a9, a8, a7, a6, a5, a4, a3, a2, a1,
           b9, b8, b7, b6, b5, b4, b3, b2, b1 } = in;

  assign out = {
	       oc6, oc5, oc4, oc3, oc2, oc1,
               ob9, ob8, ob7, ob6, ob5, ob4, ob3, ob2, ob1,
               oa9, oa8, oa7, oa6, oa5, oa4, oa3, oa2, oa1
	       };

endmodule // spec
