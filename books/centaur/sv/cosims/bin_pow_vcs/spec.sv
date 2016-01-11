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

  wire [3:0] a4;
  wire [2:0] a3;
  wire a1;

  wire [2:0] b3;
  wire [1:0] b2;
  wire b1;

  wire signed [3:0] c4 = a4;
  wire signed [2:0] c3 = a3;
  wire signed 	    c1 = a1;

  wire signed [2:0] d3 = b3;
  wire signed [1:0] d2 = b2;
  wire signed       d1 = b1;

  wire [8:0]  o1 = a4 ** b3;
  wire [3:0]  o2 = a3 ** b2;
  wire 	      o3 = a1 ** b1;
  wire [15:0] o4 = a4 ** b3;
  wire [6:0]  o5 = a3 ** b3;

  wire [8:0]  o6 = c4 ** d3;
  wire [3:0]  o7 = c3 ** d2;
  wire 	      o8 = c1 ** d1;
  wire [15:0] o9 = c4 ** d3;
  wire [6:0]  o10 = c3 ** d3;

   assign { a4, a3, a1, b3, b2, b1 } = in;

  assign out = {
    o10, o9, o8, o7, o6,
    o5, o4, o3, o2, o1
  };

endmodule // spec
