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

  wire [8:0] a9;
  wire [3:0] a4;
  wire a1;

  wire [8:0] b9;
  wire [5:0] b6;
  wire [1:0] b2;

  wire signed [8:0] c9 = a9;
  wire signed [3:0] c4 = a4;
  wire signed 	    c1 = a1;

  wire signed [8:0] d9 = b9;
  wire signed [5:0] d6 = b6;
  wire signed [1:0] d2 = b2;


  wire [8:0]  o1 = a9 != b9;
  wire [3:0]  o2 = a4 != b6;
  wire 	      o3 = a1 != b2[0];
  wire [15:0] o4 = a9 != b6;
  wire [6:0]  o5 = a9 != b9;

  wire [8:0]  o6 = c9 != d9;
  wire [3:0]  o7 = c4 != d6;
  wire 	      o8 = c1 != d2;
  wire [15:0] o9 = c9 != d6;
  wire [6:0]  o10 = c9 != d2;

  assign { a9, a4, a1, b9, b6, b2 } = in;

  assign out = {
    o10, o9, o8, o7, o6,
    o5, o4, o3, o2, o1
  };

endmodule // spec
