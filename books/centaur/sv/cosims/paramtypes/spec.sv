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
// Original authors: Sol Swords <sswords@centtech.com>
//                   Jared Davis <jared@centtech.com>

// Tests of top-level explicit value parameter handling
// This is tricky because you have to be careful to convert the rhs to the
// right datatype.

parameter logic [5:0] a1 = 3'b100 << 1'b1;
parameter logic [5:0] a2 = 3'b100 << 1;
parameter logic [5:0] a3 = 3'sb100 << 1;
parameter logic signed [5:0] a4 = 3'b100 << 1;
parameter logic signed [5:0] a5 = 3'sb100 << 1;

parameter logic signed [5:0] b1 = 3'sb 110 >>> 1'sb1 ;
parameter logic signed [5:0] b2 = 3'sb 110 >>> 1 ;
parameter logic signed [5:0] b3 = 6'b 111100 >>> 1'sb1 ;
parameter logic signed [5:0] b4 = 6'b 111100 >>> 1 ;
parameter logic signed [5:0] b5 = 3'sb 110;
parameter logic signed [5:0] b6 = 3'b 110;

parameter logic [5:0] c1 = 3'sb 110 >>> 1'sb1 ;
parameter logic [5:0] c2 = 3'sb 110 >>> 1 ;
parameter logic [5:0] c3 = 6'b 111100 >>> 1'sb1 ;
parameter logic [5:0] c4 = 6'b 111100 >>> 1 ;

module spec (input logic [127:0] in,
	     output logic [127:0] out);

   assign out = { c4, c3, c2, c1,
		  b6, b5, b4, b3, b2, b1,
		  a5, a4, a3, a2, a1 };

endmodule

