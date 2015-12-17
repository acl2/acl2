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

// Note: NCV and VCS disagree about c4_sign and c3_sign below.  We
// think VCS's behavior makes sense: the parameter is declared
// unsigned, so treat it as unsigned regardless of the signedness of
// the value assigned to it.

parameter [5:0] a1 = 5'b11010;
parameter [5:0] a2 = 8'b10101000;
parameter [5:0] a3 = 5'sb11010;
parameter [5:0] a4 = 8'sb10101000;

parameter signed [5:0] b1 = 5'b11010;
parameter signed [5:0] b2 = 8'b10101000;
parameter signed [5:0] b3 = 5'sb11010;
parameter signed [5:0] b4 = 8'sb10101000;

parameter unsigned [5:0] c1 = 5'b11010;
parameter unsigned [5:0] c2 = 8'b10101000;
parameter unsigned [5:0] c3 = 5'sb11010;
parameter unsigned [5:0] c4 = 8'sb10101000;


module spec (input logic [127:0] in,
	     output logic [127:0] out);

  wire [$bits(a1):0] a1_signcheck = a1; wire a1_sign = a1_signcheck[$bits(a1)];
  wire [$bits(a2):0] a2_signcheck = a2; wire a2_sign = a2_signcheck[$bits(a2)];
  wire [$bits(a3):0] a3_signcheck = a3; wire a3_sign = a3_signcheck[$bits(a3)];
  wire [$bits(a4):0] a4_signcheck = a4; wire a4_sign = a4_signcheck[$bits(a4)];

  wire [$bits(b1):0] b1_signcheck = b1; wire b1_sign = b1_signcheck[$bits(b1)];
  wire [$bits(b2):0] b2_signcheck = b2; wire b2_sign = b2_signcheck[$bits(b2)];
  wire [$bits(b3):0] b3_signcheck = b3; wire b3_sign = b3_signcheck[$bits(b3)];
  wire [$bits(b4):0] b4_signcheck = b4; wire b4_sign = b4_signcheck[$bits(b4)];

  wire [$bits(c1):0] c1_signcheck = c1; wire c1_sign = c1_signcheck[$bits(c1)];
  wire [$bits(c2):0] c2_signcheck = c2; wire c2_sign = c2_signcheck[$bits(c2)];
  wire [$bits(c3):0] c3_signcheck = c3; wire c3_sign = c3_signcheck[$bits(c3)];
  wire [$bits(c4):0] c4_signcheck = c4; wire c4_sign = c4_signcheck[$bits(c4)];


   assign out = { c4, c3, c2, c1,
		  b4, b3, b2, b1,
		  a4, a3, a2, a1,
		  c4_sign, c3_sign, c2_sign, c1_sign,
		  b4_sign, b3_sign, b2_sign, b1_sign,
		  a4_sign, a3_sign, a2_sign, a1_sign
		  };
   
endmodule
