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
// Original author: Sol Swords <sswords@centtech.com>

// BOZO this test has nothing to do with gates, should be renamed.

module sub (input logic [3:0] a,
	    input logic [3:0] b,
	    output logic [3:0] res0,
	    output logic [3:0] res1,
	    output logic [3:0] res2,
	    output logic [3:0] res3,
	    output logic [3:0] res4,
	    output logic [3:0] res5,
	    output logic [3:0] res6,
	    output logic [3:0] res7);

   assign res0 = a & b;
   assign res1 = a | b;
   assign res2 = a ^ b;
   assign res3 = a << b;
   assign res4 = a >> b;
   assign res5 = a + b;
   assign res6 = a - b;
   assign res7 = a ~^ b;


endmodule // sub

module spec (input logic [127:0] in,
	     output logic [127:0] out);

  logic [3:0] a;
  logic [3:0] b;
  logic [3:0] res0;
  logic [3:0] res1;
  logic [3:0] res2;
  logic [3:0] res3;
  logic [3:0] res4;
  logic [3:0] res5;
  logic [3:0] res6;
  logic [3:0] res7;

   assign {a, b} = in;
   assign out = {res0, res1, res2, res3, res4, res5, res6, res7};

   sub subinst (.*);

endmodule // spec
