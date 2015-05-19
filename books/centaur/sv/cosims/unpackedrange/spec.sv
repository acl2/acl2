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

typedef struct packed {
  logic [3:0] a;
  logic [3:0] b;
  logic [3:0] op;
} alu_in;

module sub (input alu_in ain [1:0],
	    output logic [3:0] res [1:0]);

   assign res[0] = ain[0].op[1] ?
		   ain[0].op[0] ? ain[0].a + ain[0].b : ain[0].a - ain[0].b :
		   ain[0].op[0] ? ain[0].a & ain[0].b : ain[0].a | ain[0].b;

   assign res[1] = ain[1].op[1] ?
		   ain[1].op[0] ? ain[1].a + ain[1].b : ain[1].a - ain[1].b :
		   ain[1].op[0] ? ain[1].a & ain[1].b : ain[1].a | ain[1].b;

endmodule // sub

module spec (input logic [127:0] in,
	     output wire [127:0] out);

   alu_in ain [3:0];
   assign { ain[0].a, ain[0].b, ain[0].op,
	    ain[1].a, ain[1].b, ain[1].op
	    } = in;

  logic [3:0] o [1:0];
   assign out = {o[1], o[0]};

   sub subinst (.ain(ain[1:0]), .res(o));

endmodule // spec
