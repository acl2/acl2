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
  logic [2:0] [3:0] a;
  logic [2:0] [3:0] b;
  logic [2:0] [3:0] op;
  logic [2:0] [3:0] res;
} alu_in;

module sub (inout alu_in ain); // BOZO make this work without the INOUT

   assign ain.res[0] = ain.op[0][1] ?
		       ain.op[0][0] ? ain.a[0] + ain.b[0] : ain.a[0] - ain.b[0] :
		       ain.op[0][0] ? ain.a[0] & ain.b[0] : ain.a[0] | ain.b[0];

   assign ain.res[1] = ain.op[1][1] ?
		       ain.op[1][0] ? ain.a[1] + ain.b[1] : ain.a[1] - ain.b[1] :
		       ain.op[1][0] ? ain.a[1] & ain.b[1] : ain.a[1] | ain.b[1];

   assign ain.res[2] = ain.op[2][1] ?
		       ain.op[2][0] ? ain.a[2] + ain.b[2] : ain.a[2] - ain.b[2] :
		       ain.op[2][0] ? ain.a[2] & ain.b[2] : ain.a[2] | ain.b[2];

endmodule // sub



module spec (input logic [127:0] in,
	     output [127:0] out);

   wire alu_in ain [0:2];
   assign ain[0].a = in[11:0];
   assign ain[0].b = in[23:12];
   assign ain[0].op = in[35:24];

   assign ain[1].a = in[47:36];
   assign ain[1].b = in[59:48];
   assign ain[1].op = in[71:60];

   assign ain[2].a = in[83:72];
   assign ain[2].b = in[95:84];
   assign ain[2].op = in[107:96];

   sub subinst [2:0] (.ain(ain));

   assign out[11:0] = ain[0].res;
   assign out[23:12] = ain[1].res;
   assign out[35:24] = ain[2].res;


endmodule // spec
