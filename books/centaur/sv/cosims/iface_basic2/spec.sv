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

// Like iface_basic, but we'll drive outputs from multiple modules

interface alu_iface ();
  logic [3:0] a;
  logic [3:0] b;
  logic [3:0] op;
  logic [3:0] out1;
  logic [3:0] out2;
endinterface

module alu1 (alu_iface aif);

   assign aif.out1 = aif.op[1] ?
		     aif.op[0] ? aif.a + aif.b : aif.a - aif.b :
		     aif.op[0] ? aif.a & aif.b : aif.a | aif.b;

endmodule

module alu2 (alu_iface aif);

  assign aif.out2 = ~aif.out1;

endmodule

module spec (input logic [127:0] in,
	     output wire [127:0] out);

  alu_iface aif ();
  assign {aif.a, aif.b, aif.op} = in;

  alu1 aluinst1 (aif);
  alu2 aluinst2 (aif);

  assign out = { aif.a, aif.b, aif.op, aif.out1, aif.out2 };

endmodule // spec
