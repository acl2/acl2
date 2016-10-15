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

interface alu_iface ();

  parameter version = 1;

  logic [3:0] a;
  logic [3:0] b;

  if (version == 1)
  begin : foo
    logic [3:0] out1;
  end
  else
  begin : bar
    logic [3:0] out2;
  end

endinterface

module alu1 (alu_iface aif);
  assign aif.foo.out1 = aif.a;
endmodule

module alu2 (alu_iface aif);
  assign aif.bar.out2 = aif.b;
endmodule


module spec (input logic [127:0] in,
	     output wire [127:0] out);


  // VCS J-2014.12-SP3-1 fails and says about the following line:
  //   Feature is not yet supported: Xmrs into scopes within interface
  // presumably xmrs is "cross module references"

  alu_iface #(.version(1)) aif1 ();

  assign {aif1.a, aif1.b} = in[7:0];

  alu1 aluinst1 (aif1);


  alu_iface #(.version(2)) aif2 ();

  assign {aif2.a, aif2.b} = ~in[7:0];

  alu2 aluinst2 (aif2);


  assign out = { aif1.a,
                 aif1.b,
                 aif1.foo.out1,
                 aif2.a,
                 aif2.b,
                 aif2.bar.out2 };

endmodule // spec
