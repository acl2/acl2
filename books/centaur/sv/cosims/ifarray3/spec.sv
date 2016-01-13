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

interface alu_iface (input logic[1:0] op);
  logic [3:0] a;
  logic [3:0] b;
  logic [4:0] out;
endinterface

// Test of a module that takes an interface array

module alu (alu_iface aif[5:0]);

  for(genvar i = 0; i < 6; ++i)
  begin
    assign aif[i].out = (aif[i].op == 0) ? aif[i].a + aif[i].b
                      : (aif[i].op == 1) ? aif[i].a - aif[i].b
                      : (aif[i].op == 2) ? aif[i].a & aif[i].b
                      : aif[i].a | aif[i].b;
  end

endmodule

module spec (input logic [127:0] in,
             output wire [127:0] out);

  logic [1:0] op;

  alu_iface ifaces [5:0] (op);

  assign {ifaces[5].a, ifaces[5].b,
          ifaces[4].a, ifaces[4].b,
          ifaces[3].a, ifaces[3].b,
          ifaces[2].a, ifaces[2].b,
          ifaces[1].a, ifaces[1].b,
          ifaces[0].a, ifaces[0].b,
          op } = in;

  alu sub (ifaces);

  assign out = { ifaces[5].out,
                 ifaces[4].out,
                 ifaces[3].out,
                 ifaces[2].out,
                 ifaces[1].out,
                 ifaces[0].out };

endmodule
