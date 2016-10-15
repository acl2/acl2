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


// Basic checks of port sizes/types being correctly inherited

module m1 (output [3:0] size, input logic [3:0] foo, bar);
  assign size = $bits(bar);
endmodule

module m2 (output [3:0] size, input foo, bar);
  assign size = $bits(bar);
endmodule

interface i1 (input [3:0] foo, bar);
  wire [3:0] size;
endinterface

module i1Loader(i1 iface);
  assign iface.size = $bits(iface.bar);
endmodule

module spec (input logic [127:0] in,
	     output logic [127:0] out);

  wire [3:0] m1_size1, m1_size2;
  wire [3:0] m1_foo;
  wire [3:0] m1_bar1;
  wire 	     m1_bar2;

  m1 m1_inst1 (m1_size1, m1_foo, m1_bar1);
  m1 m1_inst2 (m1_size2, m1_foo, m1_bar2);

  wire [3:0] m2_size;
  m2 m2_inst (.size(m2_size), .foo(), .bar());

  wire [3:0] i1_foo;
  wire [3:0] i1_bar1;
  wire 	     i2_bar2;

  i1 i1_inst1(i1_foo, i1_bar1);
  i1 i1_inst2(i1_foo, i2_bar2);

  i1Loader i1_inst1_loader(i1_inst1);
  i1Loader i1_inst2_loader(i1_inst2);

  assign out = { i1_inst1.size, i1_inst2.size, m2_size, m1_size1, m1_size2 };

  initial begin
    #10;
    $display("m1: size1 is %d, size2 is %d", m1_size1, m1_size2);
    $display("m2: size is %d", m2_size);
    $display("i1_inst1: size is %d", i1_inst1.size);
    $display("i1_inst2: size is %d", i1_inst2.size);

  end

endmodule
