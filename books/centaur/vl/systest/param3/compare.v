// VL Verilog Toolkit
// Copyright (C) 2008-2014 Centaur Technology
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
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
//   THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.
//
// Original author: Jared Davis <jared@centtech.com>

// Stupid little two-level unparameterization test, with some bad modules
// thrown in to boot.

`include "spec.v"

`ifdef SYSTEM_VERILOG_MODE
 `include "impl.sv"
`else
 `include "impl.v"
`endif

module test ();

  reg [2:0] a;
  wire [2:0] o1, o2;

  GoodE spec (o1, a);
  \GoodE$blah=1 impl (o2, a);


  integer    i;
  initial begin
    for(i = 0; i < 8; i = i + 1)
    begin
      a = i;
      #10;
      if (o1 === o2)
      begin
	$display("looks ok for %d", a);
      end
      else
      begin
	$display("fail: a = %d, o1 = %d, o2 = %d", a, o1, o2);
      end
    end

  end

endmodule
