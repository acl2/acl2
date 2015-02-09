// VL 2014 -- Verilog Toolkit, 2014 Edition
// Copyright (C) 2008-2015 Centaur Technology
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

`ifdef SYSTEM_VERILOG_MODE

module dut ( input [7:0] in1, in2,
             output [7:0] out1, out2, out3, out4, out5 );

  parameter size = 1;
  wire make_size_matter = size;


  function logic f1 (logic signed a, unsigned b);
    reg [3:0] r;
    r = b;
    f1 = a ^ r;
  endfunction

  assign out1 = f1(in1, in2);


  function logic [3:0] f2 (input a, input b);
    reg       r0;
    logic     r1;
    r0 = 0;
    r1 = 1;
    f2 = {r0, r1, a, b};
  endfunction

  assign out2 = f2(in1, in2);


  function signed [3:0] f3 (input logic [3:0] a, input b);
    f3 = a & b;
  endfunction

  assign out3 = f3(in1, in2);

  // var is a tricky case: does it mean the variable has a type and therefore shouldn't
  // inherit the type from the previous port?  i think so?

  // From the spec, I think it should be legal to just use "var b" here, but neither
  // NCV nor VCS allows it.  VCS doesn't even allow input var, but NCV allows it.

  function signed [3:0] f4 (input logic [3:0] a,

                              `ifdef VL_SYSTEST_VCS
                                     input b
                               `else
                                     input var b
                                `endif
  );

    f4 = a & b;
  endfunction

  assign out4 = f4(in1, in2);


  function signed [3:0] f5 (signed [3:0] a, unsigned b);
    f5 = a < b;
  endfunction

  assign out5 = f5(in1, in2);

endmodule



/*+VL

module make_tests () ;

 wire [7:0] w;
 dut #(1) test1 (w, w, w, w, w, w, w);

endmodule
*/


`endif
