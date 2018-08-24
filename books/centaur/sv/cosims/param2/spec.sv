// Cosim Test for submodule parameter parens
// Copyright (C) 2016 Apple, Inc.
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
// Original author: Jared Davis

module sub #(parameter WIDTH = 1)
   (output [WIDTH-1:0] o,
    input [WIDTH-1:0] a,
    input [WIDTH-1:0] b);
   assign o = a & b;
endmodule

module spec (input logic [127:0] in,
	     output wire [127:0] out);

   logic o1, a1, b1;
   assign {a1,b1} = in;
   sub mysub1 (o1, a1, b1);

   logic o2, a2, b2;
   assign {a2,b2} = in;
   sub #(1) mysub2 (o2, a2, b2);

   // Surprisingly the following is allowed and appears to be treated as
   // equivalent to sub #(1).  This seems to contradict the SystemVerilog-2012
   // grammar which clearly has parentheses:
   //
   // parameter_value_assignment ::= '#' '(' [list_of_parameter_assignments] ')'
   //
   // But other tools accept the paren-free syntax.

   logic o3, a3, b3;
   assign {a3,b3} = in;
   sub #1 mysub3 (o3, a3, b3);

   logic [1:0] o4, a4, b4;
   assign {a4,b4} = in;
   sub #2 mysub4 (o4, a4, b4);

   logic [1:0] o5, a5, b5;
   assign {a5,b5} = in;
   sub #(.WIDTH(2)) mysub5 (o5, a5, b5);

   assign out = {o5, o4, o3, o2, o1};

   // initial begin
   //    #10;
   //    $display("mysub1.width is %d", mysub1.WIDTH);
   //    $display("mysub2.width is %d", mysub2.WIDTH);
   //    $display("mysub3.width is %d", mysub3.WIDTH);
   //    $display("mysub4.width is %d", mysub4.WIDTH);
   //    $display("mysub5.width is %d", mysub5.WIDTH);
   // end

endmodule
