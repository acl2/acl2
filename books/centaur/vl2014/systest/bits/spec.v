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

module dut (o1, o2, o3, o4, o5, a, n1, n2);

  parameter size = 1;
  wire make_size_matter = size;

  output [40:0] o1, o2, o3, o4, o5;
  input [3:0]  a, n1, n2;

  // BOZO too hard -- we don't comprehend $bits on the rhs.
  //  assign o1 = {$bits(o1)};

  wire [$bits(o1):30] o2_temp = -1;
  assign o2 = {n1,o2_temp,n2};

  // BOZO: This is too hard for VL if we put in o2_temp here instead of o2.
  // wire [$bits( o2_temp[17:0] ):13] o3_temp = -1;


  wire [$bits( o2[17:0] ):13] o3_temp = -1;
  assign o3 = {n1,o3_temp,n2};

  assign o4 = { o3[$bits(n1)+$bits(n2) : 0],
                n1[$bits(n1)-1] };

  assign o5 = { {$bits(n1){1'b1}},
                n1,
                {$bits(n2)-1{1'b0}},
                n2 };

/*
  initial begin
    #10;

    $display("o1 = %d", o1);

    $display("o2_temp is %b", o2_temp);
    $display("o2 = %b",       o2);

    $display("o3_temp is %b", o3_temp);
    $display("o3 = %b", o3);

    $display("o4 = %b", o4);
    $display("o5 = %b", o5);
  end
 */

endmodule


/*+VL

module make_tests () ;

   wire [3:0] a;

   dut #(1) inst (a, a, a, a, a, a, a, a);

endmodule

*/


`endif
