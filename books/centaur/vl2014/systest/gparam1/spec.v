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

parameter [4:0] globalp1 = 12;

package pkg1 ;
  parameter [3:0] pkgparam1 = 6;
endpackage

package pkg2 ;
  parameter [9:0] pkgparam2 = 1582;
endpackage

package pkg3 ;
  parameter [12:0] pkgparam3 = 9876;
endpackage

module dut (o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10,
            a, n1, n2);

  parameter size = 1;
  wire make_size_matter = size;

  output [40:0] o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10;
  input [3:0]  a, n1, n2;

  parameter [4:0] localp1 = 17;

  import pkg1::*;
  import pkg2::pkgparam2;

  assign o0  = {n1,localp1,n2};
  assign o1  = {n1,globalp1,n2};
  assign o2  = {n1,pkgparam1,n2};
  assign o3  = {n1,pkgparam2,n2};

// BOZO fixme, doesn't work yet  assign o4  = {n1,pkg3::pkgparam3,n2};
  assign o4 = 0;

  assign o5  = 0;
  assign o6  = 0;
  assign o7  = 0;
  assign o8  = 0;
  assign o9  = 0;
  assign o10 = 0;

  initial begin
    #10;
    $display(" o0 = %b",  o0);
    $display(" o1 = %b",  o1);
    $display(" o2 = %b",  o2);
    $display(" o3 = %b",  o3);
    $display(" o4 = %b",  o4);
    $display(" o5 = %b",  o5);
    $display(" o6 = %b",  o6);
    $display(" o7 = %b",  o7);
    $display(" o8 = %b",  o8);
    $display(" o9 = %b",  o9);
    $display("o10 = %b", o10);
  end

endmodule


/*+VL

module make_tests () ;

   wire [3:0] a;

   dut #(1) inst (a, a, a, a, a, a, a, a);

endmodule

*/


`endif
