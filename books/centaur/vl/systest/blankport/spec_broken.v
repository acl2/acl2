// VL Verilog Toolkit
// Copyright (C) 2008-2014 Centaur Technology
//
// Contact:
//   Centaur Technology Formal Verification Group
//   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
//   http://www.centtech.com/
//
// This program is free software; you can redistribute it and/or modify it under
// the terms of the GNU General Public License as published by the Free Software
// Foundation; either version 2 of the License, or (at your option) any later
// version.  This program is distributed in the hope that it will be useful but
// WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
// more details.  You should have received a copy of the GNU General Public
// License along with this program; if not, write to the Free Software
// Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
//
// Original author: Jared Davis <jared@centtech.com>

// basic test of blank port support

module blankport_test (o, a, b);

   parameter size = 1;

   output [7:0] o;
   input [3:0] a;
   input [3:0] b;

   wire [size-1:0] foo = 0;

   blankport foo1 (.o(o[1:0]), .a(a[1:0]), .b(b[1:0]));
   blankport foo2 (o[3:2], , a[3:2], b[3:2]);

   blankport bar [1:0] (o[7:4], , a[3:2], b);

endmodule


/*+VL

module make_tests () ;

   wire [100:0] w;
   wire a;

   blankport_test #(4) test (4'b0, 4'b0, 4'b0);

endmodule

*/


