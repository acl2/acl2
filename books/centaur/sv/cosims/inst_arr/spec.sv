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

module sub1 (output out, input a, input b);

  assign out = a & b;

endmodule


module sub2 (output [1:0] out, input [1:0] a, input [1:0] b);

  assign out = a ^ b;

endmodule


module sub3 (output [2:0] out, input [2:0] in, input b) ;

  assign out = b ? ~in : ^in;

endmodule


module spec (input logic [127:0] in,
	     output wire [127:0] out);

  wire a1;
  wire [1:0] a2;
  wire [2:0] a3;

  wire b1;
  wire [1:0] b2;
  wire [2:0] b3;

  assign { a1, a2, a3, b1, b2, b3 } = in;


  wire oa0;
  wire oa1;
  wire oa2;
  wire oa3;
  wire oa4;

  sub1 mkoa0 (oa0, a1, b1);
  sub1 mkoa1 [0:0] (oa1, a1, b1);
  sub1 mkoa2 [1:0] (oa2, a1, b1);
  sub1 mkoa3 [1:0] (oa3, {a1, a2[0]}, {b1, b2[0]});
  sub1 mkoa4 [2:0] (oa4, {a1, a2}, {b1, b2});

  wire ob0;
  wire ob1;
  wire [1:0] ob2;
  wire [1:0] ob3;
  wire [2:0] ob4;


  sub1 mkob0 (ob0, a1, b1);
  sub1 mkob1 [0:0] (ob1, a1, b1);
  sub1 mkob2 [2] (ob2, a1, b1);
  sub1 mkob3 [1:0] (ob3, {a1, a2[0]}, {b1, b2[0]});
  sub1 mkob4 [0:2] (ob4, {a1, a2}, {b1, b2});



  wire       oc0;
  wire 	     oc1;
  wire [1:0] oc2;
  wire [1:0] oc3;
  wire [1:0] oc4;
  wire [3:0] oc5;
  wire [3:0] oc6;

  sub2 mkoc1 [0:0] ({oc1,oc0}, a2, b2);
  sub2 mkoc2 [1] (oc2, a2, b2);
  sub2 mkoc3 [1:0] (oc3, a2, b2);
  sub2 mkoc4 [0:1] (oc4, a2, {b1,a1});
  sub2 mkoc5 [1:0] (oc5, a2, b2);
  sub2 mkoc6 [1:0] (oc6, {a2,a1,a3[0]}, {b2, b1, b3[0]});


  wire 	     od0, od1, od2;
  wire [2:0] od3, od4, od5;
  wire [5:0] od6, od7;
  wire [8:0] od8, od9;

  sub3 mkod1 [3:3] ({od0, od1, od2}, a3, b1);            // 3, 3, 1
  sub3 mkod3 [1:0] (od3, {a3,b3}, b1);                   // 3, 6, 1 (same output)
  sub3 mkod4 [1:0] (od4, {a3,a3}, b1);                   // 3, 6, 1 (same output)
  sub3 mkod5 [1:0] (od5, {b3,a3}, {b1,a1});              // 3, 6, 2 (same output, diff ins)
  sub3 mkod6 [2] (od6, {a3,b3}, {b1,a1});                // 6, 6, 2 (diff outputs, diff ins)
  sub3 mkod7 [1:0] (od7, a3, {a1,b1});                   // 6, 3, 2
  sub3 mkod8 [2:0] (od8, {b3,a3,a2,a1}, {a1,b1,a2[0]});  // 9, 9, 3
  sub3 mkod9 [3] (od9, a3, b3);                          // 9, 3, 3

  assign out = {
	       od9, od8, od7, od6, od5, od4, od3, od2, od1, od0,
	       oc6, oc5, oc4, oc3, oc2, oc1, oc0,
	       ob4, ob3, ob2, ob1, ob0,
	       oa4, oa3, oa2, oa1, oa0
	       };



endmodule
