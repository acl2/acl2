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
// Original authors: Jared Davis <jared@centtech.com>
//                   Sol Swords <sswords@centtech.com>

module spec (input logic [127:0] in,
	     output logic [127:0] out);

  wire [3:0] a;
  wire signed [3:0] b;
  assign { a, b } = in;

  wire [3:0] oa1, oa2, oa3, oa4;
  assign oa1 = a <= '1;
  assign oa2 = a + '1;
  assign oa3 = a & '1;
  assign oa4 = a | '1;

  wire [3:0] ob1, ob2, ob3, ob4;
  assign ob1 = b <= '1;
  assign ob2 = b + '1;
  assign ob3 = b & '1;
  assign ob4 = b | '1;

  wire [4:0] oc1, oc2, oc3, oc4;
  assign oc1 = a <= '1;
  assign oc2 = a + '1;
  assign oc3 = a & '1;
  assign oc4 = a | '1;

  wire [4:0] od1, od2, od3, od4;
  assign od1 = b <= '1;
  assign od2 = b + '1;
  assign od3 = b & '1;
  assign od4 = b | '1;

  wire [4:0] oe1, oe2, oe3, oe4;
  assign oe1 = a == '1;
  assign oe2 = (a + '1) >>> 1;
  assign oe3 = (a & '1) >>> 1;
  assign oe4 = (a | '1) >>> 1;

  wire [4:0] of1, of2, of3, of4;
  assign of1 = b == '1;
  assign of2 = (b + '1) >>> 1;
  assign of3 = (b & '1) >>> 1;
  assign of4 = (b | '1) >>> 1;

  assign out = { of4, of3, of2, of1,
                 oe4, oe3, oe2, oe1,
                 od4, od3, od2, od1,
                 oc4, oc3, oc2, oc1,
                 ob4, ob3, ob2, ob1,
                 oa4, oa3, oa2, oa1 };

endmodule
