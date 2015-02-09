// Centaur Hardware Verification Tutorial for ESIM/VL2014
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
// Original authors: Sol Swords <sswords@centtech.com>
//                   Jared Davis <jared@centtech.com>

// assumes minusb = - b.
// computes pp = b * (signed(abits[2:1]) + abits[0]).
module boothenc (pp, abits, b, minusb);
  output [17:0] pp;
  input [2:0] abits;
  input [15:0] b;
  input [16:0] minusb;

  wire [16:0] bsign = abits[2] ? minusb : { b[15], b };

   // is it shifted?
  wire shft = abits[0] ~^ abits[1];

   // is it zero? (all abits same)
  wire zro = shft & (abits[2] ~^ abits[1]);

   // result without the shift
  wire [16:0] res1 = zro ? 16'b0 : bsign;

   // final shift
  wire [17:0] pp = shft ? { res1, 1'b0 } : { res1[16], res1 };

endmodule

module boothmul (o, a, b);

  output [31:0] o;
  input [15:0] a, b;

  wire [16:0] minusb = 17'b1 + ~{ b[15], b };

  wire [17:0] pp0;
  wire [17:0] pp1;
  wire [17:0] pp2;
  wire [17:0] pp3;
  wire [17:0] pp4;
  wire [17:0] pp5;
  wire [17:0] pp6;
  wire [17:0] pp7;

  boothenc booth0 (pp0, { a[1:0], 1'b0 }, b, minusb);
  boothenc booth1 (pp1, a[3:1], b, minusb);
  boothenc booth2 (pp2, a[5:3], b, minusb);
  boothenc booth3 (pp3, a[7:5], b, minusb);
  boothenc booth4 (pp4, a[9:7], b, minusb);
  boothenc booth5 (pp5, a[11:9], b, minusb);
  boothenc booth6 (pp6, a[13:11], b, minusb);
  boothenc booth7 (pp7, a[15:13], b, minusb);

  // We originally wrote this just as "assign o = ... + ... + ...", but
  // later, to experiment with alternative strategies, we decided to make
  // the summation order explicit, so that we can better match how the
  // implementation's term is built.
  wire [31:0] s0 = { {14{pp0[17]}}, pp0 };
  wire [31:0] s1 = s0 + { {12{pp1[17]}}, pp1, 2'b0 };
  wire [31:0] s2 = s1 + { {10{pp2[17]}}, pp2, 4'b0 };
  wire [31:0] s3 = s2 + { {8{pp3[17]}}, pp3, 6'b0 };
  wire [31:0] s4 = s3 + { {6{pp4[17]}}, pp4, 8'b0 };
  wire [31:0] s5 = s4 + { {4{pp5[17]}}, pp5, 10'b0 };
  wire [31:0] s6 = s5 + { {2{pp6[17]}}, pp6, 12'b0 };
  wire [31:0] s7 = s6 + { pp7, 14'b0 };

  assign o = s7;

endmodule


