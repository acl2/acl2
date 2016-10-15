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

module spec (input logic [127:0] in,
	     output wire [127:0] out);

  // Similar to gates_wideand

  wire       a1, b1, c1;
  wire [1:0] a2, b2, c2;
  wire [2:0] a3, b3, c3;
  wire [3:0] a4, b4, c4;

  wire signed       sa1, sb1, sc1;
  wire signed [1:0] sa2, sb2, sc2;
  wire signed [2:0] sa3, sb3, sc3;
  wire signed [3:0] sa4, sb4, sc4;

  assign {a1, b1, c1} = in;
  assign {a2, b2, c2} = in;
  assign {a3, b3, c3} = in;
  assign {a4, b4, c4} = in;

  assign {sa1, sb1, sc1} = in;
  assign {sa2, sb2, sc2} = in;
  assign {sa3, sb3, sc3} = in;
  assign {sa4, sb4, sc4} = in;

  wire m1, m2, m3, m4;
  or (m1, a1, b1);
  or (m2, a2, b2, c2);
  or (m3, b3, c3);
  or (m4, a4, b4, c4);

  wire r1, r2, r3, r4;
  or (r1, a1);
  or (r2, a2);
  or (r3, a3);
  or (r4, a4);

  wire sm1, sm2, sm3, sm4;
  or (sm1, sa1, sb1);
  or (sm2, sa2, sb2, sc2);
  or (sm3, sb3, sc3);
  or (sm4, sa4, sb4, sc4);

  wire sr1, sr2, sr3, sr4;
  or (sr1, sa1);
  or (sr2, sa2);
  or (sr3, sa3);
  or (sr4, sa4);

  assign out = { m1, m2, m3, m4,
                 r1, r2, r3, r4,
                 sm1, sm2, sm3, sm4,
                 sr1, sr2, sr3, sr4
                 };

endmodule
