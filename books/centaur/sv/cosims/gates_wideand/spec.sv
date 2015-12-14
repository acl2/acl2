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

  // This looks at what happens when we connect wide wires to a gate instance.
  //
  // Both NCVerilog and VCS cause errors when gate outputs are connected to
  // wide wires.  For example:
  //
  //    wire [1:0] n1, n2, n3, n4;
  //    and (n1, a1, b1, c1);
  //
  // NCVerilog complains about gate outputs being more than 1 bit.
  //
  //      and (n1, a1, b1, c1);
  //           |
  //   ncelab: *E,PCPSBT (./spec.sv,51|8): A primitive 'output' terminal
  //           must be connected to a single bit actual.
  //
  // VCS similarly complains about wide outputs:
  //
  //   Error-[IGOE] Illegal gate output expression
  //   spec.sv, 53
  //     The following expression is illegally connected to gate.
  //     Expression: n1
  //     Source info: and (n1, a1, b1, c1);
  //     The gate connection must be a scalar net or bit-select of vector net.
  //     Please refer Chapter:Gate and switch-level modeling in IEEE standard for
  //     verilog.
  //
  // But both simulators tolerate gate inputs being connected to wide wires.
  // NCVerilog seems to reduction OR the inputs whereas VCS just operates on
  // the least significant bit.  That is, we have:
  //
  //     and(tmp, a[1:0], b[1:0]) --> assign tmp = (|a[1:0]) & (|b[1:0])    // NCV behavior
  //     and(tmp, a[0], b[0])     --> assign tmp = a[0] & b[0]              // VCS behavior
  //
  // For VL/SV we have decided to follow the VCS behavior, but we also want to
  // issue warnings about this case.
  //
  // Note that both NCV and VCS seem to prohibit connecting incorrectly sized
  // wires to gate array instances, so we don't try to check anything like that
  // here.  See also failtest/gates3.v and failtest/gates4.v.

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
  and (m1, a1, b1);
  and (m2, a2, b2, c2);
  and (m3, b3, c3);
  and (m4, a4, b4, c4);

  wire r1, r2, r3, r4;
  and (r1, a1);
  and (r2, a2);
  and (r3, a3);
  and (r4, a4);

  wire sm1, sm2, sm3, sm4;
  and (sm1, sa1, sb1);
  and (sm2, sa2, sb2, sc2);
  and (sm3, sb3, sc3);
  and (sm4, sa4, sb4, sc4);

  wire sr1, sr2, sr3, sr4;
  and (sr1, sa1);
  and (sr2, sa2);
  and (sr3, sa3);
  and (sr4, sa4);

  assign out = { m1, m2, m3, m4,
                 r1, r2, r3, r4,
                 sm1, sm2, sm3, sm4,
                 sr1, sr2, sr3, sr4
                 };



  // So these won't work:

  // and (n2, b2, c2, a2);
  // and (n3, b3, c3);
  // and (n4, a4, b4, c4);

  // wire [2:0] o1, o2, o3, o4;
  // and (o1, a1, b1, c1);
  // and (o2, a1, c2);
  // and (o3, a1, c3);
  // and (o4, a1, b2, c4);

  // wire [3:0] p1, p2, p3, p4;
  // and (p1, a1, b1, c1);
  // and (p2, b2, c2, a1);
  // and (p3, b3, c3, c1);
  // and (p4, b4, c4, b1);

  // wire [4:0] q1, q2, q3, q4;
  // and (q1, a1);
  // and (q2, a2);
  // and (q3, a3);
  // and (q4, a4);


endmodule
