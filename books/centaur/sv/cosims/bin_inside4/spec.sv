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

  wire [3:0] 			 lhs1;
  wire signed [2:0] 		 lhs2;
  wire [1:0] 			 lhs3;
  wire signed 			 lhs4;

  assign { lhs4, lhs3, lhs2, lhs1 } = in;

  // Notes:
  //
  //   NCV-only because VCS doesn't seem to like [$:$] ranges.
  //
  //   NCV seems to have a bug with one-bit signed wires.  Reported
  //   2015-12-21.  If it is fixed, we can put ot4 back in.

  wire ot1 = lhs1 inside { [$:$] };
  wire ot2 = lhs2 inside { [$:$] };
  wire ot3 = lhs3 inside { [$:$] };
  wire ot4 = lhs4 inside { [$:$] };

  assign out = { // ot4,  // Commented out due to work around NCV bug.
                 ot3, ot2, ot1 };

endmodule
