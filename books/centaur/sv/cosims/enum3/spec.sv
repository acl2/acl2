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

  parameter bval = 2;

  typedef enum logic [4:0]
  {
      AA = 0,
      BB = bval,
      CC[0:4] = 4,   // 4,5,6,7,8
      DD,            // 9
      EE[2] = 11,    // 11,12
      FF,            // 13
      GG[2],         // 14,15
      HH[3] = 20,    // 20,21,22,23
      II[0:3]        // 24,25,26,27
  } state_t;

  assign out = { II3, II2, II1, II0,
                 HH2, HH1, HH0,
                 GG1, GG0,
                 FF,
                 EE1, EE0,
                 DD,
                 CC3, CC2, CC1, CC0,
                 BB,
                 AA };

endmodule // spec
