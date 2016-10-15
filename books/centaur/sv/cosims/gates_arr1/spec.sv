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

module spec (input wire [127:0] in,
	     output wire [127:0] out);

  and arr1 [3:0] (out[3:0],  in[3:0], in[7:4]);
  and arr2 [3:0] (out[7:4],  ~in[3:0], ~in[7:4]);

  or arr3 [3:0] (out[11:8],  in[3:0], in[0]);
  or arr4 [3:0] (out[15:12], ~in[3:0], ~in[0]);

  xor arr5 [3:0] (out[19:16],  in[3:0], in[7:4]);
  xor arr6 [3:0] (out[23:20], ~in[3:0], ~in[7:4], in[8]);

  nand arr7 [4] (out[27:24],  in[7:4], in[3:0], in[11:8]);
  nand arr8 [4] (out[31:28], ~in[7:4], ~in[3:0]);

  nor arr9 [0:3] (out[35:32],  in[3:0], in[7:4]);
  nor arr10 [0:3] (out[39:36], ~in[3:0], ~in[7:4]);

  not arr11 [4] (out[43:40], in[3:0] + in[7:4]);
  not arr12 [4] (out[47:44], out[51:48], in[0]);

  buf arr13 [3:0] (out[55:52], in[3:0]);
  buf arr14 [0:3] (out[59:56], out[63:60], in[3:0]);


endmodule // spec
