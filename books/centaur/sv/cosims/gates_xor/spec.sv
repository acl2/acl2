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

  wire i5, i4, i3, i2, i1;

  assign {i5, i4, i3, i2, i1} = in;

  wire out_xor1, out_xor2, out_xor3, out_xor4, out_xor5, out_xor6;

  xor        (out_xor1, i1);
  xor myxor  (out_xor2, i2);
  xor        (out_xor3, i3, i4);
  xor myxor2 (out_xor4, i4, i5, i3);
  xor        (out_xor5, i1, i2, i3, i4);
  xor myxor3 (out_xor6, i1, i2, i3, i4, i5);

  assign out = {
	       out_xor6, out_xor5, out_xor4, out_xor3, out_xor2, out_xor1
	       };

endmodule // spec
