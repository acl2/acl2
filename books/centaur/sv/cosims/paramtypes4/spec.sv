// Another SV parameter type cosim test
// Copyright (C) 2016 Apple, Inc.
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
// Original author: Jared Davis

// Tests of top-level explicit value parameter handling for unpacked arrays
// with test cases based on paramtypes/spec.sv

// These are the same as paramtypes3 except we drop the explicit "logic" type
// to see what happens (because we aren't sure if parameters with unpacked
// array dimensions are supposed to get treated like implicitly typed
// parameters or not).

parameter  [5:0] a1[1] = '{3'b100 << 1'b1};
parameter  [5:0] a2[1] = '{3'b100 << 1};
parameter  [5:0] a3[1] = '{3'sb100 << 1};
parameter  signed [5:0] a4[1] = '{3'b100 << 1};
parameter  signed [5:0] a5[1] = '{3'sb100 << 1};

parameter  signed [5:0] b1[1] = '{3'sb 110 >>> 1'sb1};
parameter  signed [5:0] b2[1] = '{3'sb 110 >>> 1};
parameter  signed [5:0] b3[1] = '{6'b 111100 >>> 1'sb1};
parameter  signed [5:0] b4[1] = '{6'b 111100 >>> 1};
parameter  signed [5:0] b5[1] = '{3'sb 110};
parameter  signed [5:0] b6[1] = '{3'b 110};

parameter  [5:0] c1[1] = '{3'sb 110 >>> 1'sb1};
parameter  [5:0] c2[1] = '{3'sb 110 >>> 1};
parameter  [5:0] c3[1] = '{6'b 111100 >>> 1'sb1};
parameter  [5:0] c4[1] = '{6'b 111100 >>> 1};

module spec (input logic [127:0] in,
	     output logic [127:0] out);

   assign out = { c4[0], c3[0], c2[0], c1[0],
		  b6[0], b5[0], b4[0], b3[0], b2[0], b1[0],
		  a5[0], a4[0], a3[0], a2[0], a1[0] };

endmodule

