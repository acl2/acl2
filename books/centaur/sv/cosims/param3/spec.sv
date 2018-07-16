// Array parameter test
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

module sub #(parameter [3:0] choices [1:0] = '{5,0})
   (input logic [127:0] in,
    output wire [7:0] out);

   wire [3:0] i1,i0;

   localparam choice1_lsb = choices[1] * 4;
   localparam choice0_lsb = choices[0] * 4;

   assign i1 = in[choice1_lsb +: 4];
   assign i0 = in[choice0_lsb +: 4];

   assign out = {i1,i0};

endmodule

module spec (input logic [127:0] in,
	     output wire [127:0] out);

   sub #(.choices('{1,0})) xx0 (in, out[7:0]);
   sub #(.choices('{3,2})) xx1 (in, out[15:8]);
   sub #(.choices('{8,4})) xx2 (in, out[23:16]);

endmodule

