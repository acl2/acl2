// Enum Cosim Test
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

module spec (input logic [127:0] in,
	     output wire [127:0] out);

   if (1) begin

      enum { FOO, BAR, BAZ } a, b;    // The parameters should go into the if scope...

      assign a = in[0]   ? FOO
                 : in[1] ? BAR
                 :         BAZ;

      assign b = (a == FOO)   ? BAR
                 : (a == BAR) ? BAZ
                 :              FOO;

      assign out[63:0] = {a,b};

   end

   if (1) begin

      enum { BAZ, FOO, BAR } c, d;    // And hence should not conflict with these ones

      assign c = in[0]   ? FOO
                 : in[1] ? BAR
                 :         BAZ;

      assign d = (c == FOO) ? BAR
                 : (c == BAR) ? BAZ
                 :              FOO;

      assign out[127:64] = {c,d};

   end

endmodule
