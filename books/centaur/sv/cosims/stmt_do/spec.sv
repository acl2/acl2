// Do-while Loop Cosim Test
// Copyright (C) 2018 Apple, Inc.
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
	     output logic [127:0] out);

   logic [3:0] low;

   always_comb begin : lowbits
      integer i;
      i = 0;

      do begin : loop
         low[i] = in[i];
         ++i;
      end : loop
      while (i < 4);

   end : lowbits


   logic [7:4] high;

   wire [3:0] a = in[3:0];
   wire [3:0] b = in[7:4];

   always_comb begin : highbits
      integer j, k;
      k = 0;
      j = 4;
      do begin : loop
         high[j] = a[k] & b[k];
         k = k + 1;
         j = j + 1;
      end while (j < 8);
   end : highbits


   assign out = {high, low};

endmodule
