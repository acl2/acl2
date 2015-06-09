// SV - Regression Test
// Copyright (C) 2015, Oracle and/or its affiliates. All rights reserved.
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
// Original authors: Andrew Brock <andrew.brock@oracle.com>
//                   David L. Rager <david.rager@oracle.com>

module spec (input logic [127:0] in,
	     output logic [127:0] out);

       reg [3:0] r[3:0];
       wire[1:0] p;
       wire flag;

       assign flag = (in[127] == in[126]);
       assign p = in[125:124];

       assign r[0] = in[63:60];
       assign r[1] = in[59:56];
       assign r[2] = in[55:52];
       assign r[3] = in[51:48];

       assign out[127:8] = 120'b0;

       always_comb begin
         if(flag) begin
           out[7:4] = r[p[1:0]];
         end else begin
           out[7:4] = 4'bxxxx;
         end
       end

       always_comb begin
         if(flag) begin
           out[3:0] = 4'bxxxx;
         end else begin
           // this also fails if "r[p[1:0]]" is replaced with "4'b0000"
           out[3:0] = r[p[1:0]];
         end
       end

endmodule // spec
