// SV - Regression Test
// Copyright (C) 2017, Oracle and/or its affiliates. All rights reserved.
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
// Original authors: Yan Peng <yan.p.peng@oracle.com>
//                   David L. Rager <david.rager@oracle.com>

// latch modelled using non-blocking (parallel) assignment
module latch (input logic in,
              output logic out,
              input wire en);

   always @(en or in) begin
      if(en) begin
         // non-blocking assignment
         out <= in;
      end
   end

endmodule

module spec (input logic [127:0] in,
             output wire [127:0] out);
   reg  latch_out;
   wire latch_in;

   assign en = in[0];
   assign latch_in = in[1];

   latch latch_inst (.in  (latch_in),
                     .out (latch_out),
                     .en  (en));

   assign out = latch_out;

endmodule
