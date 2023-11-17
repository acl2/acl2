//SV - Symbolic Vector Hardware Analysis Framework
//Copyright (C) 2023 Intel Corporation
//
//License: (An MIT/X11-style license)
//
//  Permission is hereby granted, free of charge, to any person obtaining a
//  copy of this software and associated documentation files (the "Software"),
//  to deal in the Software without restriction, including without limitation
//  the rights to use, copy, modify, merge, publish, distribute, sublicense,
//  and/or sell copies of the Software, and to permit persons to whom the
//  Software is furnished to do so, subject to the following conditions:
//
//  The above copyright notice and this permission notice shall be included in
//  all copies or substantial portions of the Software.
//
//  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//  FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//  DEALINGS IN THE SOFTWARE.
//
//Original author: Sol Swords <sol.swords@intel.com>


module counter (input clk, input inc, input reset, output [3:0] sum);

logic [3:0] sum_next;
logic [3:0] sum1;
logic [3:0] sum1_next_tmp;
logic [3:0] sum1_next;

always @(posedge clk) begin
   sum <= sum_next;
   sum1 <= sum1_next;
end

always_comb begin
   if (reset) begin
     sum1_next = 0;
     sum_next = 0;
   end else begin
     sum1_next_tmp = (sum == 4'd11 ? 0 : sum) + inc;
     sum1_next = (sum1_next_tmp == 4'd11) ? 0 : sum1_next_tmp;
     sum_next = sum1 + inc;
   end
end

endmodule
