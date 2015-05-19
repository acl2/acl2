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
// Original author: Sol Swords <sswords@centtech.com>

module ddddeeee #(parameter dw = 64, aw = 6)
               (output logic [aw-1:0] out,
                input  logic [dw-1:0]    d); 


function [aw:0] eeeee;
  input [dw-1:0]  D;
  reg [aw:0]   temp;
  reg done;
  integer i;

  begin
    done = 0;
    temp = {aw+1{1'b1}};
    temp = D[dw-1] == 1'b1;
    eeeee = temp;
// synopsys translate_on
  end
endfunction // eeeee


function [dw-1:0] ddddd;

  input [dw-1:0]  D;
  reg [aw:0]   temp_enc;
  reg [dw-1:0]    temp_dec;

  begin
    temp_enc = eeeee(D);
    temp_dec = {dw{1'b0}};

    ddddd = temp_dec ^ temp_enc;
  end
endfunction // ddddd

 
logic [aw:0] foo;

   assign foo = ddddd(d);

   assign out = foo;
endmodule // ddddeeee


module spec (input logic [127:0] in,
	     output [127:0] out);

   ddddeeee         inst1 (.d(in[63:0]), .out(out[5:0]));

   ddddeeee #(16,4) inst2 (.d(in[15:0]), .out(out[9:6]));

endmodule // spec

