// VL 2014 -- Verilog Toolkit, 2014 Edition
// Copyright (C) 2008-2015 Centaur Technology
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
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
//   THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.
//
// Original author: Jared Davis <jared@centtech.com>

`ifdef SYSTEM_VERILOG_MODE

module comb_test (

src1,
src2,
src3,

out1,
out2,
out3,
out4,
out5

);

  parameter size = 1;

  input [size-1:0] src1;
  input [size-1:0] src2;
  input [size-1:0] src3;

  output [size-1:0] out1;
  output [size-1:0] out2;
  output [size-1:0] out3;
  output [size-1:0] out4;
  output [size-1:0] out5;

  reg [size-1:0]    out1, out2;
  logic [size-1:0]  out3, out4, out5;

  always_comb
    out1 = src1;

  always_comb
    if (src1 < src2)
      out2 = src1;
    else
      out2 = src3;

  wire [2:0] lsbs = {src1[0], src2[0], src3[0]};

  always_comb
  begin
    case(lsbs)
      3'd0: out3 = 7;
      3'd1: out3 = 6;
      3'd2: out3 = 5;
      3'd3: out3 = 4;
      3'd4: out3 = 3;
      3'd5: out3 = 2;
      3'd6: out3 = 1;
      3'd7: out3 = 0;
      default: out3 = {1'bx, 1'b0};
    endcase
  end

  always_comb
    begin
      out4 = src1;
      out5 = src2;
    end

endmodule



/*+VL

module make_tests () ;

 wire [7:0] w;

 comb_test #(1) test1 (w[0:0], w[0:0], w[0:0],
                       w[0:0], w[0:0], w[0:0], w[0:0], w[0:0]);

 comb_test #(2) test2 (w[1:0], w[1:0], w[1:0],
                       w[1:0], w[1:0], w[1:0], w[1:0], w[1:0]);

 comb_test #(3) test3 (w[2:0], w[2:0], w[2:0],
                       w[2:0], w[2:0], w[2:0], w[2:0], w[2:0]);

 comb_test #(4) test4 (w[3:0], w[3:0], w[3:0],
                       w[3:0], w[3:0], w[3:0], w[3:0], w[3:0]);

 comb_test #(5) test5 (w[4:0], w[4:0], w[4:0],
                       w[4:0], w[4:0], w[4:0], w[4:0], w[4:0]);

 comb_test #(6) test6 (w[5:0], w[5:0], w[5:0],
                       w[5:0], w[5:0], w[5:0], w[5:0], w[5:0]);

 comb_test #(7) test7 (w[6:0], w[6:0], w[6:0],
                       w[6:0], w[6:0], w[6:0], w[6:0], w[6:0]);

 comb_test #(8) test8 (w[7:0], w[7:0], w[7:0],
                       w[7:0], w[7:0], w[7:0], w[7:0], w[7:0]);

endmodule

*/


`endif
