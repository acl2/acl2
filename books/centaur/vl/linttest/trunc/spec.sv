// VL Verilog Toolkit
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

module m0;

  wire clk;
  wire [3:0] foo;
  wire [2:0] trunc1, trunc2, trunc3, trunc4, trunc5, trunc6, trunc7, trunc8;

  assign trunc1 = foo;
  assign trunc2 = (foo & 4'b0);

  always_comb
  begin
    trunc3 = foo;
    trunc4 = (foo & 4'b0);
  end

  always @(posedge clk)
  begin
    trunc5 <= foo;
    trunc6 <= (foo & 4'b0);
  end

  always_ff @(posedge clk)
  begin
    trunc7 <= foo;
    trunc8 <= (foo & 4'b0);
  end

  function [2:0] truncfun (logic [3:0] i) ;
    logic [2:0] trunc9;
    begin
      trunc9 = i;
      truncfun = i;
    end
  endfunction

  task trunctask (output [2:0] trunc10, input [3:0] i) ;
    logic [2:0] trunc11;
    begin
      trunc10 = i;
      trunc11 = i;
    end
  endtask

  logic [2:0] trunc12, trunc13;

  initial begin
    trunc12 = foo;
    trunc13 = (foo & 4'b0);
  end

  genvar i;
  wire [9:0][2:0] warr;
  generate
    for(i = 0;i < 10;++i) begin
      assign warr[i] = foo;
    end
  endgenerate

endmodule



parameter global_size = 4;

module m1 ;

  wire [3:0] normal1 = 0;
  wire [3:0] normal2 = 15;
  wire [3:0] normal3 = global_size;
  wire [3:0] trunc1 = 16;

endmodule


module m2 ;

   parameter width = 0;

   output [width-1:0] foo0, foo1;
   input [width-1:0] bar;

   assign foo0 = bar;
   assign foo0[width-1:0] = bar[width-1:0];

endmodule

module m3;

   input [32'd4294967295:0] bar ;
   output [32'd4294967295:0] foo ;
   assign bar = foo ;

endmodule


module a0 ;

   wire [3:0] w;

   wire       mod1 = w % 2;  // no warning, compatible with wire range
   wire [1:0] mod2 = w % 3;  // no warning, compatible with wire range
   wire [1:0] mod3 = w % 4;  // no warning, compatible with wire range

   wire       mod4 = w % 3;  // warn because it's bigger than the wire range
   wire       mod5 = w % 4;  // warn because it's bigger than the wire range

endmodule

module a1;

   wire [3:0] w;

   wire [3:0] xx0 = {3{1'b0}}; // no warning, fits
   wire [3:0] xx1 = {4{1'b0}}; // no warning, fits
   wire [3:0] xx2 = {5{1'b0}}; // no warning, still getting all zeroes

   wire [3:0] yy0 = {3{1'b1}}; // warn, extension
   wire [3:0] yy1 = {4{1'b1}}; // no warning, correct
   wire [3:0] yy2 = {5{1'b1}}; // warn, truncating a 1

   wire [3:0] zz0 = $countones(w);  // no warning, integer-valued system function
   wire [3:0] zz1 = $bits(w);       // no warning, integer-valued system function
   wire [2:0] zz2 = $unsigned(w);   // warn, wrong size

endmodule
