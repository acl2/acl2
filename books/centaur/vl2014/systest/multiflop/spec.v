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


// Flops that write to multiple registers

module f1 (q1, q2, d1, d2, clk);

  parameter size = 1;

  output [size-1:0] q1, q2;
  input [size-1:0]  d1, d2;
  input 	    clk;

  reg [size-1:0]    q1, q2;

  always @(posedge clk)
    begin
      q1 <= d1;
      q2 <= d2;
    end

endmodule

module f2 (q1, q2, d1, d2, clk);

  parameter size = 1;

  output [size-1:0] q1, q2;
  input [size-1:0]  d1, d2;
  input 	    clk;

  reg [size-1:0]    q1, q2;

  always @(posedge clk)
    begin
      q1 <= d1;
      q1 <= d1;
      q2 <= d1;
      q2 <= d2;
    end

endmodule

module f3 (q1, q2, d1, d2, clk);

  parameter size = 1;

  output [size-1:0] q1, q2;
  input [size-1:0]  d1, d2;
  input 	    clk;

  reg [size-1:0]    q1, q2;

  // think of d1[0] here as a reset signal.  d2 does nothing.
  always @(posedge clk)
    begin
      q1 <= d1[0] ? {size{1'b0}} : q2;
      q2 <= d1[0] ? {size{1'b1}} : q1;
    end

endmodule



// G modules: flops with various conditional and unconditional always assignments.

module g1 (q1, q2, d1, d2, en, clk);

  parameter size = 1;

  output [size-1:0] q1, q2;
  input [size-1:0]  d1, d2;
  input 	    clk, en;

  reg [size-1:0]    q1, q2;

  always @(posedge clk)
    begin
      if (en) q1 <= d1;
      if (en) q2 <= d2;
    end

endmodule

module g2 (q1, q2, q3, d1, d2, en, clk);

  parameter size = 1;

  output [size-1:0] q1, q2, q3;
  input [size-1:0]  d1, d2;
  input 	    clk, en;

  reg [size-1:0]    q1, q2, q3;

  always @(posedge clk)
    begin
      q1 <= d1;
      if (en) q2 <= q1;
      if (en) q3 <= q2;
    end

endmodule

module g3 (q1, q2, d1, d2, en, clk);

  parameter size = 1;

  output [size-1:0] q1, q2;
  input [size-1:0]  d1, d2;
  input 	    clk, en;

  reg [size-1:0]    q1, q2;

  always @(posedge clk)
    begin
      q1 <= d1;
      q2 <= d2;
      if (en) q1 <= q2;
      if (en) q2 <= q1;
    end

endmodule

module g4 (q1, q2, d1, d2, en, clk);

  parameter size = 1;

  output [size-1:0] q1, q2;
  input [size-1:0]  d1, d2;
  input 	    clk, en;

  reg [size-1:0]    q1, q2;

  always @(posedge clk)
    begin
      if (en) q1 <= d1;
      if (en) q2 <= q1;
      q2 <= d2;
      q1 <= q2;
    end

endmodule

module g5 (q1, q2, d1, d2, en, clk);

  parameter size = 1;

  output [size-1:0] q1, q2;
  input [size-1:0]  d1, d2;
  input 	    clk, en;

  reg [size-1:0]    q1, q2;

  always @(posedge clk)
    begin
      q1 <= d1;
      if (en) q2 <= d2;
      if (!en) q1 <= d1;
    end

endmodule


module g6 (q1, q2, d1, d2, en, clk);

  parameter size = 1;

  output [size-1:0] q1, q2;
  input [size-1:0]  d1, d2;
  input 	    clk, en;

  reg [size-1:0]    q1, q2;

  always @(posedge clk)
    begin
      q1 <= 0;
      q2 <= 1;
      if (en)
	begin
	  q1 <= d1;
	  q2 <= d2;
	end
    end

endmodule



/*+VL

module make_tests();

  wire  q1, q2, q3, d1, d2, d3, en, clk;

  f1 f1spec (q1, q2, d1, d2, clk);
  f2 f2spec (q1, q2, d1, d2, clk);
  f3 f3spec (q1, q2, d1, d2, clk);

  g1 g1spec (q1, q2, d1, d2, en, clk);
  g2 g2spec (q1, q2, q3, d1, d2, en, clk);
  g3 g3spec (q1, q2, d1, d2, en, clk);
  g4 g4spec (q1, q2, d1, d2, en, clk);
  g5 g5spec (q1, q2, d1, d2, en, clk);
  g6 g6spec (q1, q2, d1, d2, en, clk);


 wire [3:0] q4, d4;

  f1 #(4) f1spec4 (q4, q4, d4, d4, clk);
  f2 #(4) f2spec4 (q4, q4, d4, d4, clk);
  f3 #(4) f3spec4 (q4, q4, d4, d4, clk);

  g1 #(4) g1spec4 (q4, q4, d4, d4, en, clk);
  g2 #(4) g2spec4 (q4, q4, q4, d4, d4, en, clk);
  g3 #(4) g3spec4 (q4, q4, d4, d4, en, clk);
  g4 #(4) g4spec4 (q4, q4, d4, d4, en, clk);
  g5 #(4) g5spec4 (q4, q4, d4, d4, en, clk);
  g6 #(4) g6spec4 (q4, q4, d4, d4, en, clk);

endmodule

*/
