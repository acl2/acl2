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


// flopcode2 tests

// This is identical to the original flopcode tests, except that we replace
// posedge everywhere with negedge.

module f1 (q, d, clk);

  parameter size = 1;

  output [size-1:0] q;
  input [size-1:0]  d;
  input 	    clk;

  reg [size-1:0]    q;

  always @(negedge clk)
    q <= d;

endmodule


module f2 (q, d, clk);

  parameter size = 1;

  output [size-1:0] q;
  input [size-1:0]  d;
  input 	    clk;

  reg [size-1:0]    q;

  always @(negedge clk)
    begin
      q <= d;
      q <= d;
    end

endmodule


module f3 (q, d, clk);

  parameter size = 1;

  output [size-1:0] q;
  input [size-1:0]  d;
  input 	    clk;

  reg [size-1:0]    q;

  always @(negedge clk)
    begin
      q <= d;
      q <= d;
      q <= {size {1'b0}};
      q <= {size {1'b1}};
      q <= d;
    end

endmodule


module f4 (q, d1, d2, d3, clk);

  parameter size = 1;

  output [size-1:0] q;
  input [size-1:0]  d1, d2, d3;
  input 	    clk;

  reg [size-1:0]    q;

  always @(negedge clk)
    begin
      q <= d1;
      q <= d2;
      q <= d3;
    end

endmodule


module f5 (q, d1, d2, d3, clk);

  parameter size = 1;

  output [size-1:0] q;
  input [size-1:0]  d1, d2, d3;
  input 	    clk;

  reg [size-1:0]    q;

  always @(negedge clk)
    begin
      q <= d1;
      q <= d2;
      q <= d3;
      q <= d1;
      q <= d2;
      q <= d3;
    end

endmodule


// G modules: flops with various conditional and unconditional always assignments.

module g1 (q, d, en, clk);

  parameter size = 1;

  output [size-1:0] q;
  input [size-1:0]  d;
  input 	    clk, en;

  reg [size-1:0]    q;

  always @(negedge clk)
    begin
      if (en) q <= d;
    end

endmodule


module g2 (q, d1, d2, en, clk);

  parameter size = 1;

  output [size-1:0] q;
  input [size-1:0]  d1, d2;
  input 	    clk, en;

  reg [size-1:0]    q;

  always @(negedge clk)
    begin
      if (en) q <= d1;
      if (en) q <= d2;
    end

endmodule


module g3 (q, d1, d2, en, clk);

  parameter size = 1;

  output [size-1:0] q;
  input [size-1:0]  d1, d2;
  input 	    clk, en;

  reg [size-1:0]    q;

  always @(negedge clk)
    begin
      q <= d1;
      if (en) q <= d2;
    end

endmodule


module g4 (q, d1, d2, en, clk);

  parameter size = 1;

  output [size-1:0] q;
  input [size-1:0]  d1, d2;
  input 	    clk, en;

  reg [size-1:0]    q;

  always @(negedge clk)
    begin
      if (en) q <= d1;
      q <= d2;
    end

endmodule


module g5 (q, d1, d2, en, clk);

  parameter size = 1;

  output [size-1:0] q;
  input [size-1:0]  d1, d2;
  input 	    clk, en;

  reg [size-1:0]    q;

  always @(negedge clk)
    begin
      q <= d1;
      if (en) q <= d1;
      if (!en) q <= d2;
    end

endmodule


module g6 (q, d1, d2, en, clk);

  parameter size = 1;

  output [size-1:0] q;
  input [size-1:0]  d1, d2;
  input 	    clk, en;

  reg [size-1:0]    q;

  always @(negedge clk)
    begin
      q <= d1;
      if (en) q <= d1;
      if (!en) q <= d2;
      q <= d2;
    end

endmodule



/*+VL

module make_tests();

  wire  q, d1, d2, d3, en, clk;

  f1 f1spec (q, d1, clk);
  f2 f2spec (q, d1, clk);
  f3 f3spec (q, d1, clk);
  f4 f4spec (q, d1, d2, d3, clk);
  f5 f5spec (q, d1, d2, d3, clk);

  g1 g1spec (q, d1, en, clk);
  g2 g2spec (q, d1, d2, en, clk);
  g3 g3spec (q, d1, d2, en, clk);
  g4 g4spec (q, d1, d2, en, clk);
  g5 g5spec (q, d1, d2, en, clk);
  g6 g6spec (q, d1, d2, en, clk);


 wire [3:0] q4, d4;

  f1 #(4) f1spec4 (q4, d4, clk);
  f2 #(4) f2spec4 (q4, d4, clk);
  f3 #(4) f3spec4 (q4, d4, clk);
  f4 #(4) f4spec4 (q4, d4, d4, d4, clk);
  f5 #(4) f5spec4 (q4, d4, d4, d4, clk);

  g1 #(4) g1spec4 (q4, d4, en, clk);
  g2 #(4) g2spec4 (q4, d4, d4, en, clk);
  g3 #(4) g3spec4 (q4, d4, d4, en, clk);
  g4 #(4) g4spec4 (q4, d4, d4, en, clk);
  g5 #(4) g5spec4 (q4, d4, d4, en, clk);
  g6 #(4) g6spec4 (q4, d4, d4, en, clk);

endmodule

*/
