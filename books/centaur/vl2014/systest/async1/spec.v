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


// Tests of multi-edge flops, e.g., with asynchronous clears/sets.

// F tests, simple cases.

module f1 (q, d, clk, reset);

  parameter size = 1;

  output [size-1:0] q;
  input [size-1:0]  d;
  input 	    clk;
  input 	    reset;

  reg [size-1:0]    q;

  always @(posedge clk or posedge reset)
    if (reset)
      q <= 0;
    else
      q <= d;

endmodule


module f2 (q, d, clk, set);

  parameter size = 1;

  output [size-1:0] q;
  input [size-1:0]  d;
  input 	    clk;
  input 	    set;

  reg [size-1:0]    q;

  always @(posedge clk or posedge set)
    if (set)
      q <= {size{1'b1}};
    else
      q <= d;

endmodule


module f3 (q, d, clk, resetb);

  parameter size = 1;

  output [size-1:0] q;
  input [size-1:0]  d;
  input 	    clk;
  input 	    resetb;

  reg [size-1:0]    q;

  always @(posedge clk or negedge resetb)
    if (!resetb)
      q <= 0;
    else
      q <= d;

endmodule


module f4 (q, d, clk, resetb);

  parameter size = 1;

  output [size-1:0] q;
  input [size-1:0]  d;
  input 	    clk;
  input 	    resetb;

  reg [size-1:0]    q;

  always @(posedge clk or negedge resetb)
    if ({{{{~(!(~resetb))}}}})
      q <= 0;
    else
      q <= d;

endmodule


module f5 (q, d, clk, reset);

  parameter size = 1;

  output [size-1:0] q;
  input [size-1:0]  d;
  input 	    clk;
  input 	    reset;

  reg [size-1:0]    q;

  always @(posedge clk or posedge reset)
    q <= reset ? 0 : d;

endmodule



module f6 (q, d, clk, resetb);

  parameter size = 1;

  output [size-1:0] q;
  input [size-1:0]  d;
  input 	    clk;
  input 	    resetb;

  reg [size-1:0]    q;

  always @(posedge clk or negedge resetb)
    q <= ~resetb ? 0 : d;

endmodule


/*+VL

module make_tests();

  wire  q1, d1, clk, reset;

  f1 f1spec (q1, d1, clk, reset);
  f2 f2spec (q1, d1, clk, set);
  f3 f3spec (q1, d1, clk, resetb);
  f4 f4spec (q1, d1, clk, resetb);
  f5 f5spec (q1, d1, clk, reset);
  f6 f6spec (q1, d1, clk, resetb);

  wire [3:0] q4, d4;

  f1 #(4) f1spec4 (q4, d4, clk, reset);
  f2 #(4) f2spec4 (q4, d4, clk, set);
  f3 #(4) f3spec4 (q4, d4, clk, resetb);
  f4 #(4) f4spec4 (q4, d4, clk, resetb);
  f5 #(4) f5spec4 (q4, d4, clk, reset);
  f6 #(4) f6spec4 (q4, d4, clk, resetb);

endmodule

*/
