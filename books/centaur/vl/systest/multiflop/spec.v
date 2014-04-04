// VL Verilog Toolkit
// Copyright (C) 2008-2014 Centaur Technology
//
// Contact:
//   Centaur Technology Formal Verification Group
//   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
//   http://www.centtech.com/
//
// This program is free software; you can redistribute it and/or modify it under
// the terms of the GNU General Public License as published by the Free Software
// Foundation; either version 2 of the License, or (at your option) any later
// version.  This program is distributed in the hope that it will be useful but
// WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
// more details.  You should have received a copy of the GNU General Public
// License along with this program; if not, write to the Free Software
// Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
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
