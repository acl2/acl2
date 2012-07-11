/*

Centaur Hardware Verification Tutorial
Copyright (C) 2012 Centaur Technology

Contact:
  Centaur Technology Formal Verification Group
  7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
  http://www.centtech.com/

This program is free software; you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free Software
Foundation; either version 2 of the License, or (at your option) any later
version.  This program is distributed in the hope that it will be useful but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
details.  You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software Foundation, Inc.,
51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

Original author: Jared Davis <jared@centtech.com>

*/


// counter.v
//
// This is a simple base-10 counter.

module counter (
  output [3:0] out,
  input reset,      // reset to zero
  input inc,        // want to increment?
  input clk
);

wire [3:0] outPlus = (out == 9) ? 4'b0 : out + 4'b1;

wire [3:0] nextState = reset ? 4'b0
           	     : inc   ? outPlus
                     : out;

myreg #(4) cstate (out, nextState, clk);

endmodule


module myreg (q, d, clk) ;   // Basic register

  parameter width = 1;
  output [width-1:0] q;
  input  [width-1:0] d;
  input  clk;

  reg [width-1:0] q;

  always @(posedge clk)
    q <= d;

endmodule
