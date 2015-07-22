// Centaur Hardware Verification Tutorial for ESIM/VL2014
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


// counter.v
//
// This is a simple base-10 counter.

module counter (
  output [3:0] out,
  input reset,      // reset to zero
  input inc,        // want to increment?
  input clk
);

wire [3:0] outPlus = (out == 4'd9) ? 4'b0 : out + 4'b1;

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
