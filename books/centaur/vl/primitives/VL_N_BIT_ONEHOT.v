// VL Verilog Toolkit
// Copyright (C) 2008-2011 Centaur Technology
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

module VL_N_BIT_ONEHOT (out, in) ;

// VL_N_BIT_ONEHOT is a Verilog module for one-hot detection.
//
// It drives OUT to:
//
//   1 when IN is definitely one-hot,
//   0 when IN is definitely not one-hot, and
//   X when IN contains X/Z values that make is one-hotness uncertain
//
// Why introduce this as a primitive module at all?  It is hard to write a
// parameterized one-hot detector out of synthesizable components, so we end up
// using a for-loop instead.
//
// VL takes special measures to recognize this module by its name, and will
// replace any instances of, e.g., VL_N_BIT_ONEHOT #(6), with specialized
// versions, e.g., VL_6_BIT_ONEHOT, that is constructed out of synthesizable
// components.

   parameter width = 1;

   input [width-1:0] in;
   output out;

   reg out;

   integer i;
   integer number;

   always @(in)
   begin
      number = 0;
      for(i = 0;i < width; i = i + 1)
          number = number + in[i];
      out = number;
   end

endmodule
