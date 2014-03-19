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



// compare-aux.v
//
// Including this file introduces a module that compares:
//
//   "the specification"  unary_ops_test #(N)   spec (...)
//   "the translation"    unary_ops_test$size=N impl (...)
//
// We cannot think of any decent way to actually instantiate the properly sized
// implementation module, so we resort to preprocessor hacks.  In particular,
// before including this file, one must define:
//
//   `SIZE         -- the width for this comparison
//   `MODNAME_SIZE -- the name of the unary_ops_test$size=n module
//   `COMPARE_NAME -- the name for this module, compare_unary_ops_aux_n
//
// See compare.v for how this is done.  The net effect is that we can get
// several instances of this module at different sizes, without having to do a
// lot of copying and pasting.

module `COMPARE_NAME (src, chk);

   input [`SIZE-1:0] src ;

// We transition chk from 0 to 1 whenever we want to check the property.  This
// lets the test-bench control all of the delays, etc.
   input chk;


   wire [`SIZE-1:0] spec_bitnot ;
   wire [`SIZE-1:0] spec_plus ;
   wire [`SIZE-1:0] spec_minus ;

   wire spec_lognot ;
   wire spec_and ;
   wire spec_nand ;
   wire spec_or ;
   wire spec_nor ;
   wire spec_xor ;
   wire spec_xnor ;
   wire spec_xnor2 ;
   wire spec_true ;
   wire spec_false ;
   wire spec_x ;
   wire spec_z ;

   unary_ops_test #(`SIZE) spec (
     src, spec_bitnot, spec_plus, spec_minus,
          spec_lognot, spec_and, spec_nand, spec_or, spec_nor,
          spec_xor, spec_xnor, spec_xnor2, spec_true, spec_false,
          spec_x, spec_z
   );



   wire [`SIZE-1:0] impl_bitnot ;
   wire [`SIZE-1:0] impl_plus ;
   wire [`SIZE-1:0] impl_minus ;
   wire impl_lognot ;
   wire impl_and ;
   wire impl_nand ;
   wire impl_or ;
   wire impl_nor ;
   wire impl_xor ;
   wire impl_xnor ;
   wire impl_xnor2 ;

   `MODNAME_SIZE impl (
     src, impl_bitnot, impl_plus, impl_minus,
          impl_lognot, impl_and, impl_nand, impl_or, impl_nor,
          impl_xor, impl_xnor, impl_xnor2, impl_true, impl_false,
          impl_x, impl_z
   );



   always @(posedge chk)
   begin

// You can leave this display statement in to make sure the tests are getting run,
// but it starts to produce too much output around size 7 or 8.
//
//      $display("Checking unary ops for size = %0d, src = %b", `SIZE, src);

      if (spec_bitnot !== impl_bitnot)
	$display("compare_unary_ops fail (bitnot): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_bitnot, impl_bitnot);

      if (spec_plus !== impl_plus)
	$display("compare_unary_ops fail (plus): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_plus, impl_plus);

      if (spec_minus !== impl_minus)
	$display("compare_unary_ops fail (minus): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_minus, impl_minus);

      if (spec_lognot !== impl_lognot)
	$display("compare_unary_ops fail (lognot): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_lognot, impl_lognot);

      if (spec_and !== impl_and)
	$display("compare_unary_ops fail (   and): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_and, impl_and);

      if (spec_nand !== impl_nand)
	$display("compare_unary_ops fail (  nand): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_nand, impl_nand);

      if (spec_or !== impl_or)
	$display("compare_unary_ops fail (    or): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_or, impl_or);

      if (spec_nor !== impl_nor)
	$display("compare_unary_ops fail (   nor): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_nor, impl_nor);

      if (spec_xor !== impl_xor)
	$display("compare_unary_ops fail (   xor): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_xor, impl_xor);

      if (spec_xnor !== impl_xnor)
	$display("compare_unary_ops fail (  xnor): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_xnor, impl_xnor);

      if (spec_xnor2 !== impl_xnor2)
	$display("compare_unary_ops fail ( xnor2): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_xnor2, impl_xnor2);


      if (spec_true !== impl_true || impl_true !== 1'b1)
	$display("compare_unary_ops fail (  true): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_true, impl_true);

      if (spec_false !== impl_false || impl_false !== 1'b0)
	$display("compare_unary_ops fail ( false): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_false, impl_false);

      if (spec_x !== impl_x || impl_x !== 1'bx)
	$display("compare_unary_ops fail (     x): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_x, impl_x);

      if (spec_z !== impl_z || impl_z !== 1'bz)
	$display("compare_unary_ops fail (     z): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_z, impl_z);

   end

endmodule
