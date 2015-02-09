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

   `ifdef SYSTEM_VERILOG_MODE
   wire spec_wildeq1 ;
   wire spec_wildeq2 ;
   wire spec_wildeq3 ;
   wire spec_wildeq4 ;
   wire spec_wildneq1 ;
   wire spec_wildneq2 ;
   wire spec_wildneq3 ;
   wire spec_wildneq4 ;
   `endif

   unary_ops_test #(`SIZE) spec (

     `ifdef SYSTEM_VERILOG_MODE
     .out_wildeq1(spec_wildeq1),
     .out_wildeq2(spec_wildeq2),
     .out_wildeq3(spec_wildeq3),
     .out_wildeq4(spec_wildeq4),
     .out_wildneq1(spec_wildneq1),
     .out_wildneq2(spec_wildneq2),
     .out_wildneq3(spec_wildneq3),
     .out_wildneq4(spec_wildneq4),
     `endif

     .in(src),
     .out_bitnot(spec_bitnot),
     .out_plus(spec_plus),
     .out_minus(spec_minus),
     .out_lognot(spec_lognot),
     .out_and(spec_and),
     .out_nand(spec_nand),
     .out_or(spec_or),
     .out_nor(spec_nor),
     .out_xor(spec_xor),
     .out_xnor(spec_xnor),
     .out_xnor2(spec_xnor2),
     .out_true(spec_true),
     .out_false(spec_false),
     .out_x(spec_x),
     .out_z(spec_z)
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

  `ifdef SYSTEM_VERILOG_MODE
   wire impl_wildeq1 ;
   wire impl_wildeq2 ;
   wire impl_wildeq3 ;
   wire impl_wildeq4 ;
   wire impl_wildneq1 ;
   wire impl_wildneq2 ;
   wire impl_wildneq3 ;
   wire impl_wildneq4 ;
  `endif

   `MODNAME_SIZE impl (

     `ifdef SYSTEM_VERILOG_MODE
     .out_wildeq1(impl_wildeq1),
     .out_wildeq2(impl_wildeq2),
     .out_wildeq3(impl_wildeq3),
     .out_wildeq4(impl_wildeq4),
     .out_wildneq1(impl_wildneq1),
     .out_wildneq2(impl_wildneq2),
     .out_wildneq3(impl_wildneq3),
     .out_wildneq4(impl_wildneq4),
     `endif

     .in(src),
     .out_bitnot(impl_bitnot),
     .out_plus(impl_plus),
     .out_minus(impl_minus),
     .out_lognot(impl_lognot),
     .out_and(impl_and),
     .out_nand(impl_nand),
     .out_or(impl_or),
     .out_nor(impl_nor),
     .out_xor(impl_xor),
     .out_xnor(impl_xnor),
     .out_xnor2(impl_xnor2),
     .out_true(impl_true),
     .out_false(impl_false),
     .out_x(impl_x),
     .out_z(impl_z)
   );


 // Horrible hack.  VCS doesn't seem to implement the wildcard equalities correctly
 // when the left hand side has X or Z bits.

`ifndef VL_SYSTEST_VCS
  wire 	allow_wild_mismatch = 0;

`else

  reg 	src_has_some_x;
  integer i;

  always @(src)
  begin
    src_has_some_x = 0;
    for(i = 0;i < `SIZE;i = i + 1)
       if (src[i] === 1'bx || src[i] === 1'bz)
          src_has_some_x = 1;
  end

  wire allow_wild_mismatch = src_has_some_x;
`endif


   always @(posedge chk)
   begin

// You can leave this display statement in to make sure the tests are getting run,
// but it starts to produce too much output around size 7 or 8.
//
//      $display("Checking unary ops for size = %0d, src = %b", `SIZE, src);

      if (spec_bitnot !== impl_bitnot)
	$display("compare_unary_ops fail (bitnot): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_bitnot, impl_bitnot);

`ifndef VL_SYSTEST_VCS

      // NCVerilog implements unary "+A" as if it were "A + 0" -- that is,
      // if there are any X/Z bits in A, then the whole result is X.

      // VCS implements unary "+A" as if it were just "A" -- that is, no
      // such X coercion occurs.

      // VL follows NCV's approach, so we suppress this check on VCS because
      // otherwise it will fail on VCS.

      if (spec_plus !== impl_plus)
	$display("compare_unary_ops fail (plus): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_plus, impl_plus);

`endif

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


     `ifdef SYSTEM_VERILOG_MODE

       if (!allow_wild_mismatch && (spec_wildeq1 !== impl_wildeq1))
         $display("compare_unary_ops fail (wildeq1): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_wildeq1, impl_wildeq1);

       if (!allow_wild_mismatch && (spec_wildeq2 !== impl_wildeq2))
 	$display("compare_unary_ops fail (wildeq2): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_wildeq2, impl_wildeq2);

       if (!allow_wild_mismatch && (spec_wildeq3 !== impl_wildeq3))
	$display("compare_unary_ops fail (wildeq3): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_wildeq3, impl_wildeq3);

       if (!allow_wild_mismatch && (spec_wildeq4 !== impl_wildeq4))
	$display("compare_unary_ops fail (wildeq4): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_wildeq4, impl_wildeq4);

       if (!allow_wild_mismatch && (spec_wildneq1 !== impl_wildneq1))
	$display("compare_unary_ops fail (wildneq1): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_wildneq1, impl_wildneq1);

       if (!allow_wild_mismatch && (spec_wildneq2 !== impl_wildneq2))
	$display("compare_unary_ops fail (wildneq2): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_wildneq2, impl_wildneq2);

       if (!allow_wild_mismatch && (spec_wildneq3 !== impl_wildneq3))
	$display("compare_unary_ops fail (wildneq3): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_wildneq3, impl_wildneq3);

       if (!allow_wild_mismatch && (spec_wildneq4 !== impl_wildneq4))
	$display("compare_unary_ops fail (wildneq4): size = %0d, src = %b, spec = %b, impl = %b",
	  `SIZE, src, spec_wildneq4, impl_wildneq4);

     `endif

   end

endmodule
