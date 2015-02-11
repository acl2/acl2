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
// Stupid preprocessor hack to introduce a comparison module for some
// particular size.

module `COMPARE_NAME (src1, src2, chk);

   input [`SIZE-1:0] src1 ;
   input [`SIZE-1:0] src2 ;
   input chk;


   wire [`SIZE-1:0] spec_plus ;
   wire [`SIZE-1:0] spec_minus ;
   wire [`SIZE-1:0] spec_shl ;
   wire [`SIZE-1:0] spec_shr ;
   wire [`SIZE-1:0] spec_mult ;
   wire [`SIZE-1:0] spec_bitand ;
   wire [`SIZE-1:0] spec_xor ;
   wire [`SIZE-1:0] spec_xnor1 ;
   wire [`SIZE-1:0] spec_xnor2 ;
   wire [`SIZE-1:0] spec_bitor ;
   wire spec_lt ;
   wire spec_lte ;
   wire spec_gt ;
   wire spec_gte ;
   wire spec_eq ;
   wire spec_neq ;
   wire spec_logand ;
   wire spec_logor ;
   wire spec_ceq ;
   wire spec_cne ;

   wire [`SIZE-1:0] sspec_plus ;
   wire [`SIZE-1:0] sspec_minus ;
   wire [`SIZE-1:0] sspec_shl ;
   wire [`SIZE-1:0] sspec_shr ;
   wire [`SIZE-1:0] sspec_mult ;
   wire [`SIZE-1:0] sspec_bitand ;
   wire [`SIZE-1:0] sspec_xor ;
   wire [`SIZE-1:0] sspec_xnor1 ;
   wire [`SIZE-1:0] sspec_xnor2 ;
   wire [`SIZE-1:0] sspec_bitor ;
   wire sspec_lt ;
   wire sspec_lte ;
   wire sspec_gt ;
   wire sspec_gte ;
   wire sspec_eq ;
   wire sspec_neq ;
   wire sspec_logand ;
   wire sspec_logor ;
   wire sspec_ceq ;
   wire sspec_cne ;


   binary_ops_test #(`SIZE) spec (
     .src1       (src1),
     .src2       (src2),
     .out_plus   (spec_plus),
     .out_minus  (spec_minus),
     .out_shl    (spec_shl),
     .out_shr    (spec_shr),
     .out_mult   (spec_mult),
     .out_bitand (spec_bitand),
     .out_xor    (spec_xor),
     .out_xnor1  (spec_xnor1),
     .out_xnor2  (spec_xnor2),
     .out_bitor  (spec_bitor),
     .out_lt     (spec_lt),
     .out_lte    (spec_lte),
     .out_gt     (spec_gt),
     .out_gte    (spec_gte),
     .out_eq     (spec_eq),
     .out_neq    (spec_neq),
     .out_logand (spec_logand),
     .out_logor  (spec_logor),
     .out_ceq    (spec_ceq),
     .out_cne    (spec_cne),

     .sout_plus   (sspec_plus),
     .sout_minus  (sspec_minus),
     .sout_shl    (sspec_shl),
     .sout_shr    (sspec_shr),
     .sout_mult   (sspec_mult),
     .sout_bitand (sspec_bitand),
     .sout_xor    (sspec_xor),
     .sout_xnor1  (sspec_xnor1),
     .sout_xnor2  (sspec_xnor2),
     .sout_bitor  (sspec_bitor),
     .sout_lt     (sspec_lt),
     .sout_lte    (sspec_lte),
     .sout_gt     (sspec_gt),
     .sout_gte    (sspec_gte),
     .sout_eq     (sspec_eq),
     .sout_neq    (sspec_neq),
     .sout_logand (sspec_logand),
     .sout_logor  (sspec_logor),
     .sout_ceq    (sspec_ceq),
     .sout_cne    (sspec_cne)

   );

   // Our shifters only produces a conservative approximation, and converts
   // Z bits into X bits.
   wire [`SIZE-1:0] spec_shl_zfix;
   wire [`SIZE-1:0] spec_shr_zfix;
   convert_z_to_x #(`SIZE) make_spec_shl_zfix (spec_shl_zfix, spec_shl);
   convert_z_to_x #(`SIZE) make_spec_shr_zfix (spec_shr_zfix, spec_shr);

   wire [`SIZE-1:0] impl_plus ;
   wire [`SIZE-1:0] impl_minus ;
   wire [`SIZE-1:0] impl_shl ;
   wire [`SIZE-1:0] impl_shr ;
   wire [`SIZE-1:0] impl_mult ;
   wire [`SIZE-1:0] impl_bitand ;
   wire [`SIZE-1:0] impl_xor ;
   wire [`SIZE-1:0] impl_xnor1 ;
   wire [`SIZE-1:0] impl_xnor2 ;
   wire [`SIZE-1:0] impl_bitor ;
   wire impl_lt ;
   wire impl_lte ;
   wire impl_gt ;
   wire impl_gte ;
   wire impl_eq ;
   wire impl_neq ;
   wire impl_logand ;
   wire impl_logor ;
   wire impl_ceq ;
   wire impl_cne ;

   wire [`SIZE-1:0] simpl_plus ;
   wire [`SIZE-1:0] simpl_minus ;
   wire [`SIZE-1:0] simpl_shl ;
   wire [`SIZE-1:0] simpl_shr ;
   wire [`SIZE-1:0] simpl_mult ;
   wire [`SIZE-1:0] simpl_bitand ;
   wire [`SIZE-1:0] simpl_xor ;
   wire [`SIZE-1:0] simpl_xnor1 ;
   wire [`SIZE-1:0] simpl_xnor2 ;
   wire [`SIZE-1:0] simpl_bitor ;
   wire simpl_lt ;
   wire simpl_lte ;
   wire simpl_gt ;
   wire simpl_gte ;
   wire simpl_eq ;
   wire simpl_neq ;
   wire simpl_logand ;
   wire simpl_logor ;
   wire simpl_ceq ;
   wire simpl_cne ;


   wire [`SIZE-1:0] sspec_shl_zfix;
   wire [`SIZE-1:0] sspec_shr_zfix;
   convert_z_to_x #(`SIZE) make_sspec_shl_zfix (sspec_shl_zfix, sspec_shl);
   convert_z_to_x #(`SIZE) make_sspec_shr_zfix (sspec_shr_zfix, sspec_shr);


   `MODNAME_SIZE impl (
     .src1       (src1),
     .src2       (src2),
     .out_plus   (impl_plus),
     .out_minus  (impl_minus),
     .out_shl    (impl_shl),
     .out_shr    (impl_shr),
     .out_mult   (impl_mult),
     .out_bitand (impl_bitand),
     .out_xor    (impl_xor),
     .out_xnor1  (impl_xnor1),
     .out_xnor2  (impl_xnor2),
     .out_bitor  (impl_bitor),
     .out_lt     (impl_lt),
     .out_lte    (impl_lte),
     .out_gt     (impl_gt),
     .out_gte    (impl_gte),
     .out_eq     (impl_eq),
     .out_neq    (impl_neq),
     .out_logand (impl_logand),
     .out_logor  (impl_logor),
     .out_ceq    (impl_ceq),
     .out_cne    (impl_cne),

     .sout_plus   (simpl_plus),
     .sout_minus  (simpl_minus),
     .sout_shl    (simpl_shl),
     .sout_shr    (simpl_shr),
     .sout_mult   (simpl_mult),
     .sout_bitand (simpl_bitand),
     .sout_xor    (simpl_xor),
     .sout_xnor1  (simpl_xnor1),
     .sout_xnor2  (simpl_xnor2),
     .sout_bitor  (simpl_bitor),
     .sout_lt     (simpl_lt),
     .sout_lte    (simpl_lte),
     .sout_gt     (simpl_gt),
     .sout_gte    (simpl_gte),
     .sout_eq     (simpl_eq),
     .sout_neq    (simpl_neq),
     .sout_logand (simpl_logand),
     .sout_logor  (simpl_logor),
     .sout_ceq    (simpl_ceq),
     .sout_cne    (simpl_cne)

   );


   always @(posedge chk)
   begin

//      $display("Checking binary ops for size = %0d, src1 = %b, src2 = %b", `SIZE, src1, src2);

      if (spec_plus !== impl_plus)
	$display("compare_binary_ops fail (  plus): size = %0d, src1 = %b, src2 = %b, spec = %b, impl = %b",
	  `SIZE, src1, src2, spec_plus, impl_plus);

      if (spec_minus !== impl_minus)
	$display("compare_binary_ops fail ( minus): size = %0d, src1 = %b, src2 = %b, spec = %b, impl = %b",
	  `SIZE, src1, src2, spec_minus, impl_minus);

      if (spec_shl_zfix !== impl_shl)
	$display("compare_binary_ops fail (   shl): size = %0d, src1 = %b, src2 = %b, spec = %b, impl = %b",
	  `SIZE, src1, src2, spec_shl_zfix, impl_shl);

      if (spec_shr_zfix !== impl_shr)
	$display("compare_binary_ops fail (   shr): size = %0d, src1 = %b, src2 = %b, spec = %b, impl = %b",
	  `SIZE, src1, src2, spec_shr_zfix, impl_shr);

      if (spec_mult !== impl_mult)
        $display("compare_binary_ops fail (  mult): size = %0d, src1 = %b, src2 = %b, spec = %b, impl = %b",
	  `SIZE, src1, src2, spec_mult, impl_mult);

      if (spec_bitand !== impl_bitand)
	$display("compare_binary_ops fail (bitand): size = %0d, src1 = %b, src2 = %b, spec = %b, impl = %b",
	  `SIZE, src1, src2, spec_bitand, impl_bitand);

      if (spec_xor !== impl_xor)
	$display("compare_binary_ops fail (   xor): size = %0d, src1 = %b, src2 = %b, spec = %b, impl = %b",
	  `SIZE, src1, src2, spec_xor, impl_xor);

      if (spec_xnor1 !== impl_xnor1)
	$display("compare_binary_ops fail ( xnor1): size = %0d, src1 = %b, src2 = %b, spec = %b, impl = %b",
	  `SIZE, src1, src2, spec_xnor1, impl_xnor1);

      if (spec_xnor2 !== impl_xnor2)
	$display("compare_binary_ops fail ( xnor2): size = %0d, src1 = %b, src2 = %b, spec = %b, impl = %b",
	  `SIZE, src1, src2, spec_xnor2, impl_xnor2);

      if (spec_bitor !== impl_bitor)
	$display("compare_binary_ops fail ( bitor): size = %0d, src1 = %b, src2 = %b, spec = %b, impl = %b",
	  `SIZE, src1, src2, spec_bitor, impl_bitor);

      if (spec_lt !== impl_lt)
	$display("compare_binary_ops fail (    lt): size = %0d, src1 = %b, src2 = %b, spec = %b, impl = %b",
	  `SIZE, src1, src2, spec_lt, impl_lt);

      if (spec_lte !== impl_lte)
	$display("compare_binary_ops fail (   lte): size = %0d, src1 = %b, src2 = %b, spec = %b, impl = %b",
	  `SIZE, src1, src2, spec_lte, impl_lte);

      if (spec_gt !== impl_gt)
	$display("compare_binary_ops fail (    gt): size = %0d, src1 = %b, src2 = %b, spec = %b, impl = %b",
	  `SIZE, src1, src2, spec_gt, impl_gt);

      if (spec_gte !== impl_gte)
	$display("compare_binary_ops fail (   gte): size = %0d, src1 = %b, src2 = %b, spec = %b, impl = %b",
	  `SIZE, src1, src2, spec_gte, impl_gte);

      if (spec_eq !== impl_eq)
	$display("compare_binary_ops fail (    eq): size = %0d, src1 = %b, src2 = %b, spec = %b, impl = %b",
	  `SIZE, src1, src2, spec_eq, impl_eq);

      if (spec_neq !== impl_neq)
	$display("compare_binary_ops fail (   neq): size = %0d, src1 = %b, src2 = %b, spec = %b, impl = %b",
	  `SIZE, src1, src2, spec_neq, impl_neq);

      if (spec_logand !== impl_logand)
	$display("compare_binary_ops fail (logand): size = %0d, src1 = %b, src2 = %b, spec = %b, impl = %b",
	  `SIZE, src1, src2, spec_logand, impl_logand);

      if (spec_logor !== impl_logor)
	$display("compare_binary_ops fail ( logor): size = %0d, src1 = %b, src2 = %b, spec = %b, impl = %b",
	  `SIZE, src1, src2, spec_logor, impl_logor);

      if (spec_ceq !== impl_ceq)
	$display("compare_binary_ops fail (   ceq): size = %0d, src1 = %b, src2 = %b, spec = %b, impl = %b",
	  `SIZE, src1, src2, spec_ceq, impl_ceq);

      if (spec_cne !== impl_cne)
	$display("compare_binary_ops fail (   cne): size = %0d, src1 = %b, src2 = %b, spec = %b, impl = %b",
	  `SIZE, src1, src2, spec_cne, impl_cne);



      if (sspec_plus !== simpl_plus)
	$display("compare_binary_ops signed fail (  plus): size = %0d, src1 = %b, src2 = %b, sspec = %b, simpl = %b",
	  `SIZE, src1, src2, sspec_plus, simpl_plus);

      if (sspec_minus !== simpl_minus)
	$display("compare_binary_ops signed fail ( minus): size = %0d, src1 = %b, src2 = %b, sspec = %b, simpl = %b",
	  `SIZE, src1, src2, sspec_minus, simpl_minus);

      if (sspec_shl_zfix !== simpl_shl)
	$display("compare_binary_ops signed fail (   shl): size = %0d, src1 = %b, src2 = %b, sspec = %b, simpl = %b",
	  `SIZE, src1, src2, sspec_shl_zfix, simpl_shl);

      if (sspec_shr_zfix !== simpl_shr)
	$display("compare_binary_ops signed fail (   shr): size = %0d, src1 = %b, src2 = %b, sspec = %b, simpl = %b",
	  `SIZE, src1, src2, sspec_shr_zfix, simpl_shr);

      if (sspec_mult !== simpl_mult)
        $display("compare_binary_ops signed fail (  mult): size = %0d, src1 = %b, src2 = %b, sspec = %b, simpl = %b",
	  `SIZE, src1, src2, sspec_mult, simpl_mult);

      if (sspec_bitand !== simpl_bitand)
	$display("compare_binary_ops signed fail (bitand): size = %0d, src1 = %b, src2 = %b, sspec = %b, simpl = %b",
	  `SIZE, src1, src2, sspec_bitand, simpl_bitand);

      if (sspec_xor !== simpl_xor)
	$display("compare_binary_ops signed fail (   xor): size = %0d, src1 = %b, src2 = %b, sspec = %b, simpl = %b",
	  `SIZE, src1, src2, sspec_xor, simpl_xor);

      if (sspec_xnor1 !== simpl_xnor1)
	$display("compare_binary_ops signed fail ( xnor1): size = %0d, src1 = %b, src2 = %b, sspec = %b, simpl = %b",
	  `SIZE, src1, src2, sspec_xnor1, simpl_xnor1);

      if (sspec_xnor2 !== simpl_xnor2)
	$display("compare_binary_ops signed fail ( xnor2): size = %0d, src1 = %b, src2 = %b, sspec = %b, simpl = %b",
	  `SIZE, src1, src2, sspec_xnor2, simpl_xnor2);

      if (sspec_bitor !== simpl_bitor)
	$display("compare_binary_ops signed fail ( bitor): size = %0d, src1 = %b, src2 = %b, sspec = %b, simpl = %b",
	  `SIZE, src1, src2, sspec_bitor, simpl_bitor);

      if (sspec_lt !== simpl_lt)
	$display("compare_binary_ops signed fail (    lt): size = %0d, src1 = %b, src2 = %b, sspec = %b, simpl = %b",
	  `SIZE, src1, src2, sspec_lt, simpl_lt);

      if (sspec_lte !== simpl_lte)
	$display("compare_binary_ops signed fail (   lte): size = %0d, src1 = %b, src2 = %b, sspec = %b, simpl = %b",
	  `SIZE, src1, src2, sspec_lte, simpl_lte);

      if (sspec_gt !== simpl_gt)
	$display("compare_binary_ops signed fail (    gt): size = %0d, src1 = %b, src2 = %b, sspec = %b, simpl = %b",
	  `SIZE, src1, src2, sspec_gt, simpl_gt);

      if (sspec_gte !== simpl_gte)
	$display("compare_binary_ops signed fail (   gte): size = %0d, src1 = %b, src2 = %b, sspec = %b, simpl = %b",
	  `SIZE, src1, src2, sspec_gte, simpl_gte);

      if (sspec_eq !== simpl_eq)
	$display("compare_binary_ops signed fail (    eq): size = %0d, src1 = %b, src2 = %b, sspec = %b, simpl = %b",
	  `SIZE, src1, src2, sspec_eq, simpl_eq);

      if (sspec_neq !== simpl_neq)
	$display("compare_binary_ops signed fail (   neq): size = %0d, src1 = %b, src2 = %b, sspec = %b, simpl = %b",
	  `SIZE, src1, src2, sspec_neq, simpl_neq);

      if (sspec_logand !== simpl_logand)
	$display("compare_binary_ops signed fail (logand): size = %0d, src1 = %b, src2 = %b, sspec = %b, simpl = %b",
	  `SIZE, src1, src2, sspec_logand, simpl_logand);

      if (sspec_logor !== simpl_logor)
	$display("compare_binary_ops signed fail ( logor): size = %0d, src1 = %b, src2 = %b, sspec = %b, simpl = %b",
	  `SIZE, src1, src2, sspec_logor, simpl_logor);

      if (sspec_ceq !== simpl_ceq)
	$display("compare_binary_ops signed fail (   ceq): size = %0d, src1 = %b, src2 = %b, sspec = %b, simpl = %b",
	  `SIZE, src1, src2, sspec_ceq, simpl_ceq);

      if (spec_cne !== simpl_cne)
	$display("compare_binary_ops signed fail (   cne): size = %0d, src1 = %b, src2 = %b, spec = %b, simpl = %b",
	  `SIZE, src1, src2, spec_cne, simpl_cne);

   end

endmodule
