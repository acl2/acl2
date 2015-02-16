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

module `COMPARE_NAME (a, b, c, check);

  input [`SIZE-1:0]  a, b, c;
  input 	     check;

  wire [`SIZE-1:0] unary_plus_spec;
  wire [`SIZE-1:0] unary_minus_spec;
  wire unary_lognot_spec;
  wire [`SIZE-1:0] unary_bitnot_spec;
  wire unary_bitand_spec;
  wire unary_nand_spec;
  wire unary_bitor_spec;
  wire unary_nor_spec;
  wire unary_xor_spec;
  wire unary_xnor1_spec;
  wire unary_xnor2_spec;
  wire [`SIZE-1:0] binary_plus_spec;
  wire [`SIZE-1:0] binary_minus_spec;
  wire [`SIZE-1:0] binary_times_spec;
  wire [`SIZE-1:0] binary_div_spec;
  wire [`SIZE-1:0] binary_rem_spec;
  wire binary_eq_spec;
  wire binary_neq_spec;
  wire binary_ceq_spec;
  wire binary_logand_spec;
  wire binary_logor_spec;
  // wire [`SIZE-1:0] binary_power_spec;
  wire binary_lt_spec;
  wire binary_lte_spec;
  wire binary_gt_spec;
  wire binary_gte_spec;
  wire [`SIZE-1:0] binary_bitand_spec;
  wire [`SIZE-1:0] binary_bitor_spec;
  wire [`SIZE-1:0] binary_xor_spec;
  wire [`SIZE-1:0] binary_xnor1_spec;
  wire [`SIZE-1:0] binary_xnor2_spec;
  wire [`SIZE-1:0] binary_shr_spec;
  wire [`SIZE-1:0] binary_shl_spec;
  //wire [`SIZE-1:0] binary_ashr_spec;
  //wire [`SIZE-1:0] binary_ashl_spec;
  wire [`SIZE-1:0] qmark_spec;

  spec #(`SIZE) my_spec (.unary_plus(unary_plus_spec),
			 .unary_minus(unary_minus_spec),
			 .unary_lognot(unary_lognot_spec),
			 .unary_bitnot(unary_bitnot_spec),
			 .unary_bitand(unary_bitand_spec),
			 .unary_nand(unary_nand_spec),
			 .unary_bitor(unary_bitor_spec),
			 .unary_nor(unary_nor_spec),
			 .unary_xor(unary_xor_spec),
			 .unary_xnor1(unary_xnor1_spec),
			 .unary_xnor2(unary_xnor2_spec),
			 .binary_plus(binary_plus_spec),
			 .binary_minus(binary_minus_spec),
			 .binary_times(binary_times_spec),
			 .binary_div(binary_div_spec),
			 .binary_rem(binary_rem_spec),
			 .binary_eq(binary_eq_spec),
			 .binary_neq(binary_neq_spec),
			 .binary_ceq(binary_ceq_spec),
			 .binary_logand(binary_logand_spec),
			 .binary_logor(binary_logor_spec),
			 //.binary_power(binary_power_spec),
			 .binary_lt(binary_lt_spec),
			 .binary_lte(binary_lte_spec),
			 .binary_gt(binary_gt_spec),
			 .binary_gte(binary_gte_spec),
			 .binary_bitand(binary_bitand_spec),
			 .binary_bitor(binary_bitor_spec),
			 .binary_xor(binary_xor_spec),
			 .binary_xnor1(binary_xnor1_spec),
			 .binary_xnor2(binary_xnor2_spec),
			 .binary_shr(binary_shr_spec),
			 .binary_shl(binary_shl_spec),
			 //.binary_ashr(//binary_ashr_spec),
			 //.binary_ashl(//binary_ashl_spec),
			 .qmark(qmark_spec),
			 .a(a),
			 .b(b),
			 .c(c));

  wire [`SIZE-1:0] unary_plus_impl;
  wire [`SIZE-1:0] unary_minus_impl;
  wire unary_lognot_impl;
  wire [`SIZE-1:0] unary_bitnot_impl;
  wire unary_bitand_impl;
  wire unary_nand_impl;
  wire unary_bitor_impl;
  wire unary_nor_impl;
  wire unary_xor_impl;
  wire unary_xnor1_impl;
  wire unary_xnor2_impl;
  wire [`SIZE-1:0] binary_plus_impl;
  wire [`SIZE-1:0] binary_minus_impl;
  wire [`SIZE-1:0] binary_times_impl;
  wire [`SIZE-1:0] binary_div_impl;
  wire [`SIZE-1:0] binary_rem_impl;
  wire binary_eq_impl;
  wire binary_neq_impl;
  wire binary_ceq_impl;
  wire binary_logand_impl;
  wire binary_logor_impl;
  // wire [`SIZE-1:0] binary_power_impl;
  wire binary_lt_impl;
  wire binary_lte_impl;
  wire binary_gt_impl;
  wire binary_gte_impl;
  wire [`SIZE-1:0] binary_bitand_impl;
  wire [`SIZE-1:0] binary_bitor_impl;
  wire [`SIZE-1:0] binary_xor_impl;
  wire [`SIZE-1:0] binary_xnor1_impl;
  wire [`SIZE-1:0] binary_xnor2_impl;
  wire [`SIZE-1:0] binary_shr_impl;
  wire [`SIZE-1:0] binary_shl_impl;
  // wire [`SIZE-1:0] binary_ashr_impl;
  // wire [`SIZE-1:0] binary_ashl_impl;
  wire [`SIZE-1:0] qmark_impl;

  `MODNAME_SIZE my_impl (.unary_plus(unary_plus_impl),
			 .unary_minus(unary_minus_impl),
			 .unary_lognot(unary_lognot_impl),
			 .unary_bitnot(unary_bitnot_impl),
			 .unary_bitand(unary_bitand_impl),
			 .unary_nand(unary_nand_impl),
			 .unary_bitor(unary_bitor_impl),
			 .unary_nor(unary_nor_impl),
			 .unary_xor(unary_xor_impl),
			 .unary_xnor1(unary_xnor1_impl),
			 .unary_xnor2(unary_xnor2_impl),
			 .binary_plus(binary_plus_impl),
			 .binary_minus(binary_minus_impl),
			 .binary_times(binary_times_impl),
			 .binary_div(binary_div_impl),
			 .binary_rem(binary_rem_impl),
			 .binary_eq(binary_eq_impl),
			 .binary_neq(binary_neq_impl),
			 .binary_ceq(binary_ceq_impl),
			 .binary_logand(binary_logand_impl),
			 .binary_logor(binary_logor_impl),
			 //.binary_power(binary_power_impl),
			 .binary_lt(binary_lt_impl),
			 .binary_lte(binary_lte_impl),
			 .binary_gt(binary_gt_impl),
			 .binary_gte(binary_gte_impl),
			 .binary_bitand(binary_bitand_impl),
			 .binary_bitor(binary_bitor_impl),
			 .binary_xor(binary_xor_impl),
			 .binary_xnor1(binary_xnor1_impl),
			 .binary_xnor2(binary_xnor2_impl),
			 .binary_shr(binary_shr_impl),
			 .binary_shl(binary_shl_impl),
			 //.binary_ashr(binary_ashr_impl),
			 //.binary_ashl(binary_ashl_impl),
			 .qmark(qmark_impl),
			 .a(a),
			 .b(b),
			 .c(c));

  wire [`SIZE-1:0] binary_shl_specfix;
  wire [`SIZE-1:0] binary_shr_specfix;
  convert_z_to_x #(`SIZE) fix_shl (binary_shl_specfix, binary_shl_spec);
  convert_z_to_x #(`SIZE) fix_shr (binary_shr_specfix, binary_shr_spec);


  always @(posedge check)
    begin
      //$display("Checking size %0d, a %b, b %b, c %b", `SIZE, a, b, c);

`ifndef VL_SYSTEST_VCS

      // NCVerilog implements unary "+A" as if it were "A + 0" -- that is,
      // if there are any X/Z bits in A, then the whole result is X.

      // VCS implements unary "+A" as if it were just "A" -- that is, no
      // such X coercion occurs.

      // VL follows NCV's approach, so we suppress this check on VCS because
      // otherwise it will fail on VCS.

      if (unary_plus_spec !== unary_plus_impl)
	$display("fail: unary_plus: spec %b, impl %b",
		 unary_plus_spec, unary_plus_impl);
`endif

      if (unary_minus_spec !== unary_minus_impl)
	$display("fail: unary_minus: spec %b, impl %b",
		 unary_minus_spec, unary_minus_impl);

      if (unary_lognot_spec !== unary_lognot_impl)
	$display("fail: unary_lognot: spec %b, impl %b",
		 unary_lognot_spec, unary_lognot_impl);

      if (unary_bitnot_spec !== unary_bitnot_impl)
	$display("fail: unary_bitnot: spec %b, impl %b",
		 unary_bitnot_spec, unary_bitnot_impl);

      if (unary_bitand_spec !== unary_bitand_impl)
	$display("fail: unary_bitand: spec %b, impl %b",
		 unary_bitand_spec, unary_bitand_impl);

      if (unary_nand_spec !== unary_nand_impl)
	$display("fail: unary_nand: spec %b, impl %b",
		 unary_nand_spec, unary_nand_impl);

      if (unary_bitor_spec !== unary_bitor_impl)
	$display("fail: unary_bitor: spec %b, impl %b",
		 unary_bitor_spec, unary_bitor_impl);

      if (unary_nor_spec !== unary_nor_impl)
	$display("fail: unary_nor: spec %b, impl %b",
		 unary_nor_spec, unary_nor_impl);

      if (unary_xor_spec !== unary_xor_impl)
	$display("fail: unary_xor: spec %b, impl %b",
		 unary_xor_spec, unary_xor_impl);

      if (unary_xnor1_spec !== unary_xnor1_impl)
	$display("fail: unary_xnor1: spec %b, impl %b",
		 unary_xnor1_spec, unary_xnor1_impl);

      if (unary_xnor2_spec !== unary_xnor2_impl)
	$display("fail: unary_xnor2: spec %b, impl %b",
		 unary_xnor2_spec, unary_xnor2_impl);

      if (binary_plus_spec !== binary_plus_impl)
	$display("fail: binary_plus: spec %b, impl %b",
		 binary_plus_spec, binary_plus_impl);

      if (binary_minus_spec !== binary_minus_impl)
	$display("fail: binary_minus: spec %b, impl %b",
		 binary_minus_spec, binary_minus_impl);

      if (binary_times_spec !== binary_times_impl)
	$display("fail: binary_times: spec %b, impl %b",
		 binary_times_spec, binary_times_impl);

      if (binary_div_spec !== binary_div_impl)
	$display("fail: binary_div: spec %b, impl %b",
		 binary_div_spec, binary_div_impl);

      if (binary_rem_spec !== binary_rem_impl)
	$display("fail: binary_rem: spec %b, impl %b",
		 binary_rem_spec, binary_rem_impl);

      if (binary_eq_spec !== binary_eq_impl)
	$display("fail: binary_eq: spec %b, impl %b",
		 binary_eq_spec, binary_eq_impl);

      if (binary_neq_spec !== binary_neq_impl)
	$display("fail: binary_neq: spec %b, impl %b",
		 binary_neq_spec, binary_neq_impl);

      if (binary_ceq_spec !== binary_ceq_impl)
	$display("fail: binary_ceq: spec %b, impl %b",
		 binary_ceq_spec, binary_ceq_impl);

      if (binary_logand_spec !== binary_logand_impl)
	$display("fail: binary_logand: spec %b, impl %b",
		 binary_logand_spec, binary_logand_impl);

      if (binary_logor_spec !== binary_logor_impl)
	$display("fail: binary_logor: spec %b, impl %b",
		 binary_logor_spec, binary_logor_impl);

      if (binary_lt_spec !== binary_lt_impl)
	$display("fail: binary_lt: spec %b, impl %b",
		 binary_lt_spec, binary_lt_impl);

      if (binary_lte_spec !== binary_lte_impl)
	$display("fail: binary_lte: spec %b, impl %b",
		 binary_lte_spec, binary_lte_impl);

      if (binary_gt_spec !== binary_gt_impl)
	$display("fail: binary_gt: spec %b, impl %b",
		 binary_gt_spec, binary_gt_impl);

      if (binary_gte_spec !== binary_gte_impl)
	$display("fail: binary_gte: spec %b, impl %b",
		 binary_gte_spec, binary_gte_impl);

      if (binary_bitand_spec !== binary_bitand_impl)
	$display("fail: binary_bitand: spec %b, impl %b",
		 binary_bitand_spec, binary_bitand_impl);

      if (binary_bitor_spec !== binary_bitor_impl)
	$display("fail: binary_bitor: spec %b, impl %b",
		 binary_bitor_spec, binary_bitor_impl);

      if (binary_xor_spec !== binary_xor_impl)
	$display("fail: binary_xor: spec %b, impl %b",
		 binary_xor_spec, binary_xor_impl);

      if (binary_xnor1_spec !== binary_xnor1_impl)
	$display("fail: binary_xnor1: spec %b, impl %b",
		 binary_xnor1_spec, binary_xnor1_impl);

      if (binary_xnor2_spec !== binary_xnor2_impl)
	$display("fail: binary_xnor2: spec %b, impl %b",
		 binary_xnor2_spec, binary_xnor2_impl);

      if (binary_shr_specfix !== binary_shr_impl)
	$display("fail: binary_shr: spec %b, impl %b",
		 binary_shr_spec, binary_shr_impl);

      if (binary_shl_specfix !== binary_shl_impl)
	$display("fail: binary_shl: spec %b, impl %b",
		 binary_shl_spec, binary_shl_impl);

      // if (binary_ashr_spec !== binary_ashr_impl)
      // 	$display("fail: binary_ashr");

      // if (binary_ashl_spec !== binary_ashl_impl)
      // 	$display("fail: binary_ashl");

      if (qmark_spec !== qmark_impl)
	$display("fail: qmark: spec %b, impl %b",
		 qmark_spec, qmark_impl);
    end

endmodule
