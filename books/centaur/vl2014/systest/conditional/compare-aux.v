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


// Preprocessor hacking for ?: comparison modules

module `COMPARE_NAME (select, src1, src2, chk);

   input select;
   input [`SIZE-1:0] src1 ;
   input [`SIZE-1:0] src2 ;
   input chk;

   wire [`SIZE-1:0] spec_out1 ;
   wire [`SIZE-1:0] spec_out2 ;
   wire [`SIZE-1:0] spec_out3 ;

   wire [`SIZE-1:0] impl_out1 ;
   wire [`SIZE-1:0] impl_out2 ;
   wire [`SIZE-1:0] impl_out3 ;

   conditional_ops_test #(`SIZE) spec (
     .select     (select),
     .src1       (src1),
     .src2       (src2),
     .out1       (spec_out1),
     .out2       (spec_out2),
     .out3       (spec_out3)
   );

   // Our mux implementations only produce conservative approximations, and may
   // produce Xes where other results are expected.

    wire [`SIZE-1:0] spec_out1_zfix ;
    wire [`SIZE-1:0] spec_out2_zfix ;
    wire [`SIZE-1:0] spec_out3_zfix ;

    convert_z_to_x #(`SIZE) make_spec_out1_zfix (spec_out1_zfix, spec_out1);
    convert_z_to_x #(`SIZE) make_spec_out2_zfix (spec_out2_zfix, spec_out2);
    convert_z_to_x #(`SIZE) make_spec_out3_zfix (spec_out3_zfix, spec_out3);

   `MODNAME_SIZE impl (
     .select     (select),
     .src1       (src1),
     .src2       (src2),
     .out1       (impl_out1),
     .out2       (impl_out2),
     .out3       (impl_out3)
   );


   always @(posedge chk)
   begin

    if (`SIZE == 1)
    begin

      $display("(%b %b %b) --> (%b vs %b: %s)  (%b vs %b: %s)  (%b vs %b: %s)",
                select,
                src1,
                src2,
                spec_out1, impl_out1,

		((spec_out1 === impl_out1) ? "exact"
              : (impl_out1 === 1'bx && spec_out1 === 1'bz) ? "zappr"
	      : (impl_out1 === 1'bx) ? "consr"
	      : "fail"),

                spec_out2, impl_out2,
		((spec_out2 === impl_out2) ? "exact"
              : (impl_out2 === 1'bx && spec_out2 === 1'bz) ? "zappr"
	      : (impl_out2 === 1'bx) ? "consr"
	      : "fail"),

                spec_out3, impl_out3,

		((spec_out3 === impl_out3) ? "exact"
              : (impl_out3 === 1'bx && spec_out3 === 1'bz) ? "zappr"
	      : (impl_out3 === 1'bx) ? "consr"
	      : "fail")

	       );

    end


   end

endmodule
