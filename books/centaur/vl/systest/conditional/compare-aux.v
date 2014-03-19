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
