// SV - Symbolic Vector Hardware Analysis Framework
// Copyright (C) 2014-2015 Centaur Technology
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
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.
//
// Original author: Jared Davis <jared@centtech.com>

module spec (input logic [127:0] in,
	     output wire [127:0] out);

  wire [3:0] 			 lhs1;
  wire signed [2:0] 		 lhs2;
  wire [1:0] 			 lhs3;
  wire signed 			 lhs4;

  assign { lhs4, lhs3, lhs2, lhs1 } = in;

  wire 	      oa1 = lhs1 inside { [0:0] };
  wire 	      oa2 = lhs2 inside { [0:0] };
  wire 	      oa3 = lhs3 inside { [0:0] };
  wire 	      oa4 = lhs4 inside { [0:0] };

  wire 	      ob1 = lhs1 inside { [1'b1:1'b1] };
  wire 	      ob2 = lhs2 inside { [1'b1:1'b1] };
  wire 	      ob3 = lhs3 inside { [1'b1:1'b1] };
  wire 	      ob4 = lhs4 inside { [1'b1:1'b1] };

  wire 	      oc1 = lhs1 inside { [1'sb1:1'sb1] };
  wire 	      oc2 = lhs2 inside { [1'sb1:1'sb1] };
  wire 	      oc3 = lhs3 inside { [1'sb1:1'sb1] };
  wire 	      oc4 = lhs4 inside { [1'sb1:1'sb1] };

  wire 	      od1 = lhs1 inside { [lhs1:lhs1] };
  wire 	      od2 = lhs2 inside { [lhs1:lhs1] };
  wire 	      od3 = lhs3 inside { [lhs1:lhs1] };
  wire 	      od4 = lhs4 inside { [lhs1:lhs1] };

  wire 	      oe1 = lhs1 inside { [lhs2:lhs2] };
  wire 	      oe2 = lhs2 inside { [lhs2:lhs2] };
  wire 	      oe3 = lhs3 inside { [lhs2:lhs2] };
  wire 	      oe4 = lhs4 inside { [lhs2:lhs2] };

  wire 	      of1 = lhs1 inside { [lhs3:lhs3] };
  wire 	      of2 = lhs2 inside { [lhs3:lhs3] };
  wire 	      of3 = lhs3 inside { [lhs3:lhs3] };
  wire 	      of4 = lhs4 inside { [lhs3:lhs3] };

  wire 	      og1 = lhs1 inside { [lhs4:lhs4] };
  wire 	      og2 = lhs2 inside { [lhs4:lhs4] };
  wire 	      og3 = lhs3 inside { [lhs4:lhs4] };
  wire 	      og4 = lhs4 inside { [lhs4:lhs4] };

  wire 	      oh1 = lhs1 inside { [lhs1:lhs2] };
  wire 	      oh2 = lhs2 inside { [lhs1:lhs2] };
  wire 	      oh3 = lhs3 inside { [lhs1:lhs2] };
  wire 	      oh4 = lhs4 inside { [lhs1:lhs2] };

  wire 	      oi1 = lhs1 inside { [lhs1:lhs3] };
  wire 	      oi2 = lhs2 inside { [lhs1:lhs3] };
  wire 	      oi3 = lhs3 inside { [lhs1:lhs3] };
  wire 	      oi4 = lhs4 inside { [lhs1:lhs3] };

  wire 	      oj1 = lhs1 inside { [lhs1:lhs4] };
  wire 	      oj2 = lhs2 inside { [lhs1:lhs4] };
  wire 	      oj3 = lhs3 inside { [lhs1:lhs4] };
  wire 	      oj4 = lhs4 inside { [lhs1:lhs4] };

  wire 	      ok1 = lhs1 inside { [lhs2:lhs1] };
  wire 	      ok2 = lhs2 inside { [lhs2:lhs1] };
  wire 	      ok3 = lhs3 inside { [lhs2:lhs1] };
  wire 	      ok4 = lhs4 inside { [lhs2:lhs1] };

  wire 	      ol1 = lhs1 inside { [lhs2:lhs3] };
  wire 	      ol2 = lhs2 inside { [lhs2:lhs3] };
  wire 	      ol3 = lhs3 inside { [lhs2:lhs3] };
  wire 	      ol4 = lhs4 inside { [lhs2:lhs3] };

  wire 	      om1 = lhs1 inside { [lhs2:lhs4] };
  wire 	      om2 = lhs2 inside { [lhs2:lhs4] };
  wire 	      om3 = lhs3 inside { [lhs2:lhs4] };
  wire 	      om4 = lhs4 inside { [lhs2:lhs4] };

  wire 	      on1 = lhs1 inside { [lhs1:lhs2], [lhs3:$] };
  wire 	      on2 = lhs2 inside { [lhs1:lhs2], [lhs3:$] };
  wire 	      on3 = lhs3 inside { [lhs1:lhs2], [lhs3:$] };
  wire 	      on4 = lhs4 inside { [lhs1:lhs2], [lhs3:$] };

  wire 	      oo1 = lhs1 inside { [lhs1:lhs3], [lhs4:$] };
  wire 	      oo2 = lhs2 inside { [lhs1:lhs3], [lhs4:$] };
  wire 	      oo3 = lhs3 inside { [lhs1:lhs3], [lhs4:$] };
  wire 	      oo4 = lhs4 inside { [lhs1:lhs3], [lhs4:$] };

  wire 	      op1 = lhs1 inside { [lhs2:lhs3], lhs4 };
  wire 	      op2 = lhs2 inside { [lhs2:lhs3], lhs4 };
  wire 	      op3 = lhs3 inside { [lhs2:lhs3], lhs4 };
  wire 	      op4 = lhs4 inside { [lhs2:lhs3], lhs4 };

  wire 	      oq1 = lhs1 inside { [$:lhs2], lhs3 };
  wire 	      oq2 = lhs2 inside { [$:lhs2], lhs3 };
  wire 	      oq3 = lhs3 inside { [$:lhs2], lhs3 };
  wire 	      oq4 = lhs4 inside { [$:lhs2], lhs3 };

  wire 	      or1 = lhs1 inside { [lhs1:lhs2], [lhs3:lhs4] };
  wire 	      or2 = lhs2 inside { [lhs1:lhs2], [lhs3:lhs4] };
  wire 	      or3 = lhs3 inside { [lhs1:lhs2], [lhs3:lhs4] };
  wire 	      or4 = lhs4 inside { [lhs1:lhs2], [lhs3:lhs4] };

  wire 	      os1 = lhs1 inside { [lhs1:lhs3], [lhs2:lhs4], 0 };
  wire 	      os2 = lhs2 inside { [lhs1:lhs3], [lhs2:lhs4], 0 };
  wire 	      os3 = lhs3 inside { [lhs1:lhs3], [lhs2:lhs4], 0 };
  wire 	      os4 = lhs4 inside { [lhs1:lhs3], [lhs2:lhs4], 0 };


  assign out = {
	       os4, os3, os2, os1,
	       or4, or3, or2, or1,
	       oq4, oq3, oq2, oq1,
	       op4, op3, op2, op1,
	       oo4, oo3, oo2, oo1,
	       on4, on3, on2, on1,
	       om4, om3, om2, om1,
	       ol4, ol3, ol2, ol1,
	       ok4, ok3, ok2, ok1,
	       oj4, oj3, oj2, oj1,
	       oi4, oi3, oi2, oi1,
               oh4, oh3, oh2, oh1,
	       og4, og3, og2, og1,
	       of4, of3, of2, of1,
               oe4, oe3, oe2, oe1,
               od4, od3, od2, od1,
               oc4, oc3, oc2, oc1,
               ob4, ob3, ob2, ob1,
	       oa4, oa3, oa2, oa1
	       };

endmodule // spec
