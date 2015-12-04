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
// Original authors: Sol Swords <sswords@centtech.com>
//                   Jared Davis <jared@centtech.com>


module typedAnd
  #(parameter type T = logic)
   (output T out, input T in1, input T in2);
   assign out = in1 & in2;
endmodule

module and4 (output [3:0] out, input [3:0] in1, input [3:0] in2) ;
  typedef logic [3:0] mytype_t;
  typedAnd #(mytype_t) inst (out, in1, in2);
endmodule

module and5 (output [4:0] out, input [4:0] in1, input [4:0] in2) ;
  typedef logic [4:0] mytype_t;
  typedAnd #(mytype_t) inst (out, in1, in2);
endmodule

module and3 (output [2:0] out, input [2:0] in1, input [2:0] in2) ;
  typedef logic [2:0] mytype_t;
  typedAnd #(mytype_t) inst (out, in1, in2);
endmodule // and3

module andx
  #(parameter type X = logic)
   (output X out, input X in1, input X in2);
    typedAnd #(X) inst (out, in1, in2);
endmodule // andx

module andxy
  #(parameter type X = logic,
    parameter type Y = X [3:0])
   (output Y out, input Y in1, input Y in2);
    typedAnd #(Y) inst (out, in1, in2);
endmodule // andxy

// module foo ;
//   typedef logic [3:0] mytype_t;
//    parameter type myparamtype = mytype_t;
//    localparam myparamtype myparam = 3;
//    initial
//      begin
//        #10;
//        $display("myparam is %d", myparam);
//      end
// endmodule // foo

// module top ;
//    foo #() fooinst ();
// endmodule

module andfoo (output [7:0] out, input [7:0] in1, in2);
  typedef logic signed [1:0] mybits_t;
   parameter type X = logic;
   parameter type Y = struct packed { X x; mybits_t mybits ;};

   wire [$bits(Y)-1:0] temp1, temp2, temp3;
   assign temp1 = in1;
   assign temp2 = in2;
   andx #(Y) inst (temp3, temp1, temp2);

   assign out = temp3;

endmodule



module spec (input logic [127:0] in,
	     output logic [127:0] out);

  wire [3:0] out4, in4a, in4b; assign { in4a, in4b } = in;
  wire [4:0] out5, in5a, in5b; assign { in5a, in5b } = in;
  wire [2:0] out3, in3a, in3b; assign { in3a, in3b } = in;
  wire [7:0] out8, in8a, in8b; assign { in8a, in8b } = in;

  wire [6:0] out7, in7a, in7b; assign {in7a, in7b} = in;
  wire [8:0] out9, in9a, in9b; assign {in9a, in9b} = in;
  wire [1:0][3:0] out2x4, in2x4a, in2x4b; assign {in2x4a, in2x4b} = in;


  wire [7:0] outfoo1, outfoo2, infoo1, infoo2; assign {infoo1, infoo2 } = in;

   assign out = { outfoo1, outfoo2, out2x4, out9, out8, out7, out4, out5, out3 } ;

   and4 inst4 (out4, in4a, in4b);
   and5 inst5 (out5, in5a, in5b);
   and3 inst3 (out3, in3a, in3b);

   typedAnd #(struct packed { logic [7:0] mem; }) inst8 (out8, in8a, in8b);


  typedef logic [6:0] b7;
  typedef logic [8:0] b9;

   andx #(b7) inst7 (out7, in7a, in7b);
   andx #(b9) inst9 (out9, in9a, in9b);

   andxy #(.X(logic [1:0])) inst2x4 (out2x4, in2x4a, in2x4b);

   andfoo #() inst10 (outfoo1, infoo1, infoo2);
   andfoo #(logic [1:0]) inst11 (outfoo2, infoo1, infoo2);

endmodule // spec
