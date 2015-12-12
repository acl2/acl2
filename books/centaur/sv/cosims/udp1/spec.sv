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

// basic tests of UDPs, adapted from VL2014's systest/udp1

primitive udp_not (o, i);

  output o;
  input  i;

  table
    // i   :   o
       1   :   0 ;
       0   :   1 ;
  endtable

endprimitive


primitive udp_buf (o, i);

  output o;
  input  i;

  table
    // i   :   o
       1   :   1 ;
       0   :   0 ;
  endtable

endprimitive


primitive udp_and (output o, input a, input b) ;

  table
    // a    b    :    o
       1    1    :    1 ;
       1    0    :    0 ;
       0    1    :    0 ;
       0    0    :    0 ;
  endtable

endprimitive : udp_and


primitive udp_or (output o, input a, input b) ;

  table
    // a    b    :    o
       1    ?    :    1 ;
       ?    1    :    1 ;
       0    0    :    0 ;
  endtable

endprimitive


primitive udp_xor (o, a, b);

  input  a;
  output o;
  input  b;

  table
    // a    b    :    o
       1    0    :    1 ;
       0    1    :    1 ;
       1    1    :    0 ;
       0    0    :    0 ;
  endtable

endprimitive


primitive udp_nand (o, a, b);

  input  a, b;
  output o;

  table
    // a    b    :    o
       1    1    :    0 ;
       1    0    :    1 ;
       0    1    :    1 ;
       0    0    :    0 ;
  endtable

endprimitive


primitive udp_nor (o, b, a);

  output o;
  input  a, b;

  table
    // b    a    :    o
       1    b    :    0 ;
       ?    1    :    0 ;
       0    0    :    1 ;
  endtable

endprimitive


primitive udp_xnor (output o, input a, input b);
  table
    // a    b    :    o
       1    1    :    1 ;
       0    0    :    1 ;
       1    0    :    0 ;
       0    1    :    0 ;
  endtable
endprimitive


module spec (input logic [127:0] in,
	     output wire [127:0] out);

  wire src1, src2;

  assign {src1, src2} = in;

  udp_not (out_not, src1);
  udp_buf (out_buf, src1);

  udp_and myand  (out_and,  src1, src2);
  udp_or  myor   (out_or,   src1, src2);
  udp_xor  (out_xor,  src1, src2);
  udp_nand (out_nand, src1, src2);
  udp_nor  (out_nor,  src1, src2);
  udp_xnor (out_xnor, src1, src2);

  assign out = { out_not, out_buf, out_and, out_or, out_xor, out_nand, out_nor, out_xnor };

endmodule
