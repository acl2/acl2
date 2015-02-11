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

// basic tests of UDPs


// Stupid preprocessor hacking to make VL produce modules whose names are
// different from the spec modules.

`define UDP_NOT  udp_not
`define UDP_BUF  udp_buf
`define UDP_AND  udp_and
`define UDP_OR   udp_or
`define UDP_XOR  udp_xor
`define UDP_NAND udp_nand
`define UDP_NOR  udp_nor
`define UDP_XNOR udp_xnor

/*+VL

 `define UDP_NOT  udp_not_vl
 `define UDP_BUF  udp_buf_vl
 `define UDP_AND  udp_and_vl
 `define UDP_OR   udp_or_vl
 `define UDP_XOR  udp_xor_vl
 `define UDP_NAND udp_nand_vl
 `define UDP_NOR  udp_nor_vl
 `define UDP_XNOR udp_xnor_vl

*/


primitive `UDP_NOT (o, i);

  output o;
  input  i;

  table
    // i   :   o
       1   :   0 ;
       0   :   1 ;
  endtable

endprimitive


primitive `UDP_BUF (o, i);

  output o;
  input  i;

  table
    // i   :   o
       1   :   1 ;
       0   :   0 ;
  endtable

endprimitive


primitive `UDP_AND (output o, input a, input b) ;

  table
    // a    b    :    o
       1    1    :    1 ;
       1    0    :    0 ;
       0    1    :    0 ;
       0    0    :    0 ;
  endtable

// Stupid test of end token matching
`ifdef SYSTEM_VERILOG_MODE
endprimitive : `UDP_AND
`else
endprimitive
`endif

primitive `UDP_OR (output o, input a, input b) ;

  table
    // a    b    :    o
       1    ?    :    1 ;
       ?    1    :    1 ;
       0    0    :    0 ;
  endtable

endprimitive


primitive `UDP_XOR (o, a, b);

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


primitive `UDP_NAND (o, a, b);

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


primitive `UDP_NOR (o, b, a);

  output o;
  input  a, b;

  table
    // b    a    :    o
       1    b    :    0 ;
       ?    1    :    0 ;
       0    0    :    1 ;
  endtable

endprimitive


primitive `UDP_XNOR (output o, input a, input b);
  table
    // a    b    :    o
       1    1    :    1 ;
       0    0    :    1 ;
       1    0    :    0 ;
       0    1    :    0 ;
  endtable
endprimitive



module udps_test (

src1,
src2,
src3,

out_not,
out_buf,

out_and,
out_or,
out_xor,
out_nand,
out_nor,
out_xnor

);

   parameter size = 1;

   input [size-1:0] src1;
   input [size-1:0] src2;
   input [size-1:0] src3;

   output out_not;
   output out_buf;

   output out_and;
   output out_or;
   output out_xor;
   output out_nand;
   output out_nor;
   output out_xnor;

   `UDP_NOT (out_not, src1);
   `UDP_BUF (out_buf, src1);

   `UDP_AND myand  (out_and,  src1, src2);
   `UDP_OR  myor   (out_or,   src1, src2);
   `UDP_XOR  (out_xor,  src1, src2);
   `UDP_NAND (out_nand, src1, src2);
   `UDP_NOR  (out_nor,  src1, src2);
   `UDP_XNOR (out_xnor, src1, src2);

endmodule



/*+VL

module make_tests () ;

   wire [100:0] w;
   wire a;

  `define outs w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]

   udps_test #(1) test1 (1'b0, 1'b0, 1'b0, `outs);

// Maybe, if we want to allow multi-bit inputs:
//
//   gates_test #(2) test2 (2'b0, 2'b0, 2'b0, `outs);
//   gates_test #(3) test3 (3'b0, 3'b0, 3'b0, `outs);
//   gates_test #(4) test4 (4'b0, 4'b0, 4'b0, `outs);

endmodule

*/


