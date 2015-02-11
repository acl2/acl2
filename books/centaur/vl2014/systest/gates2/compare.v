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

module compare_gates () ;

  reg src1;
  reg src2;
  reg src3;
  reg src4;

  wire spec_not;
  wire spec_buf;
  wire spec_not2;
  wire spec_buf2;
  wire spec_and;
  wire spec_or;
  wire spec_xor;
  wire spec_nand;
  wire spec_nor;
  wire spec_xnor;
  wire spec_and3;
  wire spec_or3;
  wire spec_xor3;
  wire spec_nand3;
  wire spec_nor3;
  wire spec_xnor3;
  wire spec_and4;
  wire spec_or4;
  wire spec_xor4;
  wire spec_nand4;
  wire spec_nor4;
  wire spec_xnor4;

  gates_test spec (.src1(src1),
                   .src2(src2),
                   .src3(src3),
                   .src4(src4),
                   .out_not(spec_not),
                   .out_buf(spec_buf),
                   .out_not2(spec_not2),
                   .out_buf2(spec_buf2),
                   .out_and(spec_and),
                   .out_or(spec_or),
                   .out_xor(spec_xor),
                   .out_nand(spec_nand),
                   .out_nor(spec_nor),
                   .out_xnor(spec_xnor),
                   .out_and3(spec_and3),
                   .out_or3(spec_or3),
                   .out_xor3(spec_xor3),
                   .out_nand3(spec_nand3),
                   .out_nor3(spec_nor3),
                   .out_xnor3(spec_xnor3),
                   .out_and4(spec_and4),
                   .out_or4(spec_or4),
                   .out_xor4(spec_xor4),
                   .out_nand4(spec_nand4),
                   .out_nor4(spec_nor4),
                   .out_xnor4(spec_xnor4)
  );

  wire impl_not;
  wire impl_buf;
  wire impl_not2;
  wire impl_buf2;
  wire impl_and;
  wire impl_or;
  wire impl_xor;
  wire impl_nand;
  wire impl_nor;
  wire impl_xnor;
  wire impl_and3;
  wire impl_or3;
  wire impl_xor3;
  wire impl_nand3;
  wire impl_nor3;
  wire impl_xnor3;
  wire impl_and4;
  wire impl_or4;
  wire impl_xor4;
  wire impl_nand4;
  wire impl_nor4;
  wire impl_xnor4;

  \gates_test$size=1 impl (.src1(src1),
                           .src2(src2),
                           .src3(src3),
                           .src4(src4),
                           .out_not(impl_not),
                           .out_buf(impl_buf),
                           .out_not2(impl_not2),
                           .out_buf2(impl_buf2),
                           .out_and(impl_and),
                           .out_or(impl_or),
                           .out_xor(impl_xor),
                           .out_nand(impl_nand),
                           .out_nor(impl_nor),
                           .out_xnor(impl_xnor),
                           .out_and3(impl_and3),
                           .out_or3(impl_or3),
                           .out_xor3(impl_xor3),
                           .out_nand3(impl_nand3),
                           .out_nor3(impl_nor3),
                           .out_xnor3(impl_xnor3),
                           .out_and4(impl_and4),
                           .out_or4(impl_or4),
                           .out_xor4(impl_xor4),
                           .out_nand4(impl_nand4),
                           .out_nor4(impl_nor4),
                           .out_xnor4(impl_xnor4)
       );

  reg [3:0] Vals;
  integer i0, i1, i2;

  reg check;

  initial begin
    src1 <= 1'b0;
    src2 <= 1'b0;
    src3 <= 1'b0;

    Vals <= 4'bZX10;

    for(i0 = 0; i0 < 4; i0 = i0 + 1)
    for(i1 = 0; i1 < 4; i1 = i1 + 1)
    for(i2 = 0; i2 < 4; i2 = i2 + 1)
    begin
       src1 = Vals[i0];
       src2 = Vals[i1];
       src3 = Vals[i2];
       #100
       check = 1;
       #100
       check = 0;
    end
  end

  always @(posedge check)
  begin

     if ((impl_not !== spec_not)      ||
        (impl_buf !== spec_buf)       ||
        (impl_not2 !== spec_not2)     ||
        (impl_buf2 !== spec_buf2)     ||

        (impl_and !== spec_and)       ||
        (impl_or !== spec_or)         ||
        (impl_xor !== spec_xor)       ||
        (impl_nand !== spec_nand)     ||
        (impl_nor !== spec_nor)       ||
        (impl_xnor !== spec_xnor)     ||

        (impl_and3 !== spec_and3)       ||
        (impl_or3 !== spec_or3)         ||
        (impl_xor3 !== spec_xor3)       ||
        (impl_nand3 !== spec_nand3)     ||
        (impl_nor3 !== spec_nor3)       ||
        (impl_xnor3 !== spec_xnor3)     ||

        (impl_and4 !== spec_and4)       ||
        (impl_or4 !== spec_or4)         ||
        (impl_xor4 !== spec_xor4)       ||
        (impl_nand4 !== spec_nand4)     ||
        (impl_nor4 !== spec_nor4)       ||
        (impl_xnor4 !== spec_xnor4)
     )
     begin
     $display("--- src1 = %b, src2 = %b, src3 = %b -------", src1, src2, src3);

     if (impl_not !== spec_not)       $display("fail not:    impl = %b, spec = %b", impl_not,  spec_not);
     if (impl_buf !== spec_buf)       $display("fail buf:    impl = %b, spec = %b", impl_buf,  spec_buf);
     if (impl_not2 !== spec_not2)     $display("fail not2:   impl = %b, spec = %b", impl_not2, spec_not2);
     if (impl_buf2 !== spec_buf2)     $display("fail buf2:   impl = %b, spec = %b", impl_buf2, spec_buf2);

     if (impl_and !== spec_and)       $display("fail and:    impl = %b, spec = %b", impl_and,  spec_and);
     if (impl_or !== spec_or)         $display("fail or:     impl = %b, spec = %b", impl_or,   spec_or);
     if (impl_xor !== spec_xor)       $display("fail xor:    impl = %b, spec = %b", impl_xor,  spec_xor);
     if (impl_nand !== spec_nand)     $display("fail nand:   impl = %b, spec = %b", impl_nand, spec_nand);
     if (impl_nor !== spec_nor)       $display("fail nor:    impl = %b, spec = %b", impl_nor,  spec_nor);
     if (impl_xnor !== spec_xnor)     $display("fail xnor:   impl = %b, spec = %b", impl_xnor, spec_xnor);

     if (impl_and3 !== spec_and3)     $display("fail and3:   impl = %b, spec = %b", impl_and3,  spec_and3);
     if (impl_or3 !== spec_or3)       $display("fail or3:    impl = %b, spec = %b", impl_or3,   spec_or3);
     if (impl_xor3 !== spec_xor3)     $display("fail xor3:   impl = %b, spec = %b", impl_xor3,  spec_xor3);
     if (impl_nand3 !== spec_nand3)   $display("fail nand3:  impl = %b, spec = %b", impl_nand3, spec_nand3);
     if (impl_nor3 !== spec_nor3)     $display("fail nor3:   impl = %b, spec = %b", impl_nor3,  spec_nor3);
     if (impl_xnor3 !== spec_xnor3)   $display("fail xnor3:  impl = %b, spec = %b", impl_xnor3, spec_xnor3);

     if (impl_and4 !== spec_and4)     $display("fail and4:   impl = %b, spec = %b", impl_and4,  spec_and4);
     if (impl_or4 !== spec_or4)       $display("fail or4:    impl = %b, spec = %b", impl_or4,   spec_or4);
     if (impl_xor4 !== spec_xor4)     $display("fail xor4:   impl = %b, spec = %b", impl_xor4,  spec_xor4);
     if (impl_nand4 !== spec_nand4)   $display("fail nand4:  impl = %b, spec = %b", impl_nand4, spec_nand4);
     if (impl_nor4 !== spec_nor4)     $display("fail nor4:   impl = %b, spec = %b", impl_nor4,  spec_nor4);
     if (impl_xnor4 !== spec_xnor4)   $display("fail xnor4:  impl = %b, spec = %b", impl_xnor4, spec_xnor4);

     $display("----------------------------------------\n");

    end

  end


endmodule

