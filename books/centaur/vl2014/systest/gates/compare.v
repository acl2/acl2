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

  wire spec_not;
  wire spec_buf;
  wire spec_and;
  wire spec_or;
  wire spec_xor;
  wire spec_nand;
  wire spec_nor;
  wire spec_xnor;
  wire spec_bufif0;
  wire spec_bufif1;
  wire spec_notif0;
  wire spec_notif1;
  wire spec_nmos;
  wire spec_pmos;
  wire spec_cmos;
  wire spec_rnmos;
  wire spec_rpmos;
  wire spec_rcmos;

  wire impl_not;
  wire impl_buf;
  wire impl_and;
  wire impl_or;
  wire impl_xor;
  wire impl_nand;
  wire impl_nor;
  wire impl_xnor;
  wire impl_bufif0;
  wire impl_bufif1;
  wire impl_notif0;
  wire impl_notif1;
  wire impl_nmos;
  wire impl_pmos;
  wire impl_cmos;
  wire impl_rnmos;
  wire impl_rpmos;
  wire impl_rcmos;

  gates_test spec (
     src1,
     src2,
     src3,
     spec_not,
     spec_buf,
     spec_and,
     spec_or,
     spec_xor,
     spec_nand,
     spec_nor,
     spec_xnor,
     spec_bufif0,
     spec_bufif1,
     spec_notif0,
     spec_notif1,
     spec_nmos,
     spec_pmos,
     spec_cmos,
     spec_rnmos,
     spec_rpmos,
     spec_rcmos
  );

  \gates_test$size=1 impl (
     src1,
     src2,
     src3,
     impl_not,
     impl_buf,
     impl_and,
     impl_or,
     impl_xor,
     impl_nand,
     impl_nor,
     impl_xnor,
     impl_bufif0,
     impl_bufif1,
     impl_notif0,
     impl_notif1,
     impl_nmos,
     impl_pmos,
     impl_cmos,
     impl_rnmos,
     impl_rpmos,
     impl_rcmos
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
        (impl_and !== spec_and)       ||
        (impl_or !== spec_or)         ||
        (impl_xor !== spec_xor)       ||
        (impl_nand !== spec_nand)     ||
        (impl_nor !== spec_nor)       ||
        (impl_xnor !== spec_xnor)     ||
        (impl_bufif0 !== spec_bufif0) ||
        (impl_bufif1 !== spec_bufif1) ||
        (impl_notif0 !== spec_notif0) ||
        (impl_notif1 !== spec_notif1) ||
        (impl_nmos !== spec_nmos)     ||
        (impl_pmos !== spec_pmos)     ||
        (impl_cmos !== spec_cmos)     ||
        (impl_rnmos !== spec_rnmos)   ||
        (impl_rpmos !== spec_rpmos)   ||
        (impl_rcmos !== spec_rcmos))
     begin
     $display("--- src1 = %b, src2 = %b, src3 = %b -------", src1, src2, src3);

     if (impl_not !== spec_not)       $display("fail not:    impl = %b, spec = %b", impl_not,  spec_not);
     if (impl_buf !== spec_buf)       $display("fail buf:    impl = %b, spec = %b", impl_buf,  spec_buf);
     if (impl_and !== spec_and)       $display("fail and:    impl = %b, spec = %b", impl_and,  spec_and);
     if (impl_or !== spec_or)         $display("fail or:     impl = %b, spec = %b", impl_or,   spec_or);
     if (impl_xor !== spec_xor)       $display("fail xor:    impl = %b, spec = %b", impl_xor,  spec_xor);
     if (impl_nand !== spec_nand)     $display("fail nand:   impl = %b, spec = %b", impl_nand, spec_nand);
     if (impl_nor !== spec_nor)       $display("fail nor:    impl = %b, spec = %b", impl_nor,  spec_nor);
     if (impl_xnor !== spec_xnor)     $display("fail xnor:   impl = %b, spec = %b", impl_xnor, spec_xnor);
     if (impl_bufif0 !== spec_bufif0) $display("fail bufif0: impl = %b, spec = %b", impl_bufif0, spec_bufif0);
     if (impl_bufif1 !== spec_bufif1) $display("fail bufif1: impl = %b, spec = %b", impl_bufif1, spec_bufif1);
     if (impl_notif0 !== spec_notif0) $display("fail notif0: impl = %b, spec = %b", impl_notif0, spec_notif0);
     if (impl_notif1 !== spec_notif1) $display("fail notif1: impl = %b, spec = %b", impl_notif1, spec_notif1);


     if (impl_nmos !== spec_nmos)     $display("%s nmos:   impl = %b, spec = %b", ((impl_nmos === 1'bx)  ? "conservative" : "fail"), impl_nmos,  spec_nmos);
     if (impl_pmos !== spec_pmos)     $display("%s pmos:   impl = %b, spec = %b", ((impl_pmos === 1'bx)  ? "conservative" : "fail"), impl_pmos,  spec_pmos);
     if (impl_cmos !== spec_cmos)     $display("%s cmos:   impl = %b, spec = %b", ((impl_cmos === 1'bx)  ? "conservative" : "fail"), impl_cmos,  spec_cmos);
     if (impl_rnmos !== spec_rnmos)   $display("%s rnmos:  impl = %b, spec = %b", ((impl_rnmos === 1'bx) ? "conservative" : "fail"), impl_rnmos, spec_rnmos);
     if (impl_rpmos !== spec_rpmos)   $display("%s rpmos:  impl = %b, spec = %b", ((impl_rpmos === 1'bx) ? "conservative" : "fail"), impl_rpmos, spec_rpmos);
     if (impl_rcmos !== spec_rcmos)   $display("%s rcmos:  impl = %b, spec = %b", ((impl_rcmos === 1'bx) ? "conservative" : "fail"), impl_rcmos, spec_rcmos);

     $display("----------------------------------------\n");

    end

  end


endmodule

