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

interface IBinaryALU ();
  logic [3:0] a;
  logic [3:0] b;
  logic [3:0] op;
  logic [3:0] out;
endinterface

module BinaryALU (IBinaryALU bif);

   assign bif.out = (bif.op == 3) ? bif.a + bif.b :
                    (bif.op == 2) ? bif.a - bif.b :
                    (bif.op == 1) ? bif.a & bif.b :
                                    bif.a | bif.b ;

endmodule

interface IUnaryALU ();
  logic [3:0] a;
  logic [3:0] op;
  logic [3:0] out;
endinterface

module UnaryALU (IUnaryALU uif);

   assign uif.out = (uif.op == 3) ? uif.a  :
                    (uif.op == 2) ? -uif.a :
                    (uif.op == 1) ? &uif.a :
                                    |uif.a ;

endmodule


interface IPairedALUs () ;

  IBinaryALU bif ();
  IUnaryALU uif ();

endinterface

module PairedALUs (IPairedALUs iface) ;

  BinaryALU binaryAlu (iface.bif);
  UnaryALU unaryAlu (iface.uif);

endmodule


module spec (input logic [127:0] in,
	     output wire [127:0] out);

  IPairedALUs pif ();

  assign { pif.bif.a,
           pif.bif.b,
           pif.bif.op,
           pif.uif.a,
           pif.uif.op } = in;

  PairedALUs pairedAlus (pif);

  assign out = { pif.bif.a, pif.bif.b, pif.bif.op, pif.bif.out,
                 pif.uif.a, pif.uif.op, pif.uif.out };

endmodule




