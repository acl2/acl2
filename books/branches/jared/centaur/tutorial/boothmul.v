/*

Centaur Hardware Verification Tutorial
Copyright (C) 2012-2013 Centaur Technology

Contact:
  Centaur Technology Formal Verification Group
  7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
  http://www.centtech.com/

This program is free software; you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free Software
Foundation; either version 2 of the License, or (at your option) any later
version.  This program is distributed in the hope that it will be useful but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
details.  You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software Foundation, Inc.,
51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

Original authors: Sol Swords <sswords@centtech.com>
                  Jared Davis <jared@centtech.com>

*/


// assumes minusb = - b.
// computes pp = b * (signed(abits[2:1]) + abits[0]).
module boothenc (pp, abits, b, minusb);
  output [17:0] pp;
  input [2:0] abits;
  input [15:0] b;
  input [16:0] minusb;

  wire [16:0] bsign = abits[2] ? minusb : { b[15], b };

   // is it shifted?
  wire shft = abits[0] ~^ abits[1];

   // is it zero? (all abits same)
  wire zro = shft & (abits[2] ~^ abits[1]);

   // result without the shift
  wire [16:0] res1 = zro ? 16'b0 : bsign;

   // final shift
  wire [17:0] pp = shft ? { res1, 1'b0 } : { res1[16], res1 };

endmodule

   

module boothmul (o, a, b);

  output [31:0] o;
  input [15:0] a, b;

  wire [16:0] minusb = 17'b1 + ~{ b[15], b };

  wire [17:0] pp0;
  wire [17:0] pp1;
  wire [17:0] pp2;
  wire [17:0] pp3;
  wire [17:0] pp4;
  wire [17:0] pp5;
  wire [17:0] pp6;
  wire [17:0] pp7;

   boothenc booth0 (pp0, { a[1:0], 1'b0 }, b, minusb);
   boothenc booth1 (pp1, a[3:1], b, minusb);
   boothenc booth2 (pp2, a[5:3], b, minusb);
   boothenc booth3 (pp3, a[7:5], b, minusb);
   boothenc booth4 (pp4, a[9:7], b, minusb);
   boothenc booth5 (pp5, a[11:9], b, minusb);
   boothenc booth6 (pp6, a[13:11], b, minusb);
   boothenc booth7 (pp7, a[15:13], b, minusb);

   assign o = { {14{pp0[17]}}, pp0 }
	      + { {12{pp1[17]}}, pp1, 2'b0 }
	      + { {10{pp2[17]}}, pp2, 4'b0 }
	      + { {8{pp3[17]}}, pp3, 6'b0 }
	      + { {6{pp4[17]}}, pp4, 8'b0 }
	      + { {4{pp5[17]}}, pp5, 10'b0 }
	      + { {2{pp6[17]}}, pp6, 12'b0 }
	      + { pp7, 14'b0 };

endmodule


