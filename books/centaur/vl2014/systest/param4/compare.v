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

module compare () ;

  reg [3:0] in1, in2;

  wire [3:0]
	    aout_spec1, aout_spec2, aout_spec3,
	    bout_spec1, bout_spec2, bout_spec3, bout_spec4, bout_spec5, bout_spec6, bout_spec7,
	    cout_spec1, cout_spec2, cout_spec3, cout_spec4, cout_spec5, cout_spec6, cout_spec7,
	    dout_spec1, dout_spec2, dout_spec3, dout_spec4, dout_spec5, dout_spec6, dout_spec7,
	    eout_spec1, eout_spec2, eout_spec3, eout_spec4, eout_spec5, eout_spec6, eout_spec7,
	    fout_spec1, fout_spec2, fout_spec3, fout_spec4, fout_spec5, fout_spec6, fout_spec7,
	    gout_spec1, gout_spec2, gout_spec3, gout_spec4, gout_spec5, gout_spec6, gout_spec7,
	    hout_spec1, hout_spec2, hout_spec3, hout_spec4, hout_spec5, hout_spec6, hout_spec7,
	    iout_spec1, iout_spec2, iout_spec3, iout_spec4, iout_spec5, iout_spec6, iout_spec7;

  wire [3:0]
	    aout_impl1, aout_impl2, aout_impl3,
	    bout_impl1, bout_impl2, bout_impl3, bout_impl4, bout_impl5, bout_impl6, bout_impl7,
	    cout_impl1, cout_impl2, cout_impl3, cout_impl4, cout_impl5, cout_impl6, cout_impl7,
	    dout_impl1, dout_impl2, dout_impl3, dout_impl4, dout_impl5, dout_impl6, dout_impl7,
	    eout_impl1, eout_impl2, eout_impl3, eout_impl4, eout_impl5, eout_impl6, eout_impl7,
	    fout_impl1, fout_impl2, fout_impl3, fout_impl4, fout_impl5, fout_impl6, fout_impl7,
	    gout_impl1, gout_impl2, gout_impl3, gout_impl4, gout_impl5, gout_impl6, gout_impl7,
	    hout_impl1, hout_impl2, hout_impl3, hout_impl4, hout_impl5, hout_impl6, hout_impl7,
	    iout_impl1, iout_impl2, iout_impl3, iout_impl4, iout_impl5, iout_impl6, iout_impl7;

  dut spec (.in1(in1), .in2(in2),
	    .aout1(aout_spec1), .aout2(aout_spec2), .aout3(aout_spec3),
	    .bout1(bout_spec1), .bout2(bout_spec2), .bout3(bout_spec3), .bout4(bout_spec4), .bout5(bout_spec5), .bout6(bout_spec6), .bout7(bout_spec7),
	    .cout1(cout_spec1), .cout2(cout_spec2), .cout3(cout_spec3), .cout4(cout_spec4), .cout5(cout_spec5), .cout6(cout_spec6), .cout7(cout_spec7),
	    .dout1(dout_spec1), .dout2(dout_spec2), .dout3(dout_spec3), .dout4(dout_spec4), .dout5(dout_spec5), .dout6(dout_spec6), .dout7(dout_spec7),
	    .eout1(eout_spec1), .eout2(eout_spec2), .eout3(eout_spec3), .eout4(eout_spec4), .eout5(eout_spec5), .eout6(eout_spec6), .eout7(eout_spec7),
	    .fout1(fout_spec1), .fout2(fout_spec2), .fout3(fout_spec3), .fout4(fout_spec4), .fout5(fout_spec5), .fout6(fout_spec6), .fout7(fout_spec7),
	    .gout1(gout_spec1), .gout2(gout_spec2), .gout3(gout_spec3), .gout4(gout_spec4), .gout5(gout_spec5), .gout6(gout_spec6), .gout7(gout_spec7),
	    .hout1(hout_spec1), .hout2(hout_spec2), .hout3(hout_spec3), .hout4(hout_spec4), .hout5(hout_spec5), .hout6(hout_spec6), .hout7(hout_spec7),
	    .iout1(iout_spec1), .iout2(iout_spec2), .iout3(iout_spec3), .iout4(iout_spec4), .iout5(iout_spec5), .iout6(iout_spec6), .iout7(iout_spec7)
  );

  \dut$size=1 impl (.in1(in1), .in2(in2),
	    .aout1(aout_impl1), .aout2(aout_impl2), .aout3(aout_impl3),
	    .bout1(bout_impl1), .bout2(bout_impl2), .bout3(bout_impl3), .bout4(bout_impl4), .bout5(bout_impl5), .bout6(bout_impl6), .bout7(bout_impl7),
	    .cout1(cout_impl1), .cout2(cout_impl2), .cout3(cout_impl3), .cout4(cout_impl4), .cout5(cout_impl5), .cout6(cout_impl6), .cout7(cout_impl7),
	    .dout1(dout_impl1), .dout2(dout_impl2), .dout3(dout_impl3), .dout4(dout_impl4), .dout5(dout_impl5), .dout6(dout_impl6), .dout7(dout_impl7),
	    .eout1(eout_impl1), .eout2(eout_impl2), .eout3(eout_impl3), .eout4(eout_impl4), .eout5(eout_impl5), .eout6(eout_impl6), .eout7(eout_impl7),
	    .fout1(fout_impl1), .fout2(fout_impl2), .fout3(fout_impl3), .fout4(fout_impl4), .fout5(fout_impl5), .fout6(fout_impl6), .fout7(fout_impl7),
	    .gout1(gout_impl1), .gout2(gout_impl2), .gout3(gout_impl3), .gout4(gout_impl4), .gout5(gout_impl5), .gout6(gout_impl6), .gout7(gout_impl7),
	    .hout1(hout_impl1), .hout2(hout_impl2), .hout3(hout_impl3), .hout4(hout_impl4), .hout5(hout_impl5), .hout6(hout_impl6), .hout7(hout_impl7),
	    .iout1(iout_impl1), .iout2(iout_impl2), .iout3(iout_impl3), .iout4(iout_impl4), .iout5(iout_impl5), .iout6(iout_impl6), .iout7(iout_impl7)
  );


  wire aok =
       (aout_spec1 === aout_impl1) &
       (aout_spec2 === aout_impl2) &
       (aout_spec3 === aout_impl3);

  wire bok =
       (bout_spec1 === bout_impl1) &
       (bout_spec2 === bout_impl2) &
       (bout_spec3 === bout_impl3) &
       (bout_spec4 === bout_impl4) &
       (bout_spec5 === bout_impl5) &
       (bout_spec6 === bout_impl6) &
       (bout_spec7 === bout_impl7);

  wire cok =
       (cout_spec1 === cout_impl1) &
       (cout_spec2 === cout_impl2) &
       (cout_spec3 === cout_impl3) &
       (cout_spec4 === cout_impl4) &
       (cout_spec5 === cout_impl5) &
       (cout_spec6 === cout_impl6) &
       (cout_spec7 === cout_impl7);

  wire dok =
       (dout_spec1 === dout_impl1) &
       (dout_spec2 === dout_impl2) &
       (dout_spec3 === dout_impl3) &
       (dout_spec4 === dout_impl4) &
       (dout_spec5 === dout_impl5) &
       (dout_spec6 === dout_impl6) &
       (dout_spec7 === dout_impl7);

  wire eok =
       (eout_spec1 === eout_impl1) &
       (eout_spec2 === eout_impl2) &
       (eout_spec3 === eout_impl3) &
       (eout_spec4 === eout_impl4) &
       (eout_spec5 === eout_impl5) &
       (eout_spec6 === eout_impl6) &
       (eout_spec7 === eout_impl7);

  wire fok =
       (fout_spec1 === fout_impl1) &
       (fout_spec2 === fout_impl2) &
       (fout_spec3 === fout_impl3) &
       (fout_spec4 === fout_impl4) &
       (fout_spec5 === fout_impl5) &
       (fout_spec6 === fout_impl6) &
       (fout_spec7 === fout_impl7);

  wire gok =
       (gout_spec1 === gout_impl1) &
       (gout_spec2 === gout_impl2) &
       (gout_spec3 === gout_impl3) &
       (gout_spec4 === gout_impl4) &
       (gout_spec5 === gout_impl5) &
       (gout_spec6 === gout_impl6) &
       (gout_spec7 === gout_impl7);

  wire hok =
       (hout_spec1 === hout_impl1) &
       (hout_spec2 === hout_impl2) &
       (hout_spec3 === hout_impl3) &
       (hout_spec4 === hout_impl4) &
       (hout_spec5 === hout_impl5) &
       (hout_spec6 === hout_impl6) &
       (hout_spec7 === hout_impl7);

  wire iok =
       (iout_spec1 === iout_impl1) &
       (iout_spec2 === iout_impl2) &
       (iout_spec3 === iout_impl3) &
       (iout_spec4 === iout_impl4) &
       (iout_spec5 === iout_impl5) &
       (iout_spec6 === iout_impl6) &
       (iout_spec7 === iout_impl7);

  reg [3:0] Vals;
  integer   i0, i1, i2, i3, i4, i5, i6, i7;

  initial
  begin

    Vals <= 4'bZX10;  // The valid Verilog values

    for(i0 = 0; i0 < 4; i0 = i0 + 1)
    for(i1 = 0; i1 < 4; i1 = i1 + 1)
    for(i2 = 0; i2 < 4; i2 = i2 + 1)
    for(i3 = 0; i3 < 4; i3 = i3 + 1)
    for(i4 = 0; i4 < 4; i4 = i4 + 1)
    for(i5 = 0; i5 < 4; i5 = i5 + 1)
    for(i6 = 0; i6 < 4; i6 = i6 + 1)
    for(i7 = 0; i7 < 4; i7 = i7 + 1)
    begin
      in1 = { Vals[i0], Vals[i1], Vals[i2], Vals[i3] };
      in2 = { Vals[i4], Vals[i5], Vals[i6], Vals[i7] };
      #100;

      if (aok !== 1'b1) begin
	$display("A fail for in1 = %b, in2 = %b", in1, in2);
	if (aout_spec1 !== aout_impl1) $display("aout1: spec %b !== impl %b", aout_spec1, aout_impl1);
	if (aout_spec2 !== aout_impl2) $display("aout2: spec %b !== impl %b", aout_spec2, aout_impl2);
	if (aout_spec3 !== aout_impl3) $display("aout3: spec %b !== impl %b", aout_spec3, aout_impl3);
      end

      if (bok !== 1'b1) begin
	$display("B fail for in1 = %b, in2 = %b", in1, in2);
	if (bout_spec1 !== bout_impl1) $display("bout1: spec %b !== impl %b", bout_spec1, bout_impl1);
	if (bout_spec2 !== bout_impl2) $display("bout2: spec %b !== impl %b", bout_spec2, bout_impl2);
	if (bout_spec3 !== bout_impl3) $display("bout3: spec %b !== impl %b", bout_spec3, bout_impl3);
	if (bout_spec4 !== bout_impl4) $display("bout4: spec %b !== impl %b", bout_spec4, bout_impl4);
	if (bout_spec5 !== bout_impl5) $display("bout5: spec %b !== impl %b", bout_spec5, bout_impl5);
	if (bout_spec6 !== bout_impl6) $display("bout6: spec %b !== impl %b", bout_spec6, bout_impl6);
	if (bout_spec7 !== bout_impl7) $display("bout7: spec %b !== impl %b", bout_spec7, bout_impl7);
      end

      if (cok !== 1'b1) begin
	$display("C fail for in1 = %b, in2 = %b", in1, in2);
	if (cout_spec1 !== cout_impl1) $display("cout1: spec %b !== impl %b", cout_spec1, cout_impl1);
	if (cout_spec2 !== cout_impl2) $display("cout2: spec %b !== impl %b", cout_spec2, cout_impl2);
	if (cout_spec3 !== cout_impl3) $display("cout3: spec %b !== impl %b", cout_spec3, cout_impl3);
	if (cout_spec4 !== cout_impl4) $display("cout4: spec %b !== impl %b", cout_spec4, cout_impl4);
	if (cout_spec5 !== cout_impl5) $display("cout5: spec %b !== impl %b", cout_spec5, cout_impl5);
	if (cout_spec6 !== cout_impl6) $display("cout6: spec %b !== impl %b", cout_spec6, cout_impl6);
	if (cout_spec7 !== cout_impl7) $display("cout7: spec %b !== impl %b", cout_spec7, cout_impl7);
      end

      if (dok !== 1'b1) begin
	$display("D fail for in1 = %b, in2 = %b", in1, in2);
	if (dout_spec1 !== dout_impl1) $display("dout1: spec %b !== impl %b", dout_spec1, dout_impl1);
	if (dout_spec2 !== dout_impl2) $display("dout2: spec %b !== impl %b", dout_spec2, dout_impl2);
	if (dout_spec3 !== dout_impl3) $display("dout3: spec %b !== impl %b", dout_spec3, dout_impl3);
	if (dout_spec4 !== dout_impl4) $display("dout4: spec %b !== impl %b", dout_spec4, dout_impl4);
	if (dout_spec5 !== dout_impl5) $display("dout5: spec %b !== impl %b", dout_spec5, dout_impl5);
	if (dout_spec6 !== dout_impl6) $display("dout6: spec %b !== impl %b", dout_spec6, dout_impl6);
	if (dout_spec7 !== dout_impl7) $display("dout7: spec %b !== impl %b", dout_spec7, dout_impl7);
      end

      if (eok !== 1'b1) begin
	$display("E fail for in1 = %b, in2 = %b", in1, in2);
	if (eout_spec1 !== eout_impl1) $display("eout1: spec %b !== impl %b", eout_spec1, eout_impl1);
	if (eout_spec2 !== eout_impl2) $display("eout2: spec %b !== impl %b", eout_spec2, eout_impl2);
	if (eout_spec3 !== eout_impl3) $display("eout3: spec %b !== impl %b", eout_spec3, eout_impl3);
	if (eout_spec4 !== eout_impl4) $display("eout4: spec %b !== impl %b", eout_spec4, eout_impl4);
	if (eout_spec5 !== eout_impl5) $display("eout5: spec %b !== impl %b", eout_spec5, eout_impl5);
	if (eout_spec6 !== eout_impl6) $display("eout6: spec %b !== impl %b", eout_spec6, eout_impl6);
	if (eout_spec7 !== eout_impl7) $display("eout7: spec %b !== impl %b", eout_spec7, eout_impl7);
      end

      if (fok !== 1'b1) begin
	$display("F fail for in1 = %b, in2 = %b", in1, in2);
	if (fout_spec1 !== fout_impl1) $display("fout1: spec %b !== impl %b", fout_spec1, fout_impl1);
	if (fout_spec2 !== fout_impl2) $display("fout2: spec %b !== impl %b", fout_spec2, fout_impl2);
	if (fout_spec3 !== fout_impl3) $display("fout3: spec %b !== impl %b", fout_spec3, fout_impl3);
	if (fout_spec4 !== fout_impl4) $display("fout4: spec %b !== impl %b", fout_spec4, fout_impl4);
	if (fout_spec5 !== fout_impl5) $display("fout5: spec %b !== impl %b", fout_spec5, fout_impl5);
	if (fout_spec6 !== fout_impl6) $display("fout6: spec %b !== impl %b", fout_spec6, fout_impl6);
	if (fout_spec7 !== fout_impl7) $display("fout7: spec %b !== impl %b", fout_spec7, fout_impl7);
      end

      if (gok !== 1'b1) begin
	$display("G fail for in1 = %b, in2 = %b", in1, in2);
	if (gout_spec1 !== gout_impl1) $display("gout1: spec %b !== impl %b", gout_spec1, gout_impl1);
	if (gout_spec2 !== gout_impl2) $display("gout2: spec %b !== impl %b", gout_spec2, gout_impl2);
	if (gout_spec3 !== gout_impl3) $display("gout3: spec %b !== impl %b", gout_spec3, gout_impl3);
	if (gout_spec4 !== gout_impl4) $display("gout4: spec %b !== impl %b", gout_spec4, gout_impl4);
	if (gout_spec5 !== gout_impl5) $display("gout5: spec %b !== impl %b", gout_spec5, gout_impl5);
	if (gout_spec6 !== gout_impl6) $display("gout6: spec %b !== impl %b", gout_spec6, gout_impl6);
	if (gout_spec7 !== gout_impl7) $display("gout7: spec %b !== impl %b", gout_spec7, gout_impl7);
      end

      if (hok !== 1'b1) begin
	$display("H fail for in1 = %b, in2 = %b", in1, in2);
	if (hout_spec1 !== hout_impl1) $display("hout1: spec %b !== impl %b", hout_spec1, hout_impl1);
	if (hout_spec2 !== hout_impl2) $display("hout2: spec %b !== impl %b", hout_spec2, hout_impl2);
	if (hout_spec3 !== hout_impl3) $display("hout3: spec %b !== impl %b", hout_spec3, hout_impl3);
	if (hout_spec4 !== hout_impl4) $display("hout4: spec %b !== impl %b", hout_spec4, hout_impl4);
	if (hout_spec5 !== hout_impl5) $display("hout5: spec %b !== impl %b", hout_spec5, hout_impl5);
	if (hout_spec6 !== hout_impl6) $display("hout6: spec %b !== impl %b", hout_spec6, hout_impl6);
	if (hout_spec7 !== hout_impl7) $display("hout7: spec %b !== impl %b", hout_spec7, hout_impl7);
      end

    end
  end
endmodule
