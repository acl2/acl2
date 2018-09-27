// VL Verilog Toolkit
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

module top ;

  wire cond;
  wire [3:0] xx0, xx1, xx2;
  wire [2:0] yy0, yy1, yy2;


  // A couple of obvious places where we want to warn:

  wire [3:0] and_warn1 = xx0 & 32;     // warn since 32 is too big to fit into 4 bits
  wire [3:0] and_warn2 = xx0 & yy0;    // warn since the wires are different sizes

  // Warnings about the size of a zero are especially irritating:

  wire [3:0] and_normal1 = xx0 & 0;    // do not warn because this is common

  // Warnings about extension integers aren't ok since the whole point is that
  // they're "supposed to grow"

  wire [3:0] and_normal2 = xx0 & '0;
  wire [3:0] and_normal3 = xx0 & '1;


  // Some tricky cases.
  //   Zero is really special.  If we have the wrong size of a zero, that
  //   still doesn't seem worth bothering people about.

  wire [3:0] and_normal4 = xx0 & 2'b0;

  //   For other numbers,it's less clear what we should do.  Something
  //   like xx0 & 2'b11 is especially concerning because what if 2'b11
  //   is supposed to be a mask and the designer thinks he's getting the
  //   whole signal masked out, but forgets that he added a bit to xx0
  //   and it's three bits now instead of 2.
  //
  //   Because of this sort of thing, I think it *does* make sense to issue
  //   fussy warnings about bitwise stuff being applied to nonzero integers
  //   that are too small.

  wire [3:0] and_warn3 = xx0 & 2'b11;
  wire [3:0] and_warn4 = xx0 & 2'b10;
  wire [3:0] and_warn5 = xx0 & 2'b01;



  // When compound expressions involve plain integers, things get more
  // interesting.  The heuristics for figuring out when we do and don't want to
  // warn are a bit tricky.

  wire [3:0] andc_normal1 = xx0 & (cond ? xx1 : xx2);
  wire [3:0] andc_normal2 = xx0 & (cond ? xx1 : '0);
  wire [3:0] andc_normal3 = xx0 & (cond ? xx1 : '1);

  wire [3:0] andc_warn1 = xx0 & (2'b0 & 2'b1);
  wire [3:0] andc_warn2 = xx0 & (xx1[1:0] & 2'b11);
  wire [3:0] andc_warn3 = xx0 & (cond ? xx1 : 16); // Proper warning because 16 doesn't fit
  wire [3:0] andc_warn4 = xx0 & (cond ? xx1 : 32); // Proper warning because 32 doesn't fit.

  wire [3:0] andc_minor1 = xx0 & (cond ? xx1 : 0);  // Minor because it fits
  wire [3:0] andc_minor2 = xx0 & (cond ? xx1 : 15); // Minor because it fits



  wire lt_normal1 = xx0 < xx1;
  wire lt_normal2 = xx0 < 5;
  wire lt_normal3 = '0 < xx0;

  // This should be a warning because 32 doesn't fit.
  wire lt_warn1 = xx0 < 32;

  // I'm not sure whether we should really issue a warning here.  The wires are
  // of different sizes, but that's not entirely unreasonable.  Well, I guess
  // let's warn for now and see if it is too chatty to stand.
  wire lt_warn2 = xx0 < yy0;

  // These should be minor because they fit.
  wire ltc_minor1 = xx0 < (cond ? xx1 : 0);
  wire ltc_minor2 = xx0 < (cond ? xx1 : 5);




  wire eq_normal1 = xx0 == xx1;
  wire eq_normal2 = xx0 == 5;
  wire eq_normal3 = '0 == xx0;

  // This should be a warning because 32 doesn't fit.
  wire eq_warn1 = xx0 == 32;

  // I'm not sure whether we should really issue a warning here.  The wires are
  // of different sizes, but that's not entirely unreasonable.  Well, I guess
  // let's warn for now and see if it is too chatty to stand.
  wire eq_warn2 = xx0 == yy0;

  // These should be minor because they fit.
  wire eqc_minor1 = xx0 == (cond ? xx1 : 0);
  wire eqc_minor2 = xx0 == (cond ? xx1 : 5);



  wire cond_normal1 = cond ? xx1 : xx2;
  wire cond_normal2 = cond ? xx1 : 0;
  wire cond_normal3 = cond ? xx1 : '0;
  wire cond_normal4 = cond ? xx1 : '1;

  wire cond_warn1 = cond ? xx1 : yy1;
  wire cond_warn2 = cond ? xx0 : 16;    // 16 doesn't fit
  wire cond_warn3 = cond ? (xx0 & xx1) : (yy0 & yy1);


  //@VL LINT_IGNORE
  wire [3:0] supp_normal1 = xx0 & yy0;

  //@VL LINT_IGNORE_FUSSY_SIZE_WARNING
  wire [3:0] supp_normal2 = xx0 & yy0;

  //@VL LINT_IGNORE_FUSSY
  wire [3:0] supp_normal3 = xx0 & yy0;

  // A right shift followed by an AND seems like a reasonable thing to do.  We won't
  // warn about any of these.
  wire shift_mask_normal1 = (xx0 >> 2) & 1'b1;
  wire shift_mask_normal2 = (xx0 >> 2) & 2'b1;
  wire shift_mask_normal3 = (xx0 >> 2) & yy0[1:0];
  wire shift_mask_normal4 = (xx0 >> 2) & yy0[0];

  // For shifts combined with other operators besides and (for masking), we
  // will check for a more strict agreement
  wire shift_xor_warn1 = (xx0 >> 2) ^ 1'b1;   // warn because the "intuitive size" of (xx >> 2) is 2
  wire shift_xor_warn2 = (xx0 >> 2) ^ yy0[0];
  wire shift_xor_normal1 = (xx0 >> 2) ^ 2'b1; // don't warn because the "intuitive size" matches
  wire shift_xor_normal2 = (xx0 >> 2) ^ yy0[1:0];


endmodule


module a0;

   // [Jared] this file isn't the right place to test this, but previously we
   // failed to parse these expressions, so I'd like to keep them somewhere to
   // make sure the fix works.

   wire rand1 = $random % 2;
   wire rand2 = $urandom % 2;
   wire rand3 = $random() % 2;
   wire rand4 = $urandom() % 2;


  wire [3:0] normal_sysfun1 = xx0 & $countones(xx2);
  wire [2:0] normal_sysfun2 = yy0 & $countones(xx2);
  wire [3:0] normal_sysfun3 = xx0 == $bits(xx2);
  wire [2:0] normal_sysfun4 = yy0 == $bits(xx2);

endmodule


module a1 ;

   parameter foo = 7;
   wire [3:0] bar;
   parameter [4:0] baz = 6;

   wire x0, x1, x2;
   wire y0, y1, y2;
   wire z0, z1, z2;

   assign x0 = foo ? x1 : x2;  // don't warn about wide, untyped parameters like foo
   assign y0 = bar ? y1 : y2;  // do warn about wide wires like bar
   assign z0 = baz ? z1 : z2;  // do warn about wide, typed parameters

endmodule
