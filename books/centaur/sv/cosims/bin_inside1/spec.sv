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



// NOTE: The notes below pertain to versions of VCS before around 2015
// or so.  Versions dated later than 2017 now seem to match
// NCVerilog's behavior, which means we're mismatching for now.



// Special hand-crafted tests of the inside operator.
//
// SystemVerilog-2012 seems to not cover this operator very well and there are
// many cases where NCV and VCS disagree.  Sol and Jared have decided, by coin
// flip---actually, neither of us had a coin so we used (random$ 2 state)---to
// try to follow the VCS behavior.
//
// Result size and type.  The inside operator isn't included in Table 11-21
// (expression bit lengths) but, assuming it behaves like other comparisons, it
// should probably have a self-determined size of 1 and should always be
// unsigned.  Some informative test cases:
//
//     wire signed [3:0] xx = 1;
//     wire signed [3:0] foo = xx inside {xx};
//     wire signed [3:0] bar = (xx inside {xx}) + 1'sb1;
//
// Even though everything here is signed, NCV and VCS agree that foo is 0001
// and bar is 0010, so we definitely seem to be producing a 1-bit unsigned
// result.
//
// A more subtle question is: how are the sizes/signedness of the
// subexpressions are supposed to affect each other?  Some informative basic
// tests:
//
//     3'sb 100  inside { 4'sb 1100 }       NCV and VCS both say 1
//     3'sb 100  inside { 4'b  1100 }       NCV and VCS both say 0
//     4'sb 1100 inside { 3'sb 100 }        NCV and VCS both say 1
//     4'b  1100 inside { 3'sb 100 }        NCV and VCS both say 0
//
// So at a minimum, when comparing the LHS to some RHS element of the range, it
// seems that the sizes/signedness of LHS/RHS affect each other as in equality
// comparisons.  This all seems to be consistent with the idea that:
//
//      LHS inside {VAL}    means    LHS ==? VAL
//
// But there could also be other members of the range.  Do their sizes
// and signedness matter?  Here are some good test cases where,
// unfortunately, NCVerilog and VCS disagree.
//                                                                 // VCS    NCV
//   (A) 3'sb 100  inside { (3'sb100 << 1'b1) >>> 1'b1, 4'sb0 });  //  0      1
//   (B) 3'sb 100  inside { (3'sb100 << 1'b1) >>> 1'b1,  4'b0 });  //  0      1
//   (C) 4'sb 1100 inside { (3'sb100 << 1'b1) >>> 1'b1,  4'b0 });  //  1      0
//
// Note here that the first value, (3'sb100 << 1'b1) >>> 1'b1, will evaluate
// to:
//
//       0    -- if evaluated in any 3-bit context
//       0100 -- if evaluated in a four-bit unsigned context
//       1100 -- if evaluated in a four-bit signed context
//
// Analysis of NCV behavior.  From test case A==1, it appears that the four-bit
// zero must be providing a 4-bit context for the first value, since the
// shifting has to happen in 4 bits for the comparisons to succeed.  From case
// C==0, it appears that the unsignedness of the extra value is causing the
// first expression to be evaluated in an unsigned context, since otherwise its
// value would match the LHS.  This is consistent with case B==1, since if we
// do everything in an unsigned 4-bit context then the LHS and VAL1 will both
// be 0100.
//
// Analysis of VCS behavior.  From test case A==0, it appears that despite the
// four-bit value in the range list, the shifting is being done in 3 bits,
// losing the sign bit, and hence causing a failure.  From case B==0 we can
// imagine the same thing is happening.  From case C==1 it seems that the first
// value must be evaluated in a signed context, so the extra unsigned value in
// the range list isn't affecting us.
//
// In short, it seems that NCV is considering all the range expressions
// together, while VCS is considering them one at a time.  We could imagine
// that the implementations expand the expressions to, e.g.:
//
//    NCV:  ( 3'sb 100 ==? (3'sb100 << 1'b1) >> 1'b1 ) | ( 3'sb 100 ==? 4'b0 )
//    VCS:  { 3'sb 100 ==? (3'sb100 << 1'b1) >> 1'b1 } | { 3'sb 100 ==? 4'b0 }
//
// Let's move on to ranges.
//
// From the language in 11.4.13, it sounds like an inside expression of the
// form LHS inside {[LOW:HIGH]} is essentially supposed to get turned into
// something involving <= comparisons on the ranges.  The most basic way to
// translate these would be:
//
//     (LOW <= LHS) & (LHS <= HIGH)
//
// Some basic tests suggest that we definitely need to extend the operands
// to these comparisons in some way.  For instance:
//
//     3'sb 100   inside { [4'sb1100:4'sb1100] }
//
//        -- NCV and VCS both say 1, so the 3'sb 100 seems to get sign-extended.
//
//     4'sb 1100  inside { [3'sb100 : 3'sb100] }
//
//        -- NCV and VCS both say 1, so the 3'sb100's seem to get sign extended
//
// But there seem to be disagreements between whether the high/low are to
// affect one another.  Some particular test cases:
//
//                                                  //   VCS    NCV
//     (A)  1'sb1 inside { [ 4'b0  : 3'sb 100 ] }   //    0      1
//     (B)  1'sb1 inside { [ 1'sb1 : 3'sb 100 ] }   //    0      0
//     (C)  1'sb1 inside { [ 1'sb1 : 1'sb 1 ] }     //    0      1
//
// For now we assume that the element-versus-low and element-versus-high
// comparisons should be done without having their sizes affect one another,
// and this seems to match the VCS behavior on the tests we've tried.
//
// We can imagine translating:
//
//    LHS inside { [LOW:HIGH], VAL2 } into, e.g.,
//
//       1. ((LOW <= LHS) & (LHS <= HIGH)) | (LHS ==? VAL2)
//       2. {(LOW <= LHS) & (LHS <= HIGH)} | (LHS ==? VAL2)
//
// Here are some test cases:
//
//    4'sb 1100 inside { 4' b0, [ (3'sb100 << 1'b1) >>> 1'b1 : 4'sb0 ] }   NCV says 0, VCS says 1
//    4'sb 1100 inside { 4'sb0, [ (3'sb100 << 1'b1) >>> 1'b1 : 4'sb0 ] }   NCV and VCS both say 1
//
// This seems consistent with the other NCV/VCS disagreements we've seen.  That
// is, again NCV seems to consider the signedness of the other set members,
// whereas VCS seems to only consider the current range.  Similarly test cases,
// using a range instead, yield similar results:
//
//    4'sb 1100 inside { [4' b0:4' b1], [ (3'sb100 << 1'b1) >>> 1'b1 : 4'sb0 ] }   NCV says 0, VCS says 1
//    4'sb 1100 inside { [4'sb0:4'sb1], [ (3'sb100 << 1'b1) >>> 1'b1 : 4'sb0 ] }   NCV and VCS both say 1

module spec (input logic [127:0] in,
	     output wire [127:0] out);

  wire signed [3:0] xx = -1;
  wire signed [3:0] foo = xx inside {xx};
  wire signed [3:0] bar = (xx inside {xx}) + 1'sb1;

  wire signed [3:0] val = (3'sb100 << 1'sb1);

  wire [5:0] test1  = 3'sb 100  inside { 4'sb 1100 } ;
  wire [5:0] test1b = 3'sb 100  inside { 4'b  1100 } ;
  wire [5:0] test2  = 4'sb 1100 inside { 3'sb 100 }  ;
  wire [5:0] test2b = 4'b  1100 inside { 3'sb 100 } ;

  wire [5:0] test3a = 3'sb 100  inside { (3'sb100 << 1'b1) >>> 1'b1, 4'sb 0 } ;
  wire [5:0] test3b = 3'sb 100  inside { (3'sb100 << 1'b1) >>> 1'b1, 4'b  0 } ;

  wire [5:0] test3c = 4'sb 1100 inside { (3'sb100 << 1'b1) >>> 1'b1, 4'b  0 } ;

  wire [5:0] test4 = 3'sb  100 inside { [4'sb 1100 : 4'sb 1100] } ;
  wire [5:0] test5 = 4'sb 1100 inside { [3'sb  100 : 3'sb  100] } ;

  wire [5:0] test6 = 4'sb 1100 inside { [ (3'sb100 << 1'b1) >>> 1'b1 : 4'b  0 ] } ;
  wire [5:0] test7 = 4'sb 1100 inside { [ (3'sb100 << 1'b1) >>> 1'b1 : 4'sb 0 ] } ;

  wire [5:0] test8 = 4'sb 1100 inside { 4'b  0, [ (3'sb100 << 1'b1) >>> 1'b1 : 4'sb0 ] } ;
  wire [5:0] test9 = 4'sb 1100 inside { 4'sb 0, [ (3'sb100 << 1'b1) >>> 1'b1 : 4'sb0 ] } ;

  wire [5:0] test10 = 4'sb 1100 inside { [4'b  0 : 4'b  1], [ (3'sb100 << 1'b1) >>> 1'b1 : 4'sb0 ] } ;
  wire [5:0] test11 = 4'sb 1100 inside { [4'sb 0 : 4'sb 1], [ (3'sb100 << 1'b1) >>> 1'b1 : 4'sb0 ] } ;


  assign out = { test11, test10, test9, test8, test7, test6, test5, test4,
                 test3c, test3b, test3a,
                 test2b, test2, test1b, test1, val, foo, bar
	       };

endmodule // spec
