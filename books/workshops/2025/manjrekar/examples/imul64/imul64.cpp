/*
  License: (An MIT/X11-style license)

   Permission is hereby granted, free of charge, to any person obtaining a
   copy of this software and associated documentation files (the "Software"),
   to deal in the Software without restriction, including without limitation
   the rights to use, copy, modify, merge, publish, distribute, sublicense,
   and/or sell copies of the Software, and to permit persons to whom the
   Software is furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in
   all copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
   DEALINGS IN THE SOFTWARE.

 Original author: Mayank Manjrekar <mayank.manjrekar2@arm.com>
*/

#include <stdio.h>
#include <math.h>
#include <string>
#include <vector>
#include <tuple>

#include "ac_int.h"

#define DBG(X) std::cout << (#X) << ": " << X.to_string(AC_HEX) << '\n';
#define DBGB(X) std::cout << (#X) << ": " << X << '\n';

using namespace std;

// RAC begin

typedef ac_int<2, false> ui2;
typedef ac_int<3, false> ui3;
typedef ac_int<5, false> ui5;
typedef ac_int<6, false> ui6;
typedef ac_int<7, false> ui7;
typedef ac_int<8, false> ui8;
typedef ac_int<9, false> ui9;
typedef ac_int<10, false> ui10;
typedef ac_int<11, false> ui11;
typedef ac_int<12, false> ui12;
typedef ac_int<13, false> ui13;
typedef ac_int<14, false> ui14;
typedef ac_int<16, false> ui16;
typedef ac_int<20, false> ui20;
typedef ac_int<23, false> ui23;
typedef ac_int<24, false> ui24;
typedef ac_int<28, false> ui28;
typedef ac_int<29, false> ui29;
typedef ac_int<32, false> ui32;
typedef ac_int<36, false> ui36;
typedef ac_int<40, false> ui40;
typedef ac_int<44, false> ui44;
typedef ac_int<48, false> ui48;
typedef ac_int<52, false> ui52;
typedef ac_int<53, false> ui53;
typedef ac_int<54, false> ui54;
typedef ac_int<55, false> ui55;
typedef ac_int<56, false> ui56;
typedef ac_int<57, false> ui57;
typedef ac_int<59, false> ui59;
typedef ac_int<60, false> ui60;
typedef ac_int<61, false> ui61;
typedef ac_int<63, false> ui63;
typedef ac_int<64, false> ui64;
typedef ac_int<68, false> ui68;
typedef ac_int<71, false> ui71;
typedef ac_int<72, false> ui72;
typedef ac_int<73, false> ui73;
typedef ac_int<76, false> ui76;
typedef ac_int<80, false> ui80;
typedef ac_int<84, false> ui84;
typedef ac_int<88, false> ui88;
typedef ac_int<92, false> ui92;
typedef ac_int<96, false> ui96;
typedef ac_int<99, false> ui99;
typedef ac_int<101, false> ui101;
typedef ac_int<103, false> ui103;
typedef ac_int<104, false> ui104;
typedef ac_int<105, false> ui105;
typedef ac_int<106, false> ui106;
typedef ac_int<107, false> ui107;
typedef ac_int<117, false> ui117;

typedef ac_int<109, false> ui109;
typedef ac_int<110, false> ui110;
typedef ac_int<111, false> ui111;
typedef ac_int<112, false> ui112;
typedef ac_int<114, false> ui114;
typedef ac_int<115, false> ui115;
typedef ac_int<116, false> ui116;

typedef ac_int<14, true> si14;
typedef ac_int<64, true> si64;

// Compress the sum of 29 products to 2-vector redundant form, using 27 3-2 compressors.

ui106 compress(ui106 pp0, ui106 pp1, ui106 pp2, ui106 pp3, ui106 pp4, ui106 pp5, ui106 pp6, ui106 pp7, ui106 pp8, ui106 pp9, ui106 pp10, ui106 pp11, ui106 pp12, ui106 pp13, ui106 pp14, ui106 pp15, ui106 pp16, ui106 pp17, ui106 pp18, ui106 pp19, ui106 pp20, ui106 pp21, ui106 pp22, ui106 pp23, ui106 pp24, ui106 pp25, ui106 pp26, ui106 pp27, ui106 pp28) {
  // Initial partial product dot diagram:
  // 111111
  // 000000999999999988888888887777777777666666666655555555554444444444333333333322222222221111111111
  // 5432109876543210987654321098765432109876543210987654321098765432109876543210987654321098765432109876543210
  //                                                   ********************************************************
  //                                                  ******************************************************* *
  //                                                ******************************************************* *
  //                                              ******************************************************* *
  //                                            ******************************************************* *
  //                                          ******************************************************* *
  //                                        ******************************************************* *
  //                                      ******************************************************* *
  //                                    ******************************************************* *
  //                                  ******************************************************* *
  //                                ******************************************************* *
  //                              ******************************************************* *
  //                            ******************************************************* *
  //                          ******************************************************* *
  //                        ******************************************************* *
  //                      ******************************************************* *
  //                    ******************************************************* *
  //                  ******************************************************* *
  //                ******************************************************* *
  //              ******************************************************* *
  //            ******************************************************* *
  //          ******************************************************* *
  //        ******************************************************* *
  //      ******************************************************* *
  //    ******************************************************* *
  //  ******************************************************* *
  // ****************************************************** *
  //  *****************************************************
  //   ****************************************************

  // Dadda level 0 beginning dot diagram:
  // 111111
  // 000000999999999988888888887777777777666666666655555555554444444444333333333322222222221111111111
  // 5432109876543210987654321098765432109876543210987654321098765432109876543210987654321098765432109876543210
  // **********************************************************************************************************
  //  ******************************************************************************************************* *
  //  ***************************************************************************************************** *
  //   ************************************************************************************************** *
  //    *********************************************************************************************** *
  //      ******************************************************************************************* *
  //        *************************************************************************************** *
  //          *********************************************************************************** *
  //            ******************************************************************************* *
  //              *************************************************************************** *
  //                *********************************************************************** *
  //                  ******************************************************************* *
  //                    *************************************************************** *
  //                      *********************************************************** *
  //                        ******************************************************* *
  //                          *************************************************** *
  //                            *********************************************** *
  //                              ******************************************* *
  //                                *************************************** *
  //                                  *********************************** *
  //                                    ******************************* *
  //                                      *************************** *
  //                                        *********************** *
  //                                          ******************* *
  //                                            *************** *
  //                                              *********** *
  //                                                ******* *
  //                                                  *****
  //                                                   ****

  // final_pp0[0] = pp0[0]
  // final_pp1[0] = pp1[0]
  // final_pp0[1] = pp0[1]

  ui106 l0_pp0 = 0;
  l0_pp0.set_slc(2, pp0.slc<54>(2));
  l0_pp0[56] = pp1[56];
  l0_pp0.set_slc(57, pp2.slc<2>(57));
  l0_pp0.set_slc(59, pp3.slc<2>(59));
  l0_pp0.set_slc(61, pp4.slc<2>(61));
  l0_pp0.set_slc(63, pp5.slc<2>(63));
  l0_pp0.set_slc(65, pp6.slc<2>(65));
  l0_pp0.set_slc(67, pp7.slc<2>(67));
  l0_pp0.set_slc(69, pp8.slc<2>(69));
  l0_pp0.set_slc(71, pp9.slc<2>(71));
  l0_pp0.set_slc(73, pp10.slc<2>(73));
  l0_pp0.set_slc(75, pp11.slc<2>(75));
  l0_pp0.set_slc(77, pp12.slc<2>(77));
  l0_pp0.set_slc(79, pp13.slc<2>(79));
  l0_pp0.set_slc(81, pp14.slc<2>(81));
  l0_pp0.set_slc(83, pp15.slc<2>(83));
  l0_pp0.set_slc(85, pp16.slc<2>(85));
  l0_pp0.set_slc(87, pp17.slc<2>(87));
  l0_pp0.set_slc(89, pp18.slc<2>(89));
  l0_pp0.set_slc(91, pp19.slc<2>(91));
  l0_pp0.set_slc(93, pp20.slc<2>(93));
  l0_pp0.set_slc(95, pp21.slc<2>(95));
  l0_pp0.set_slc(97, pp22.slc<2>(97));
  l0_pp0.set_slc(99, pp23.slc<2>(99));
  l0_pp0.set_slc(101, pp24.slc<2>(101));
  l0_pp0.set_slc(103, pp25.slc<2>(103));
  l0_pp0[105] = pp26[105];

  ui106 l0_pp1 = 0;
  l0_pp1.set_slc(2, pp1.slc<54>(2));
  l0_pp1[56] = pp2[56];
  l0_pp1.set_slc(57, pp3.slc<2>(57));
  l0_pp1.set_slc(59, pp4.slc<2>(59));
  l0_pp1.set_slc(61, pp5.slc<2>(61));
  l0_pp1.set_slc(63, pp6.slc<2>(63));
  l0_pp1.set_slc(65, pp7.slc<2>(65));
  l0_pp1.set_slc(67, pp8.slc<2>(67));
  l0_pp1.set_slc(69, pp9.slc<2>(69));
  l0_pp1.set_slc(71, pp10.slc<2>(71));
  l0_pp1.set_slc(73, pp11.slc<2>(73));
  l0_pp1.set_slc(75, pp12.slc<2>(75));
  l0_pp1.set_slc(77, pp13.slc<2>(77));
  l0_pp1.set_slc(79, pp14.slc<2>(79));
  l0_pp1.set_slc(81, pp15.slc<2>(81));
  l0_pp1.set_slc(83, pp16.slc<2>(83));
  l0_pp1.set_slc(85, pp17.slc<2>(85));
  l0_pp1.set_slc(87, pp18.slc<2>(87));
  l0_pp1.set_slc(89, pp19.slc<2>(89));
  l0_pp1.set_slc(91, pp20.slc<2>(91));
  l0_pp1.set_slc(93, pp21.slc<2>(93));
  l0_pp1.set_slc(95, pp22.slc<2>(95));
  l0_pp1.set_slc(97, pp23.slc<2>(97));
  l0_pp1.set_slc(99, pp24.slc<2>(99));
  l0_pp1.set_slc(101, pp25.slc<2>(101));
  l0_pp1.set_slc(103, pp26.slc<2>(103));

  ui106 l0_pp2 = 0;
  l0_pp2[2] = pp2[2];
  l0_pp2.set_slc(4, pp2.slc<52>(4));
  l0_pp2[56] = pp3[56];
  l0_pp2.set_slc(57, pp4.slc<2>(57));
  l0_pp2.set_slc(59, pp5.slc<2>(59));
  l0_pp2.set_slc(61, pp6.slc<2>(61));
  l0_pp2.set_slc(63, pp7.slc<2>(63));
  l0_pp2.set_slc(65, pp8.slc<2>(65));
  l0_pp2.set_slc(67, pp9.slc<2>(67));
  l0_pp2.set_slc(69, pp10.slc<2>(69));
  l0_pp2.set_slc(71, pp11.slc<2>(71));
  l0_pp2.set_slc(73, pp12.slc<2>(73));
  l0_pp2.set_slc(75, pp13.slc<2>(75));
  l0_pp2.set_slc(77, pp14.slc<2>(77));
  l0_pp2.set_slc(79, pp15.slc<2>(79));
  l0_pp2.set_slc(81, pp16.slc<2>(81));
  l0_pp2.set_slc(83, pp17.slc<2>(83));
  l0_pp2.set_slc(85, pp18.slc<2>(85));
  l0_pp2.set_slc(87, pp19.slc<2>(87));
  l0_pp2.set_slc(89, pp20.slc<2>(89));
  l0_pp2.set_slc(91, pp21.slc<2>(91));
  l0_pp2.set_slc(93, pp22.slc<2>(93));
  l0_pp2.set_slc(95, pp23.slc<2>(95));
  l0_pp2.set_slc(97, pp24.slc<2>(97));
  l0_pp2.set_slc(99, pp25.slc<2>(99));
  l0_pp2.set_slc(101, pp26.slc<2>(101));
  l0_pp2.set_slc(103, pp27.slc<2>(103));

  ui106 l0_pp3 = 0;
  l0_pp3[4] = pp3[4];
  l0_pp3.set_slc(6, pp3.slc<50>(6));
  l0_pp3[56] = pp4[56];
  l0_pp3.set_slc(57, pp5.slc<2>(57));
  l0_pp3.set_slc(59, pp6.slc<2>(59));
  l0_pp3.set_slc(61, pp7.slc<2>(61));
  l0_pp3.set_slc(63, pp8.slc<2>(63));
  l0_pp3.set_slc(65, pp9.slc<2>(65));
  l0_pp3.set_slc(67, pp10.slc<2>(67));
  l0_pp3.set_slc(69, pp11.slc<2>(69));
  l0_pp3.set_slc(71, pp12.slc<2>(71));
  l0_pp3.set_slc(73, pp13.slc<2>(73));
  l0_pp3.set_slc(75, pp14.slc<2>(75));
  l0_pp3.set_slc(77, pp15.slc<2>(77));
  l0_pp3.set_slc(79, pp16.slc<2>(79));
  l0_pp3.set_slc(81, pp17.slc<2>(81));
  l0_pp3.set_slc(83, pp18.slc<2>(83));
  l0_pp3.set_slc(85, pp19.slc<2>(85));
  l0_pp3.set_slc(87, pp20.slc<2>(87));
  l0_pp3.set_slc(89, pp21.slc<2>(89));
  l0_pp3.set_slc(91, pp22.slc<2>(91));
  l0_pp3.set_slc(93, pp23.slc<2>(93));
  l0_pp3.set_slc(95, pp24.slc<2>(95));
  l0_pp3.set_slc(97, pp25.slc<2>(97));
  l0_pp3.set_slc(99, pp26.slc<2>(99));
  l0_pp3.set_slc(101, pp27.slc<2>(101));
  l0_pp3[103] = pp28[103];

  ui106 l0_pp4 = 0;
  l0_pp4[6] = pp4[6];
  l0_pp4.set_slc(8, pp4.slc<48>(8));
  l0_pp4[56] = pp5[56];
  l0_pp4.set_slc(57, pp6.slc<2>(57));
  l0_pp4.set_slc(59, pp7.slc<2>(59));
  l0_pp4.set_slc(61, pp8.slc<2>(61));
  l0_pp4.set_slc(63, pp9.slc<2>(63));
  l0_pp4.set_slc(65, pp10.slc<2>(65));
  l0_pp4.set_slc(67, pp11.slc<2>(67));
  l0_pp4.set_slc(69, pp12.slc<2>(69));
  l0_pp4.set_slc(71, pp13.slc<2>(71));
  l0_pp4.set_slc(73, pp14.slc<2>(73));
  l0_pp4.set_slc(75, pp15.slc<2>(75));
  l0_pp4.set_slc(77, pp16.slc<2>(77));
  l0_pp4.set_slc(79, pp17.slc<2>(79));
  l0_pp4.set_slc(81, pp18.slc<2>(81));
  l0_pp4.set_slc(83, pp19.slc<2>(83));
  l0_pp4.set_slc(85, pp20.slc<2>(85));
  l0_pp4.set_slc(87, pp21.slc<2>(87));
  l0_pp4.set_slc(89, pp22.slc<2>(89));
  l0_pp4.set_slc(91, pp23.slc<2>(91));
  l0_pp4.set_slc(93, pp24.slc<2>(93));
  l0_pp4.set_slc(95, pp25.slc<2>(95));
  l0_pp4.set_slc(97, pp26.slc<2>(97));
  l0_pp4.set_slc(99, pp27.slc<2>(99));
  l0_pp4.set_slc(101, pp28.slc<2>(101));

  ui106 l0_pp5 = 0;
  l0_pp5[8] = pp5[8];
  l0_pp5.set_slc(10, pp5.slc<46>(10));
  l0_pp5[56] = pp6[56];
  l0_pp5.set_slc(57, pp7.slc<2>(57));
  l0_pp5.set_slc(59, pp8.slc<2>(59));
  l0_pp5.set_slc(61, pp9.slc<2>(61));
  l0_pp5.set_slc(63, pp10.slc<2>(63));
  l0_pp5.set_slc(65, pp11.slc<2>(65));
  l0_pp5.set_slc(67, pp12.slc<2>(67));
  l0_pp5.set_slc(69, pp13.slc<2>(69));
  l0_pp5.set_slc(71, pp14.slc<2>(71));
  l0_pp5.set_slc(73, pp15.slc<2>(73));
  l0_pp5.set_slc(75, pp16.slc<2>(75));
  l0_pp5.set_slc(77, pp17.slc<2>(77));
  l0_pp5.set_slc(79, pp18.slc<2>(79));
  l0_pp5.set_slc(81, pp19.slc<2>(81));
  l0_pp5.set_slc(83, pp20.slc<2>(83));
  l0_pp5.set_slc(85, pp21.slc<2>(85));
  l0_pp5.set_slc(87, pp22.slc<2>(87));
  l0_pp5.set_slc(89, pp23.slc<2>(89));
  l0_pp5.set_slc(91, pp24.slc<2>(91));
  l0_pp5.set_slc(93, pp25.slc<2>(93));
  l0_pp5.set_slc(95, pp26.slc<2>(95));
  l0_pp5.set_slc(97, pp27.slc<2>(97));
  l0_pp5.set_slc(99, pp28.slc<2>(99));

  ui106 l0_pp6 = 0;
  l0_pp6[10] = pp6[10];
  l0_pp6.set_slc(12, pp6.slc<44>(12));
  l0_pp6[56] = pp7[56];
  l0_pp6.set_slc(57, pp8.slc<2>(57));
  l0_pp6.set_slc(59, pp9.slc<2>(59));
  l0_pp6.set_slc(61, pp10.slc<2>(61));
  l0_pp6.set_slc(63, pp11.slc<2>(63));
  l0_pp6.set_slc(65, pp12.slc<2>(65));
  l0_pp6.set_slc(67, pp13.slc<2>(67));
  l0_pp6.set_slc(69, pp14.slc<2>(69));
  l0_pp6.set_slc(71, pp15.slc<2>(71));
  l0_pp6.set_slc(73, pp16.slc<2>(73));
  l0_pp6.set_slc(75, pp17.slc<2>(75));
  l0_pp6.set_slc(77, pp18.slc<2>(77));
  l0_pp6.set_slc(79, pp19.slc<2>(79));
  l0_pp6.set_slc(81, pp20.slc<2>(81));
  l0_pp6.set_slc(83, pp21.slc<2>(83));
  l0_pp6.set_slc(85, pp22.slc<2>(85));
  l0_pp6.set_slc(87, pp23.slc<2>(87));
  l0_pp6.set_slc(89, pp24.slc<2>(89));
  l0_pp6.set_slc(91, pp25.slc<2>(91));
  l0_pp6.set_slc(93, pp26.slc<2>(93));
  l0_pp6.set_slc(95, pp27.slc<2>(95));
  l0_pp6.set_slc(97, pp28.slc<2>(97));

  ui106 l0_pp7 = 0;
  l0_pp7[12] = pp7[12];
  l0_pp7.set_slc(14, pp7.slc<42>(14));
  l0_pp7[56] = pp8[56];
  l0_pp7.set_slc(57, pp9.slc<2>(57));
  l0_pp7.set_slc(59, pp10.slc<2>(59));
  l0_pp7.set_slc(61, pp11.slc<2>(61));
  l0_pp7.set_slc(63, pp12.slc<2>(63));
  l0_pp7.set_slc(65, pp13.slc<2>(65));
  l0_pp7.set_slc(67, pp14.slc<2>(67));
  l0_pp7.set_slc(69, pp15.slc<2>(69));
  l0_pp7.set_slc(71, pp16.slc<2>(71));
  l0_pp7.set_slc(73, pp17.slc<2>(73));
  l0_pp7.set_slc(75, pp18.slc<2>(75));
  l0_pp7.set_slc(77, pp19.slc<2>(77));
  l0_pp7.set_slc(79, pp20.slc<2>(79));
  l0_pp7.set_slc(81, pp21.slc<2>(81));
  l0_pp7.set_slc(83, pp22.slc<2>(83));
  l0_pp7.set_slc(85, pp23.slc<2>(85));
  l0_pp7.set_slc(87, pp24.slc<2>(87));
  l0_pp7.set_slc(89, pp25.slc<2>(89));
  l0_pp7.set_slc(91, pp26.slc<2>(91));
  l0_pp7.set_slc(93, pp27.slc<2>(93));
  l0_pp7.set_slc(95, pp28.slc<2>(95));

  ui106 l0_pp8 = 0;
  l0_pp8[14] = pp8[14];
  l0_pp8.set_slc(16, pp8.slc<40>(16));
  l0_pp8[56] = pp9[56];
  l0_pp8.set_slc(57, pp10.slc<2>(57));
  l0_pp8.set_slc(59, pp11.slc<2>(59));
  l0_pp8.set_slc(61, pp12.slc<2>(61));
  l0_pp8.set_slc(63, pp13.slc<2>(63));
  l0_pp8.set_slc(65, pp14.slc<2>(65));
  l0_pp8.set_slc(67, pp15.slc<2>(67));
  l0_pp8.set_slc(69, pp16.slc<2>(69));
  l0_pp8.set_slc(71, pp17.slc<2>(71));
  l0_pp8.set_slc(73, pp18.slc<2>(73));
  l0_pp8.set_slc(75, pp19.slc<2>(75));
  l0_pp8.set_slc(77, pp20.slc<2>(77));
  l0_pp8.set_slc(79, pp21.slc<2>(79));
  l0_pp8.set_slc(81, pp22.slc<2>(81));
  l0_pp8.set_slc(83, pp23.slc<2>(83));
  l0_pp8.set_slc(85, pp24.slc<2>(85));
  l0_pp8.set_slc(87, pp25.slc<2>(87));
  l0_pp8.set_slc(89, pp26.slc<2>(89));
  l0_pp8.set_slc(91, pp27.slc<2>(91));
  l0_pp8.set_slc(93, pp28.slc<2>(93));

  ui106 l0_pp9 = 0;
  l0_pp9[16] = pp9[16];
  l0_pp9.set_slc(18, pp9.slc<38>(18));
  l0_pp9[56] = pp10[56];
  l0_pp9.set_slc(57, pp11.slc<2>(57));
  l0_pp9.set_slc(59, pp12.slc<2>(59));
  l0_pp9.set_slc(61, pp13.slc<2>(61));
  l0_pp9.set_slc(63, pp14.slc<2>(63));
  l0_pp9.set_slc(65, pp15.slc<2>(65));
  l0_pp9.set_slc(67, pp16.slc<2>(67));
  l0_pp9.set_slc(69, pp17.slc<2>(69));
  l0_pp9.set_slc(71, pp18.slc<2>(71));
  l0_pp9.set_slc(73, pp19.slc<2>(73));
  l0_pp9.set_slc(75, pp20.slc<2>(75));
  l0_pp9.set_slc(77, pp21.slc<2>(77));
  l0_pp9.set_slc(79, pp22.slc<2>(79));
  l0_pp9.set_slc(81, pp23.slc<2>(81));
  l0_pp9.set_slc(83, pp24.slc<2>(83));
  l0_pp9.set_slc(85, pp25.slc<2>(85));
  l0_pp9.set_slc(87, pp26.slc<2>(87));
  l0_pp9.set_slc(89, pp27.slc<2>(89));
  l0_pp9.set_slc(91, pp28.slc<2>(91));

  ui106 l0_pp10 = 0;
  l0_pp10[18] = pp10[18];
  l0_pp10.set_slc(20, pp10.slc<36>(20));
  l0_pp10[56] = pp11[56];
  l0_pp10.set_slc(57, pp12.slc<2>(57));
  l0_pp10.set_slc(59, pp13.slc<2>(59));
  l0_pp10.set_slc(61, pp14.slc<2>(61));
  l0_pp10.set_slc(63, pp15.slc<2>(63));
  l0_pp10.set_slc(65, pp16.slc<2>(65));
  l0_pp10.set_slc(67, pp17.slc<2>(67));
  l0_pp10.set_slc(69, pp18.slc<2>(69));
  l0_pp10.set_slc(71, pp19.slc<2>(71));
  l0_pp10.set_slc(73, pp20.slc<2>(73));
  l0_pp10.set_slc(75, pp21.slc<2>(75));
  l0_pp10.set_slc(77, pp22.slc<2>(77));
  l0_pp10.set_slc(79, pp23.slc<2>(79));
  l0_pp10.set_slc(81, pp24.slc<2>(81));
  l0_pp10.set_slc(83, pp25.slc<2>(83));
  l0_pp10.set_slc(85, pp26.slc<2>(85));
  l0_pp10.set_slc(87, pp27.slc<2>(87));
  l0_pp10.set_slc(89, pp28.slc<2>(89));

  ui106 l0_pp11 = 0;
  l0_pp11[20] = pp11[20];
  l0_pp11.set_slc(22, pp11.slc<34>(22));
  l0_pp11[56] = pp12[56];
  l0_pp11.set_slc(57, pp13.slc<2>(57));
  l0_pp11.set_slc(59, pp14.slc<2>(59));
  l0_pp11.set_slc(61, pp15.slc<2>(61));
  l0_pp11.set_slc(63, pp16.slc<2>(63));
  l0_pp11.set_slc(65, pp17.slc<2>(65));
  l0_pp11.set_slc(67, pp18.slc<2>(67));
  l0_pp11.set_slc(69, pp19.slc<2>(69));
  l0_pp11.set_slc(71, pp20.slc<2>(71));
  l0_pp11.set_slc(73, pp21.slc<2>(73));
  l0_pp11.set_slc(75, pp22.slc<2>(75));
  l0_pp11.set_slc(77, pp23.slc<2>(77));
  l0_pp11.set_slc(79, pp24.slc<2>(79));
  l0_pp11.set_slc(81, pp25.slc<2>(81));
  l0_pp11.set_slc(83, pp26.slc<2>(83));
  l0_pp11.set_slc(85, pp27.slc<2>(85));
  l0_pp11.set_slc(87, pp28.slc<2>(87));

  ui106 l0_pp12 = 0;
  l0_pp12[22] = pp12[22];
  l0_pp12.set_slc(24, pp12.slc<32>(24));
  l0_pp12[56] = pp13[56];
  l0_pp12.set_slc(57, pp14.slc<2>(57));
  l0_pp12.set_slc(59, pp15.slc<2>(59));
  l0_pp12.set_slc(61, pp16.slc<2>(61));
  l0_pp12.set_slc(63, pp17.slc<2>(63));
  l0_pp12.set_slc(65, pp18.slc<2>(65));
  l0_pp12.set_slc(67, pp19.slc<2>(67));
  l0_pp12.set_slc(69, pp20.slc<2>(69));
  l0_pp12.set_slc(71, pp21.slc<2>(71));
  l0_pp12.set_slc(73, pp22.slc<2>(73));
  l0_pp12.set_slc(75, pp23.slc<2>(75));
  l0_pp12.set_slc(77, pp24.slc<2>(77));
  l0_pp12.set_slc(79, pp25.slc<2>(79));
  l0_pp12.set_slc(81, pp26.slc<2>(81));
  l0_pp12.set_slc(83, pp27.slc<2>(83));
  l0_pp12.set_slc(85, pp28.slc<2>(85));

  ui106 l0_pp13 = 0;
  l0_pp13[24] = pp13[24];
  l0_pp13.set_slc(26, pp13.slc<30>(26));
  l0_pp13[56] = pp14[56];
  l0_pp13.set_slc(57, pp15.slc<2>(57));
  l0_pp13.set_slc(59, pp16.slc<2>(59));
  l0_pp13.set_slc(61, pp17.slc<2>(61));
  l0_pp13.set_slc(63, pp18.slc<2>(63));
  l0_pp13.set_slc(65, pp19.slc<2>(65));
  l0_pp13.set_slc(67, pp20.slc<2>(67));
  l0_pp13.set_slc(69, pp21.slc<2>(69));
  l0_pp13.set_slc(71, pp22.slc<2>(71));
  l0_pp13.set_slc(73, pp23.slc<2>(73));
  l0_pp13.set_slc(75, pp24.slc<2>(75));
  l0_pp13.set_slc(77, pp25.slc<2>(77));
  l0_pp13.set_slc(79, pp26.slc<2>(79));
  l0_pp13.set_slc(81, pp27.slc<2>(81));
  l0_pp13.set_slc(83, pp28.slc<2>(83));

  ui106 l0_pp14 = 0;
  l0_pp14[26] = pp14[26];
  l0_pp14.set_slc(28, pp14.slc<28>(28));
  l0_pp14[56] = pp15[56];
  l0_pp14.set_slc(57, pp16.slc<2>(57));
  l0_pp14.set_slc(59, pp17.slc<2>(59));
  l0_pp14.set_slc(61, pp18.slc<2>(61));
  l0_pp14.set_slc(63, pp19.slc<2>(63));
  l0_pp14.set_slc(65, pp20.slc<2>(65));
  l0_pp14.set_slc(67, pp21.slc<2>(67));
  l0_pp14.set_slc(69, pp22.slc<2>(69));
  l0_pp14.set_slc(71, pp23.slc<2>(71));
  l0_pp14.set_slc(73, pp24.slc<2>(73));
  l0_pp14.set_slc(75, pp25.slc<2>(75));
  l0_pp14.set_slc(77, pp26.slc<2>(77));
  l0_pp14.set_slc(79, pp27.slc<2>(79));
  l0_pp14.set_slc(81, pp28.slc<2>(81));

  ui106 l0_pp15 = 0;
  l0_pp15[28] = pp15[28];
  l0_pp15.set_slc(30, pp15.slc<26>(30));
  l0_pp15[56] = pp16[56];
  l0_pp15.set_slc(57, pp17.slc<2>(57));
  l0_pp15.set_slc(59, pp18.slc<2>(59));
  l0_pp15.set_slc(61, pp19.slc<2>(61));
  l0_pp15.set_slc(63, pp20.slc<2>(63));
  l0_pp15.set_slc(65, pp21.slc<2>(65));
  l0_pp15.set_slc(67, pp22.slc<2>(67));
  l0_pp15.set_slc(69, pp23.slc<2>(69));
  l0_pp15.set_slc(71, pp24.slc<2>(71));
  l0_pp15.set_slc(73, pp25.slc<2>(73));
  l0_pp15.set_slc(75, pp26.slc<2>(75));
  l0_pp15.set_slc(77, pp27.slc<2>(77));
  l0_pp15.set_slc(79, pp28.slc<2>(79));

  ui106 l0_pp16 = 0;
  l0_pp16[30] = pp16[30];
  l0_pp16.set_slc(32, pp16.slc<24>(32));
  l0_pp16[56] = pp17[56];
  l0_pp16.set_slc(57, pp18.slc<2>(57));
  l0_pp16.set_slc(59, pp19.slc<2>(59));
  l0_pp16.set_slc(61, pp20.slc<2>(61));
  l0_pp16.set_slc(63, pp21.slc<2>(63));
  l0_pp16.set_slc(65, pp22.slc<2>(65));
  l0_pp16.set_slc(67, pp23.slc<2>(67));
  l0_pp16.set_slc(69, pp24.slc<2>(69));
  l0_pp16.set_slc(71, pp25.slc<2>(71));
  l0_pp16.set_slc(73, pp26.slc<2>(73));
  l0_pp16.set_slc(75, pp27.slc<2>(75));
  l0_pp16.set_slc(77, pp28.slc<2>(77));

  ui106 l0_pp17 = 0;
  l0_pp17[32] = pp17[32];
  l0_pp17.set_slc(34, pp17.slc<22>(34));
  l0_pp17[56] = pp18[56];
  l0_pp17.set_slc(57, pp19.slc<2>(57));
  l0_pp17.set_slc(59, pp20.slc<2>(59));
  l0_pp17.set_slc(61, pp21.slc<2>(61));
  l0_pp17.set_slc(63, pp22.slc<2>(63));
  l0_pp17.set_slc(65, pp23.slc<2>(65));
  l0_pp17.set_slc(67, pp24.slc<2>(67));
  l0_pp17.set_slc(69, pp25.slc<2>(69));
  l0_pp17.set_slc(71, pp26.slc<2>(71));
  l0_pp17.set_slc(73, pp27.slc<2>(73));
  l0_pp17.set_slc(75, pp28.slc<2>(75));

  ui106 l0_pp18 = 0;
  l0_pp18[34] = pp18[34];
  l0_pp18.set_slc(36, pp18.slc<20>(36));
  l0_pp18[56] = pp19[56];
  l0_pp18.set_slc(57, pp20.slc<2>(57));
  l0_pp18.set_slc(59, pp21.slc<2>(59));
  l0_pp18.set_slc(61, pp22.slc<2>(61));
  l0_pp18.set_slc(63, pp23.slc<2>(63));
  l0_pp18.set_slc(65, pp24.slc<2>(65));
  l0_pp18.set_slc(67, pp25.slc<2>(67));
  l0_pp18.set_slc(69, pp26.slc<2>(69));
  l0_pp18.set_slc(71, pp27.slc<2>(71));
  l0_pp18.set_slc(73, pp28.slc<2>(73));

  ui106 l0_pp19 = 0;
  l0_pp19[36] = pp19[36];
  l0_pp19.set_slc(38, pp19.slc<18>(38));
  l0_pp19[56] = pp20[56];
  l0_pp19.set_slc(57, pp21.slc<2>(57));
  l0_pp19.set_slc(59, pp22.slc<2>(59));
  l0_pp19.set_slc(61, pp23.slc<2>(61));
  l0_pp19.set_slc(63, pp24.slc<2>(63));
  l0_pp19.set_slc(65, pp25.slc<2>(65));
  l0_pp19.set_slc(67, pp26.slc<2>(67));
  l0_pp19.set_slc(69, pp27.slc<2>(69));
  l0_pp19.set_slc(71, pp28.slc<2>(71));

  ui106 l0_pp20 = 0;
  l0_pp20[38] = pp20[38];
  l0_pp20.set_slc(40, pp20.slc<16>(40));
  l0_pp20[56] = pp21[56];
  l0_pp20.set_slc(57, pp22.slc<2>(57));
  l0_pp20.set_slc(59, pp23.slc<2>(59));
  l0_pp20.set_slc(61, pp24.slc<2>(61));
  l0_pp20.set_slc(63, pp25.slc<2>(63));
  l0_pp20.set_slc(65, pp26.slc<2>(65));
  l0_pp20.set_slc(67, pp27.slc<2>(67));
  l0_pp20.set_slc(69, pp28.slc<2>(69));

  ui106 l0_pp21 = 0;
  l0_pp21[40] = pp21[40];
  l0_pp21.set_slc(42, pp21.slc<14>(42));
  l0_pp21[56] = pp22[56];
  l0_pp21.set_slc(57, pp23.slc<2>(57));
  l0_pp21.set_slc(59, pp24.slc<2>(59));
  l0_pp21.set_slc(61, pp25.slc<2>(61));
  l0_pp21.set_slc(63, pp26.slc<2>(63));
  l0_pp21.set_slc(65, pp27.slc<2>(65));
  l0_pp21.set_slc(67, pp28.slc<2>(67));

  ui106 l0_pp22 = 0;
  l0_pp22[42] = pp22[42];
  l0_pp22.set_slc(44, pp22.slc<12>(44));
  l0_pp22[56] = pp23[56];
  l0_pp22.set_slc(57, pp24.slc<2>(57));
  l0_pp22.set_slc(59, pp25.slc<2>(59));
  l0_pp22.set_slc(61, pp26.slc<2>(61));
  l0_pp22.set_slc(63, pp27.slc<2>(63));
  l0_pp22.set_slc(65, pp28.slc<2>(65));

  ui106 l0_pp23 = 0;
  l0_pp23[44] = pp23[44];
  l0_pp23.set_slc(46, pp23.slc<10>(46));
  l0_pp23[56] = pp24[56];
  l0_pp23.set_slc(57, pp25.slc<2>(57));
  l0_pp23.set_slc(59, pp26.slc<2>(59));
  l0_pp23.set_slc(61, pp27.slc<2>(61));
  l0_pp23.set_slc(63, pp28.slc<2>(63));

  ui106 l0_pp24 = 0;
  l0_pp24[46] = pp24[46];
  l0_pp24.set_slc(48, pp24.slc<8>(48));
  l0_pp24[56] = pp25[56];
  l0_pp24.set_slc(57, pp26.slc<2>(57));
  l0_pp24.set_slc(59, pp27.slc<2>(59));
  l0_pp24.set_slc(61, pp28.slc<2>(61));

  ui106 l0_pp25 = 0;
  l0_pp25[48] = pp25[48];
  l0_pp25.set_slc(50, pp25.slc<6>(50));
  l0_pp25[56] = pp26[56];
  l0_pp25.set_slc(57, pp27.slc<2>(57));
  l0_pp25.set_slc(59, pp28.slc<2>(59));

  ui106 l0_pp26 = 0;
  l0_pp26[50] = pp26[50];
  l0_pp26.set_slc(52, pp26.slc<4>(52));
  l0_pp26[56] = pp27[56];
  l0_pp26.set_slc(57, pp28.slc<2>(57));

  ui106 l0_pp27 = 0;
  l0_pp27.set_slc(52, pp27.slc<4>(52));
  l0_pp27[56] = pp28[56];

  ui106 l0_pp28 = 0;
  l0_pp28.set_slc(52, pp28.slc<4>(52));


  // Max bit column depth after Dadda level #0 is 28
  ui106 l0_pp0to2_s = 0, l0_pp0to2_c = 0;
  l0_pp0to2_s[52] = l0_pp0[52] ^ l0_pp1[52];
  l0_pp0to2_c[53] = l0_pp0[52] & l0_pp1[52];
  l0_pp0to2_s.set_slc(53, ui3(l0_pp0.slc<3>(53) ^ l0_pp1.slc<3>(53) ^ l0_pp2.slc<3>(53)));
  l0_pp0to2_c.set_slc(54, ui3(l0_pp0.slc<3>(53) & l0_pp1.slc<3>(53) | l0_pp0.slc<3>(53) & l0_pp2.slc<3>(53) | l0_pp1.slc<3>(53) & l0_pp2.slc<3>(53)));
  l0_pp0to2_s[56] = l0_pp0[56] ^ l0_pp1[56];
  l0_pp0to2_c[57] = l0_pp0[56] & l0_pp1[56];

  // Dadda level 1 beginning dot diagram:
  // 111111
  // 000000999999999988888888887777777777666666666655555555554444444444333333333322222222221111111111
  // 5432109876543210987654321098765432109876543210987654321098765432109876543210987654321098765432109876543210
  // ********************************************************************************************************
  //  *******************************************************************************************************
  //  ***************************************************************************************************** *
  //   ************************************************************************************************** *
  //    *********************************************************************************************** *
  //      ******************************************************************************************* *
  //        *************************************************************************************** *
  //          *********************************************************************************** *
  //            ******************************************************************************* *
  //              *************************************************************************** *
  //                *********************************************************************** *
  //                  ******************************************************************* *
  //                    *************************************************************** *
  //                      *********************************************************** *
  //                        ******************************************************* *
  //                          *************************************************** *
  //                            *********************************************** *
  //                              ******************************************* *
  //                                *************************************** *
  //                                  *********************************** *
  //                                    ******************************* *
  //                                      *************************** *
  //                                        *********************** *
  //                                          ******************* *
  //                                            *************** *
  //                                              *********** *
  //                                                ******* *
  //                                                 ******

  ui106 l1_pp0 = 0;
  l1_pp0.set_slc(2, l0_pp0.slc<50>(2));
  l1_pp0[52] = l0_pp2[52];
  l1_pp0.set_slc(53, l0_pp3.slc<3>(53));
  l1_pp0[56] = l0_pp2[56];
  l1_pp0.set_slc(57, l0_pp0.slc<49>(57));

  ui106 l1_pp1 = 0;
  l1_pp1.set_slc(2, l0_pp1.slc<50>(2));
  l1_pp1[52] = l0_pp3[52];
  l1_pp1.set_slc(53, l0_pp4.slc<3>(53));
  l1_pp1[56] = l0_pp3[56];
  l1_pp1.set_slc(57, l0_pp1.slc<48>(57));

  ui106 l1_pp2 = 0;
  l1_pp2[2] = l0_pp2[2];
  l1_pp2.set_slc(4, l0_pp2.slc<48>(4));
  l1_pp2[52] = l0_pp4[52];
  l1_pp2.set_slc(53, l0_pp5.slc<3>(53));
  l1_pp2[56] = l0_pp4[56];
  l1_pp2.set_slc(57, l0_pp2.slc<48>(57));

  ui106 l1_pp3 = 0;
  l1_pp3[4] = l0_pp3[4];
  l1_pp3.set_slc(6, l0_pp3.slc<46>(6));
  l1_pp3[52] = l0_pp5[52];
  l1_pp3.set_slc(53, l0_pp6.slc<3>(53));
  l1_pp3[56] = l0_pp5[56];
  l1_pp3.set_slc(57, l0_pp3.slc<47>(57));

  ui106 l1_pp4 = 0;
  l1_pp4[6] = l0_pp4[6];
  l1_pp4.set_slc(8, l0_pp4.slc<44>(8));
  l1_pp4[52] = l0_pp6[52];
  l1_pp4.set_slc(53, l0_pp7.slc<3>(53));
  l1_pp4[56] = l0_pp6[56];
  l1_pp4.set_slc(57, l0_pp4.slc<46>(57));

  ui106 l1_pp5 = 0;
  l1_pp5[8] = l0_pp5[8];
  l1_pp5.set_slc(10, l0_pp5.slc<42>(10));
  l1_pp5[52] = l0_pp7[52];
  l1_pp5.set_slc(53, l0_pp8.slc<3>(53));
  l1_pp5[56] = l0_pp7[56];
  l1_pp5.set_slc(57, l0_pp5.slc<44>(57));

  ui106 l1_pp6 = 0;
  l1_pp6[10] = l0_pp6[10];
  l1_pp6.set_slc(12, l0_pp6.slc<40>(12));
  l1_pp6[52] = l0_pp8[52];
  l1_pp6.set_slc(53, l0_pp9.slc<3>(53));
  l1_pp6[56] = l0_pp8[56];
  l1_pp6.set_slc(57, l0_pp6.slc<42>(57));

  ui106 l1_pp7 = 0;
  l1_pp7[12] = l0_pp7[12];
  l1_pp7.set_slc(14, l0_pp7.slc<38>(14));
  l1_pp7[52] = l0_pp9[52];
  l1_pp7.set_slc(53, l0_pp10.slc<3>(53));
  l1_pp7[56] = l0_pp9[56];
  l1_pp7.set_slc(57, l0_pp7.slc<40>(57));

  ui106 l1_pp8 = 0;
  l1_pp8[14] = l0_pp8[14];
  l1_pp8.set_slc(16, l0_pp8.slc<36>(16));
  l1_pp8[52] = l0_pp10[52];
  l1_pp8.set_slc(53, l0_pp11.slc<3>(53));
  l1_pp8[56] = l0_pp10[56];
  l1_pp8.set_slc(57, l0_pp8.slc<38>(57));

  ui106 l1_pp9 = 0;
  l1_pp9[16] = l0_pp9[16];
  l1_pp9.set_slc(18, l0_pp9.slc<34>(18));
  l1_pp9[52] = l0_pp11[52];
  l1_pp9.set_slc(53, l0_pp12.slc<3>(53));
  l1_pp9[56] = l0_pp11[56];
  l1_pp9.set_slc(57, l0_pp9.slc<36>(57));

  ui106 l1_pp10 = 0;
  l1_pp10[18] = l0_pp10[18];
  l1_pp10.set_slc(20, l0_pp10.slc<32>(20));
  l1_pp10[52] = l0_pp12[52];
  l1_pp10.set_slc(53, l0_pp13.slc<3>(53));
  l1_pp10[56] = l0_pp12[56];
  l1_pp10.set_slc(57, l0_pp10.slc<34>(57));

  ui106 l1_pp11 = 0;
  l1_pp11[20] = l0_pp11[20];
  l1_pp11.set_slc(22, l0_pp11.slc<30>(22));
  l1_pp11[52] = l0_pp13[52];
  l1_pp11.set_slc(53, l0_pp14.slc<3>(53));
  l1_pp11[56] = l0_pp13[56];
  l1_pp11.set_slc(57, l0_pp11.slc<32>(57));

  ui106 l1_pp12 = 0;
  l1_pp12[22] = l0_pp12[22];
  l1_pp12.set_slc(24, l0_pp12.slc<28>(24));
  l1_pp12[52] = l0_pp14[52];
  l1_pp12.set_slc(53, l0_pp15.slc<3>(53));
  l1_pp12[56] = l0_pp14[56];
  l1_pp12.set_slc(57, l0_pp12.slc<30>(57));

  ui106 l1_pp13 = 0;
  l1_pp13[24] = l0_pp13[24];
  l1_pp13.set_slc(26, l0_pp13.slc<26>(26));
  l1_pp13[52] = l0_pp15[52];
  l1_pp13.set_slc(53, l0_pp16.slc<3>(53));
  l1_pp13[56] = l0_pp15[56];
  l1_pp13.set_slc(57, l0_pp13.slc<28>(57));

  ui106 l1_pp14 = 0;
  l1_pp14[26] = l0_pp14[26];
  l1_pp14.set_slc(28, l0_pp14.slc<24>(28));
  l1_pp14[52] = l0_pp16[52];
  l1_pp14.set_slc(53, l0_pp17.slc<3>(53));
  l1_pp14[56] = l0_pp16[56];
  l1_pp14.set_slc(57, l0_pp14.slc<26>(57));

  ui106 l1_pp15 = 0;
  l1_pp15[28] = l0_pp15[28];
  l1_pp15.set_slc(30, l0_pp15.slc<22>(30));
  l1_pp15[52] = l0_pp17[52];
  l1_pp15.set_slc(53, l0_pp18.slc<3>(53));
  l1_pp15[56] = l0_pp17[56];
  l1_pp15.set_slc(57, l0_pp15.slc<24>(57));

  ui106 l1_pp16 = 0;
  l1_pp16[30] = l0_pp16[30];
  l1_pp16.set_slc(32, l0_pp16.slc<20>(32));
  l1_pp16[52] = l0_pp18[52];
  l1_pp16.set_slc(53, l0_pp19.slc<3>(53));
  l1_pp16[56] = l0_pp18[56];
  l1_pp16.set_slc(57, l0_pp16.slc<22>(57));

  ui106 l1_pp17 = 0;
  l1_pp17[32] = l0_pp17[32];
  l1_pp17.set_slc(34, l0_pp17.slc<18>(34));
  l1_pp17[52] = l0_pp19[52];
  l1_pp17.set_slc(53, l0_pp20.slc<3>(53));
  l1_pp17[56] = l0_pp19[56];
  l1_pp17.set_slc(57, l0_pp17.slc<20>(57));

  ui106 l1_pp18 = 0;
  l1_pp18[34] = l0_pp18[34];
  l1_pp18.set_slc(36, l0_pp18.slc<16>(36));
  l1_pp18[52] = l0_pp20[52];
  l1_pp18.set_slc(53, l0_pp21.slc<3>(53));
  l1_pp18[56] = l0_pp20[56];
  l1_pp18.set_slc(57, l0_pp18.slc<18>(57));

  ui106 l1_pp19 = 0;
  l1_pp19[36] = l0_pp19[36];
  l1_pp19.set_slc(38, l0_pp19.slc<14>(38));
  l1_pp19[52] = l0_pp21[52];
  l1_pp19.set_slc(53, l0_pp22.slc<3>(53));
  l1_pp19[56] = l0_pp21[56];
  l1_pp19.set_slc(57, l0_pp19.slc<16>(57));

  ui106 l1_pp20 = 0;
  l1_pp20[38] = l0_pp20[38];
  l1_pp20.set_slc(40, l0_pp20.slc<12>(40));
  l1_pp20[52] = l0_pp22[52];
  l1_pp20.set_slc(53, l0_pp23.slc<3>(53));
  l1_pp20[56] = l0_pp22[56];
  l1_pp20.set_slc(57, l0_pp20.slc<14>(57));

  ui106 l1_pp21 = 0;
  l1_pp21[40] = l0_pp21[40];
  l1_pp21.set_slc(42, l0_pp21.slc<10>(42));
  l1_pp21[52] = l0_pp23[52];
  l1_pp21.set_slc(53, l0_pp24.slc<3>(53));
  l1_pp21[56] = l0_pp23[56];
  l1_pp21.set_slc(57, l0_pp21.slc<12>(57));

  ui106 l1_pp22 = 0;
  l1_pp22[42] = l0_pp22[42];
  l1_pp22.set_slc(44, l0_pp22.slc<8>(44));
  l1_pp22[52] = l0_pp24[52];
  l1_pp22.set_slc(53, l0_pp25.slc<3>(53));
  l1_pp22[56] = l0_pp24[56];
  l1_pp22.set_slc(57, l0_pp22.slc<10>(57));

  ui106 l1_pp23 = 0;
  l1_pp23[44] = l0_pp23[44];
  l1_pp23.set_slc(46, l0_pp23.slc<6>(46));
  l1_pp23[52] = l0_pp25[52];
  l1_pp23.set_slc(53, l0_pp26.slc<3>(53));
  l1_pp23[56] = l0_pp25[56];
  l1_pp23.set_slc(57, l0_pp23.slc<8>(57));

  ui106 l1_pp24 = 0;
  l1_pp24[46] = l0_pp24[46];
  l1_pp24.set_slc(48, l0_pp24.slc<4>(48));
  l1_pp24[52] = l0_pp26[52];
  l1_pp24.set_slc(53, l0_pp27.slc<3>(53));
  l1_pp24[56] = l0_pp26[56];
  l1_pp24.set_slc(57, l0_pp24.slc<6>(57));

  ui106 l1_pp25 = 0;
  l1_pp25[48] = l0_pp25[48];
  l1_pp25.set_slc(50, l0_pp25.slc<2>(50));
  l1_pp25[52] = l0_pp27[52];
  l1_pp25.set_slc(53, l0_pp28.slc<3>(53));
  l1_pp25[56] = l0_pp27[56];
  l1_pp25.set_slc(57, l0_pp25.slc<4>(57));

  ui106 l1_pp26 = 0;
  l1_pp26[50] = l0_pp26[50];
  l1_pp26[52] = l0_pp28[52];
  l1_pp26.set_slc(53, l0_pp0to2_c.slc<4>(53));
  l1_pp26.set_slc(57, l0_pp26.slc<2>(57));

  ui106 l1_pp27 = 0;
  l1_pp27.set_slc(52, l0_pp0to2_s.slc<5>(52));
  l1_pp27[57] = l0_pp0to2_c[57];


  // Max bit column depth after Dadda level #1 is 19
  ui106 l1_pp0to2_s = 0, l1_pp0to2_c = 0;
  l1_pp0to2_s.set_slc(36, ui2(l1_pp0.slc<2>(36) ^ l1_pp1.slc<2>(36)));
  l1_pp0to2_c.set_slc(37, ui2(l1_pp0.slc<2>(36) & l1_pp1.slc<2>(36)));
  l1_pp0to2_s.set_slc(38, ui36(l1_pp0.slc<36>(38) ^ l1_pp1.slc<36>(38) ^ l1_pp2.slc<36>(38)));
  l1_pp0to2_c.set_slc(39, ui36(l1_pp0.slc<36>(38) & l1_pp1.slc<36>(38) | l1_pp0.slc<36>(38) & l1_pp2.slc<36>(38) | l1_pp1.slc<36>(38) & l1_pp2.slc<36>(38)));
  l1_pp0to2_s[74] = l1_pp0[74] ^ l1_pp1[74];
  l1_pp0to2_c[75] = l1_pp0[74] & l1_pp1[74];
  ui106 l1_pp3to5_s = 0, l1_pp3to5_c = 0;
  l1_pp3to5_s.set_slc(38, ui2(l1_pp3.slc<2>(38) ^ l1_pp4.slc<2>(38)));
  l1_pp3to5_c.set_slc(39, ui2(l1_pp3.slc<2>(38) & l1_pp4.slc<2>(38)));
  l1_pp3to5_s.set_slc(40, ui32(l1_pp3.slc<32>(40) ^ l1_pp4.slc<32>(40) ^ l1_pp5.slc<32>(40)));
  l1_pp3to5_c.set_slc(41, ui32(l1_pp3.slc<32>(40) & l1_pp4.slc<32>(40) | l1_pp3.slc<32>(40) & l1_pp5.slc<32>(40) | l1_pp4.slc<32>(40) & l1_pp5.slc<32>(40)));
  l1_pp3to5_s[72] = l1_pp3[72] ^ l1_pp4[72];
  l1_pp3to5_c[73] = l1_pp3[72] & l1_pp4[72];
  ui106 l1_pp6to8_s = 0, l1_pp6to8_c = 0;
  l1_pp6to8_s.set_slc(40, ui2(l1_pp6.slc<2>(40) ^ l1_pp7.slc<2>(40)));
  l1_pp6to8_c.set_slc(41, ui2(l1_pp6.slc<2>(40) & l1_pp7.slc<2>(40)));
  l1_pp6to8_s.set_slc(42, ui28(l1_pp6.slc<28>(42) ^ l1_pp7.slc<28>(42) ^ l1_pp8.slc<28>(42)));
  l1_pp6to8_c.set_slc(43, ui28(l1_pp6.slc<28>(42) & l1_pp7.slc<28>(42) | l1_pp6.slc<28>(42) & l1_pp8.slc<28>(42) | l1_pp7.slc<28>(42) & l1_pp8.slc<28>(42)));
  l1_pp6to8_s[70] = l1_pp6[70] ^ l1_pp7[70];
  l1_pp6to8_c[71] = l1_pp6[70] & l1_pp7[70];
  ui106 l1_pp9to11_s = 0, l1_pp9to11_c = 0;
  l1_pp9to11_s.set_slc(42, ui2(l1_pp9.slc<2>(42) ^ l1_pp10.slc<2>(42)));
  l1_pp9to11_c.set_slc(43, ui2(l1_pp9.slc<2>(42) & l1_pp10.slc<2>(42)));
  l1_pp9to11_s.set_slc(44, ui24(l1_pp9.slc<24>(44) ^ l1_pp10.slc<24>(44) ^ l1_pp11.slc<24>(44)));
  l1_pp9to11_c.set_slc(45, ui24(l1_pp9.slc<24>(44) & l1_pp10.slc<24>(44) | l1_pp9.slc<24>(44) & l1_pp11.slc<24>(44) | l1_pp10.slc<24>(44) & l1_pp11.slc<24>(44)));
  l1_pp9to11_s[68] = l1_pp9[68] ^ l1_pp10[68];
  l1_pp9to11_c[69] = l1_pp9[68] & l1_pp10[68];
  ui106 l1_pp12to14_s = 0, l1_pp12to14_c = 0;
  l1_pp12to14_s.set_slc(44, ui2(l1_pp12.slc<2>(44) ^ l1_pp13.slc<2>(44)));
  l1_pp12to14_c.set_slc(45, ui2(l1_pp12.slc<2>(44) & l1_pp13.slc<2>(44)));
  l1_pp12to14_s.set_slc(46, ui20(l1_pp12.slc<20>(46) ^ l1_pp13.slc<20>(46) ^ l1_pp14.slc<20>(46)));
  l1_pp12to14_c.set_slc(47, ui20(l1_pp12.slc<20>(46) & l1_pp13.slc<20>(46) | l1_pp12.slc<20>(46) & l1_pp14.slc<20>(46) | l1_pp13.slc<20>(46) & l1_pp14.slc<20>(46)));
  l1_pp12to14_s[66] = l1_pp12[66] ^ l1_pp13[66];
  l1_pp12to14_c[67] = l1_pp12[66] & l1_pp13[66];
  ui106 l1_pp15to17_s = 0, l1_pp15to17_c = 0;
  l1_pp15to17_s.set_slc(46, ui2(l1_pp15.slc<2>(46) ^ l1_pp16.slc<2>(46)));
  l1_pp15to17_c.set_slc(47, ui2(l1_pp15.slc<2>(46) & l1_pp16.slc<2>(46)));
  l1_pp15to17_s.set_slc(48, ui16(l1_pp15.slc<16>(48) ^ l1_pp16.slc<16>(48) ^ l1_pp17.slc<16>(48)));
  l1_pp15to17_c.set_slc(49, ui16(l1_pp15.slc<16>(48) & l1_pp16.slc<16>(48) | l1_pp15.slc<16>(48) & l1_pp17.slc<16>(48) | l1_pp16.slc<16>(48) & l1_pp17.slc<16>(48)));
  l1_pp15to17_s[64] = l1_pp15[64] ^ l1_pp16[64];
  l1_pp15to17_c[65] = l1_pp15[64] & l1_pp16[64];
  ui106 l1_pp18to20_s = 0, l1_pp18to20_c = 0;
  l1_pp18to20_s.set_slc(48, ui2(l1_pp18.slc<2>(48) ^ l1_pp19.slc<2>(48)));
  l1_pp18to20_c.set_slc(49, ui2(l1_pp18.slc<2>(48) & l1_pp19.slc<2>(48)));
  l1_pp18to20_s.set_slc(50, ui12(l1_pp18.slc<12>(50) ^ l1_pp19.slc<12>(50) ^ l1_pp20.slc<12>(50)));
  l1_pp18to20_c.set_slc(51, ui12(l1_pp18.slc<12>(50) & l1_pp19.slc<12>(50) | l1_pp18.slc<12>(50) & l1_pp20.slc<12>(50) | l1_pp19.slc<12>(50) & l1_pp20.slc<12>(50)));
  l1_pp18to20_s[62] = l1_pp18[62] ^ l1_pp19[62];
  l1_pp18to20_c[63] = l1_pp18[62] & l1_pp19[62];
  ui106 l1_pp21to23_s = 0, l1_pp21to23_c = 0;
  l1_pp21to23_s.set_slc(50, ui2(l1_pp21.slc<2>(50) ^ l1_pp22.slc<2>(50)));
  l1_pp21to23_c.set_slc(51, ui2(l1_pp21.slc<2>(50) & l1_pp22.slc<2>(50)));
  l1_pp21to23_s.set_slc(52, ui8(l1_pp21.slc<8>(52) ^ l1_pp22.slc<8>(52) ^ l1_pp23.slc<8>(52)));
  l1_pp21to23_c.set_slc(53, ui8(l1_pp21.slc<8>(52) & l1_pp22.slc<8>(52) | l1_pp21.slc<8>(52) & l1_pp23.slc<8>(52) | l1_pp22.slc<8>(52) & l1_pp23.slc<8>(52)));
  l1_pp21to23_s[60] = l1_pp21[60] ^ l1_pp22[60];
  l1_pp21to23_c[61] = l1_pp21[60] & l1_pp22[60];
  ui106 l1_pp24to26_s = 0, l1_pp24to26_c = 0;
  l1_pp24to26_s[52] = l1_pp24[52] ^ l1_pp25[52];
  l1_pp24to26_c[53] = l1_pp24[52] & l1_pp25[52];
  l1_pp24to26_s.set_slc(53, ui5(l1_pp24.slc<5>(53) ^ l1_pp25.slc<5>(53) ^ l1_pp26.slc<5>(53)));
  l1_pp24to26_c.set_slc(54, ui5(l1_pp24.slc<5>(53) & l1_pp25.slc<5>(53) | l1_pp24.slc<5>(53) & l1_pp26.slc<5>(53) | l1_pp25.slc<5>(53) & l1_pp26.slc<5>(53)));
  l1_pp24to26_s[58] = l1_pp24[58] ^ l1_pp25[58];
  l1_pp24to26_c[59] = l1_pp24[58] & l1_pp25[58];

  // Dadda level 2 beginning dot diagram:
  // 111111
  // 000000999999999988888888887777777777666666666655555555554444444444333333333322222222221111111111
  // 5432109876543210987654321098765432109876543210987654321098765432109876543210987654321098765432109876543210
  // ********************************************************************************************************
  //  *******************************************************************************************************
  //  ***************************************************************************************************** *
  //   ************************************************************************************************** *
  //    *********************************************************************************************** *
  //      ******************************************************************************************* *
  //        *************************************************************************************** *
  //          *********************************************************************************** *
  //            ******************************************************************************* *
  //              *************************************************************************** *
  //                *********************************************************************** *
  //                  ******************************************************************* *
  //                    *************************************************************** *
  //                      *********************************************************** *
  //                        ******************************************************* *
  //                          *************************************************** *
  //                            *********************************************** *
  //                              ******************************************* *
  //                               **************************************** *

  ui106 l2_pp0 = 0;
  l2_pp0.set_slc(2, l1_pp0.slc<34>(2));
  l2_pp0.set_slc(36, l1_pp2.slc<2>(36));
  l2_pp0.set_slc(38, l1_pp5.slc<2>(38));
  l2_pp0.set_slc(40, l1_pp8.slc<2>(40));
  l2_pp0.set_slc(42, l1_pp11.slc<2>(42));
  l2_pp0.set_slc(44, l1_pp14.slc<2>(44));
  l2_pp0.set_slc(46, l1_pp17.slc<2>(46));
  l2_pp0.set_slc(48, l1_pp20.slc<2>(48));
  l2_pp0.set_slc(50, l1_pp23.slc<2>(50));
  l2_pp0[52] = l1_pp26[52];
  l2_pp0.set_slc(53, l1_pp27.slc<5>(53));
  l2_pp0[58] = l1_pp26[58];
  l2_pp0[59] = l1_pp24[59];
  l2_pp0[60] = l1_pp23[60];
  l2_pp0[61] = l1_pp21[61];
  l2_pp0[62] = l1_pp20[62];
  l2_pp0[63] = l1_pp18[63];
  l2_pp0[64] = l1_pp17[64];
  l2_pp0[65] = l1_pp15[65];
  l2_pp0[66] = l1_pp14[66];
  l2_pp0[67] = l1_pp12[67];
  l2_pp0[68] = l1_pp11[68];
  l2_pp0[69] = l1_pp9[69];
  l2_pp0[70] = l1_pp8[70];
  l2_pp0[71] = l1_pp6[71];
  l2_pp0[72] = l1_pp5[72];
  l2_pp0[73] = l1_pp3[73];
  l2_pp0[74] = l1_pp2[74];
  l2_pp0.set_slc(75, l1_pp0.slc<31>(75));

  ui106 l2_pp1 = 0;
  l2_pp1.set_slc(2, l1_pp1.slc<34>(2));
  l2_pp1.set_slc(36, l1_pp3.slc<2>(36));
  l2_pp1.set_slc(38, l1_pp6.slc<2>(38));
  l2_pp1.set_slc(40, l1_pp9.slc<2>(40));
  l2_pp1.set_slc(42, l1_pp12.slc<2>(42));
  l2_pp1.set_slc(44, l1_pp15.slc<2>(44));
  l2_pp1.set_slc(46, l1_pp18.slc<2>(46));
  l2_pp1.set_slc(48, l1_pp21.slc<2>(48));
  l2_pp1.set_slc(50, l1_pp24.slc<2>(50));
  l2_pp1[52] = l1_pp27[52];
  l2_pp1.set_slc(53, l1_pp0to2_c.slc<6>(53));
  l2_pp1[59] = l1_pp25[59];
  l2_pp1[60] = l1_pp24[60];
  l2_pp1[61] = l1_pp22[61];
  l2_pp1[62] = l1_pp21[62];
  l2_pp1[63] = l1_pp19[63];
  l2_pp1[64] = l1_pp18[64];
  l2_pp1[65] = l1_pp16[65];
  l2_pp1[66] = l1_pp15[66];
  l2_pp1[67] = l1_pp13[67];
  l2_pp1[68] = l1_pp12[68];
  l2_pp1[69] = l1_pp10[69];
  l2_pp1[70] = l1_pp9[70];
  l2_pp1[71] = l1_pp7[71];
  l2_pp1[72] = l1_pp6[72];
  l2_pp1[73] = l1_pp4[73];
  l2_pp1[74] = l1_pp3[74];
  l2_pp1.set_slc(75, l1_pp1.slc<30>(75));

  ui106 l2_pp2 = 0;
  l2_pp2[2] = l1_pp2[2];
  l2_pp2.set_slc(4, l1_pp2.slc<32>(4));
  l2_pp2.set_slc(36, l1_pp4.slc<2>(36));
  l2_pp2.set_slc(38, l1_pp7.slc<2>(38));
  l2_pp2.set_slc(40, l1_pp10.slc<2>(40));
  l2_pp2.set_slc(42, l1_pp13.slc<2>(42));
  l2_pp2.set_slc(44, l1_pp16.slc<2>(44));
  l2_pp2.set_slc(46, l1_pp19.slc<2>(46));
  l2_pp2.set_slc(48, l1_pp22.slc<2>(48));
  l2_pp2.set_slc(50, l1_pp25.slc<2>(50));
  l2_pp2[52] = l1_pp0to2_c[52];
  l2_pp2.set_slc(53, l1_pp3to5_c.slc<6>(53));
  l2_pp2[59] = l1_pp0to2_c[59];
  l2_pp2[60] = l1_pp25[60];
  l2_pp2[61] = l1_pp23[61];
  l2_pp2[62] = l1_pp22[62];
  l2_pp2[63] = l1_pp20[63];
  l2_pp2[64] = l1_pp19[64];
  l2_pp2[65] = l1_pp17[65];
  l2_pp2[66] = l1_pp16[66];
  l2_pp2[67] = l1_pp14[67];
  l2_pp2[68] = l1_pp13[68];
  l2_pp2[69] = l1_pp11[69];
  l2_pp2[70] = l1_pp10[70];
  l2_pp2[71] = l1_pp8[71];
  l2_pp2[72] = l1_pp7[72];
  l2_pp2[73] = l1_pp5[73];
  l2_pp2[74] = l1_pp4[74];
  l2_pp2.set_slc(75, l1_pp2.slc<30>(75));

  ui106 l2_pp3 = 0;
  l2_pp3[4] = l1_pp3[4];
  l2_pp3.set_slc(6, l1_pp3.slc<30>(6));
  l2_pp3.set_slc(36, l1_pp5.slc<2>(36));
  l2_pp3.set_slc(38, l1_pp8.slc<2>(38));
  l2_pp3.set_slc(40, l1_pp11.slc<2>(40));
  l2_pp3.set_slc(42, l1_pp14.slc<2>(42));
  l2_pp3.set_slc(44, l1_pp17.slc<2>(44));
  l2_pp3.set_slc(46, l1_pp20.slc<2>(46));
  l2_pp3.set_slc(48, l1_pp23.slc<2>(48));
  l2_pp3[50] = l1_pp26[50];
  l2_pp3[51] = l1_pp0to2_c[51];
  l2_pp3[52] = l1_pp3to5_c[52];
  l2_pp3.set_slc(53, l1_pp6to8_c.slc<6>(53));
  l2_pp3[59] = l1_pp3to5_c[59];
  l2_pp3[60] = l1_pp0to2_c[60];
  l2_pp3[61] = l1_pp24[61];
  l2_pp3[62] = l1_pp23[62];
  l2_pp3[63] = l1_pp21[63];
  l2_pp3[64] = l1_pp20[64];
  l2_pp3[65] = l1_pp18[65];
  l2_pp3[66] = l1_pp17[66];
  l2_pp3[67] = l1_pp15[67];
  l2_pp3[68] = l1_pp14[68];
  l2_pp3[69] = l1_pp12[69];
  l2_pp3[70] = l1_pp11[70];
  l2_pp3[71] = l1_pp9[71];
  l2_pp3[72] = l1_pp8[72];
  l2_pp3[73] = l1_pp6[73];
  l2_pp3[74] = l1_pp5[74];
  l2_pp3.set_slc(75, l1_pp3.slc<29>(75));

  ui106 l2_pp4 = 0;
  l2_pp4[6] = l1_pp4[6];
  l2_pp4.set_slc(8, l1_pp4.slc<28>(8));
  l2_pp4.set_slc(36, l1_pp6.slc<2>(36));
  l2_pp4.set_slc(38, l1_pp9.slc<2>(38));
  l2_pp4.set_slc(40, l1_pp12.slc<2>(40));
  l2_pp4.set_slc(42, l1_pp15.slc<2>(42));
  l2_pp4.set_slc(44, l1_pp18.slc<2>(44));
  l2_pp4.set_slc(46, l1_pp21.slc<2>(46));
  l2_pp4.set_slc(48, l1_pp24.slc<2>(48));
  l2_pp4[50] = l1_pp0to2_c[50];
  l2_pp4[51] = l1_pp3to5_c[51];
  l2_pp4[52] = l1_pp6to8_c[52];
  l2_pp4.set_slc(53, l1_pp9to11_c.slc<6>(53));
  l2_pp4[59] = l1_pp6to8_c[59];
  l2_pp4[60] = l1_pp3to5_c[60];
  l2_pp4[61] = l1_pp0to2_c[61];
  l2_pp4[62] = l1_pp24[62];
  l2_pp4[63] = l1_pp22[63];
  l2_pp4[64] = l1_pp21[64];
  l2_pp4[65] = l1_pp19[65];
  l2_pp4[66] = l1_pp18[66];
  l2_pp4[67] = l1_pp16[67];
  l2_pp4[68] = l1_pp15[68];
  l2_pp4[69] = l1_pp13[69];
  l2_pp4[70] = l1_pp12[70];
  l2_pp4[71] = l1_pp10[71];
  l2_pp4[72] = l1_pp9[72];
  l2_pp4[73] = l1_pp7[73];
  l2_pp4[74] = l1_pp6[74];
  l2_pp4.set_slc(75, l1_pp4.slc<28>(75));

  ui106 l2_pp5 = 0;
  l2_pp5[8] = l1_pp5[8];
  l2_pp5.set_slc(10, l1_pp5.slc<26>(10));
  l2_pp5.set_slc(36, l1_pp7.slc<2>(36));
  l2_pp5.set_slc(38, l1_pp10.slc<2>(38));
  l2_pp5.set_slc(40, l1_pp13.slc<2>(40));
  l2_pp5.set_slc(42, l1_pp16.slc<2>(42));
  l2_pp5.set_slc(44, l1_pp19.slc<2>(44));
  l2_pp5.set_slc(46, l1_pp22.slc<2>(46));
  l2_pp5[48] = l1_pp25[48];
  l2_pp5[49] = l1_pp0to2_c[49];
  l2_pp5[50] = l1_pp3to5_c[50];
  l2_pp5[51] = l1_pp6to8_c[51];
  l2_pp5[52] = l1_pp9to11_c[52];
  l2_pp5.set_slc(53, l1_pp12to14_c.slc<6>(53));
  l2_pp5[59] = l1_pp9to11_c[59];
  l2_pp5[60] = l1_pp6to8_c[60];
  l2_pp5[61] = l1_pp3to5_c[61];
  l2_pp5[62] = l1_pp0to2_c[62];
  l2_pp5[63] = l1_pp23[63];
  l2_pp5[64] = l1_pp22[64];
  l2_pp5[65] = l1_pp20[65];
  l2_pp5[66] = l1_pp19[66];
  l2_pp5[67] = l1_pp17[67];
  l2_pp5[68] = l1_pp16[68];
  l2_pp5[69] = l1_pp14[69];
  l2_pp5[70] = l1_pp13[70];
  l2_pp5[71] = l1_pp11[71];
  l2_pp5[72] = l1_pp10[72];
  l2_pp5[73] = l1_pp8[73];
  l2_pp5[74] = l1_pp7[74];
  l2_pp5.set_slc(75, l1_pp5.slc<26>(75));

  ui106 l2_pp6 = 0;
  l2_pp6[10] = l1_pp6[10];
  l2_pp6.set_slc(12, l1_pp6.slc<24>(12));
  l2_pp6.set_slc(36, l1_pp8.slc<2>(36));
  l2_pp6.set_slc(38, l1_pp11.slc<2>(38));
  l2_pp6.set_slc(40, l1_pp14.slc<2>(40));
  l2_pp6.set_slc(42, l1_pp17.slc<2>(42));
  l2_pp6.set_slc(44, l1_pp20.slc<2>(44));
  l2_pp6.set_slc(46, l1_pp23.slc<2>(46));
  l2_pp6[48] = l1_pp0to2_c[48];
  l2_pp6[49] = l1_pp3to5_c[49];
  l2_pp6[50] = l1_pp6to8_c[50];
  l2_pp6[51] = l1_pp9to11_c[51];
  l2_pp6[52] = l1_pp12to14_c[52];
  l2_pp6.set_slc(53, l1_pp15to17_c.slc<6>(53));
  l2_pp6[59] = l1_pp12to14_c[59];
  l2_pp6[60] = l1_pp9to11_c[60];
  l2_pp6[61] = l1_pp6to8_c[61];
  l2_pp6[62] = l1_pp3to5_c[62];
  l2_pp6[63] = l1_pp0to2_c[63];
  l2_pp6[64] = l1_pp23[64];
  l2_pp6[65] = l1_pp21[65];
  l2_pp6[66] = l1_pp20[66];
  l2_pp6[67] = l1_pp18[67];
  l2_pp6[68] = l1_pp17[68];
  l2_pp6[69] = l1_pp15[69];
  l2_pp6[70] = l1_pp14[70];
  l2_pp6[71] = l1_pp12[71];
  l2_pp6[72] = l1_pp11[72];
  l2_pp6[73] = l1_pp9[73];
  l2_pp6[74] = l1_pp8[74];
  l2_pp6.set_slc(75, l1_pp6.slc<24>(75));

  ui106 l2_pp7 = 0;
  l2_pp7[12] = l1_pp7[12];
  l2_pp7.set_slc(14, l1_pp7.slc<22>(14));
  l2_pp7.set_slc(36, l1_pp9.slc<2>(36));
  l2_pp7.set_slc(38, l1_pp12.slc<2>(38));
  l2_pp7.set_slc(40, l1_pp15.slc<2>(40));
  l2_pp7.set_slc(42, l1_pp18.slc<2>(42));
  l2_pp7.set_slc(44, l1_pp21.slc<2>(44));
  l2_pp7[46] = l1_pp24[46];
  l2_pp7[47] = l1_pp0to2_c[47];
  l2_pp7[48] = l1_pp3to5_c[48];
  l2_pp7[49] = l1_pp6to8_c[49];
  l2_pp7[50] = l1_pp9to11_c[50];
  l2_pp7[51] = l1_pp12to14_c[51];
  l2_pp7[52] = l1_pp15to17_c[52];
  l2_pp7.set_slc(53, l1_pp18to20_c.slc<6>(53));
  l2_pp7[59] = l1_pp15to17_c[59];
  l2_pp7[60] = l1_pp12to14_c[60];
  l2_pp7[61] = l1_pp9to11_c[61];
  l2_pp7[62] = l1_pp6to8_c[62];
  l2_pp7[63] = l1_pp3to5_c[63];
  l2_pp7[64] = l1_pp0to2_c[64];
  l2_pp7[65] = l1_pp22[65];
  l2_pp7[66] = l1_pp21[66];
  l2_pp7[67] = l1_pp19[67];
  l2_pp7[68] = l1_pp18[68];
  l2_pp7[69] = l1_pp16[69];
  l2_pp7[70] = l1_pp15[70];
  l2_pp7[71] = l1_pp13[71];
  l2_pp7[72] = l1_pp12[72];
  l2_pp7[73] = l1_pp10[73];
  l2_pp7[74] = l1_pp9[74];
  l2_pp7.set_slc(75, l1_pp7.slc<22>(75));

  ui106 l2_pp8 = 0;
  l2_pp8[14] = l1_pp8[14];
  l2_pp8.set_slc(16, l1_pp8.slc<20>(16));
  l2_pp8.set_slc(36, l1_pp10.slc<2>(36));
  l2_pp8.set_slc(38, l1_pp13.slc<2>(38));
  l2_pp8.set_slc(40, l1_pp16.slc<2>(40));
  l2_pp8.set_slc(42, l1_pp19.slc<2>(42));
  l2_pp8.set_slc(44, l1_pp22.slc<2>(44));
  l2_pp8[46] = l1_pp0to2_c[46];
  l2_pp8[47] = l1_pp3to5_c[47];
  l2_pp8[48] = l1_pp6to8_c[48];
  l2_pp8[49] = l1_pp9to11_c[49];
  l2_pp8[50] = l1_pp12to14_c[50];
  l2_pp8[51] = l1_pp15to17_c[51];
  l2_pp8[52] = l1_pp18to20_c[52];
  l2_pp8.set_slc(53, l1_pp21to23_c.slc<6>(53));
  l2_pp8[59] = l1_pp18to20_c[59];
  l2_pp8[60] = l1_pp15to17_c[60];
  l2_pp8[61] = l1_pp12to14_c[61];
  l2_pp8[62] = l1_pp9to11_c[62];
  l2_pp8[63] = l1_pp6to8_c[63];
  l2_pp8[64] = l1_pp3to5_c[64];
  l2_pp8[65] = l1_pp0to2_c[65];
  l2_pp8[66] = l1_pp22[66];
  l2_pp8[67] = l1_pp20[67];
  l2_pp8[68] = l1_pp19[68];
  l2_pp8[69] = l1_pp17[69];
  l2_pp8[70] = l1_pp16[70];
  l2_pp8[71] = l1_pp14[71];
  l2_pp8[72] = l1_pp13[72];
  l2_pp8[73] = l1_pp11[73];
  l2_pp8[74] = l1_pp10[74];
  l2_pp8.set_slc(75, l1_pp8.slc<20>(75));

  ui106 l2_pp9 = 0;
  l2_pp9[16] = l1_pp9[16];
  l2_pp9.set_slc(18, l1_pp9.slc<18>(18));
  l2_pp9.set_slc(36, l1_pp11.slc<2>(36));
  l2_pp9.set_slc(38, l1_pp14.slc<2>(38));
  l2_pp9.set_slc(40, l1_pp17.slc<2>(40));
  l2_pp9.set_slc(42, l1_pp20.slc<2>(42));
  l2_pp9[44] = l1_pp23[44];
  l2_pp9[45] = l1_pp0to2_c[45];
  l2_pp9[46] = l1_pp3to5_c[46];
  l2_pp9[47] = l1_pp6to8_c[47];
  l2_pp9[48] = l1_pp9to11_c[48];
  l2_pp9[49] = l1_pp12to14_c[49];
  l2_pp9[50] = l1_pp15to17_c[50];
  l2_pp9[51] = l1_pp18to20_c[51];
  l2_pp9[52] = l1_pp21to23_c[52];
  l2_pp9.set_slc(53, l1_pp24to26_c.slc<6>(53));
  l2_pp9[59] = l1_pp21to23_c[59];
  l2_pp9[60] = l1_pp18to20_c[60];
  l2_pp9[61] = l1_pp15to17_c[61];
  l2_pp9[62] = l1_pp12to14_c[62];
  l2_pp9[63] = l1_pp9to11_c[63];
  l2_pp9[64] = l1_pp6to8_c[64];
  l2_pp9[65] = l1_pp3to5_c[65];
  l2_pp9[66] = l1_pp0to2_c[66];
  l2_pp9[67] = l1_pp21[67];
  l2_pp9[68] = l1_pp20[68];
  l2_pp9[69] = l1_pp18[69];
  l2_pp9[70] = l1_pp17[70];
  l2_pp9[71] = l1_pp15[71];
  l2_pp9[72] = l1_pp14[72];
  l2_pp9[73] = l1_pp12[73];
  l2_pp9[74] = l1_pp11[74];
  l2_pp9.set_slc(75, l1_pp9.slc<18>(75));

  ui106 l2_pp10 = 0;
  l2_pp10[18] = l1_pp10[18];
  l2_pp10.set_slc(20, l1_pp10.slc<16>(20));
  l2_pp10.set_slc(36, l1_pp12.slc<2>(36));
  l2_pp10.set_slc(38, l1_pp15.slc<2>(38));
  l2_pp10.set_slc(40, l1_pp18.slc<2>(40));
  l2_pp10.set_slc(42, l1_pp21.slc<2>(42));
  l2_pp10[44] = l1_pp0to2_c[44];
  l2_pp10[45] = l1_pp3to5_c[45];
  l2_pp10[46] = l1_pp6to8_c[46];
  l2_pp10[47] = l1_pp9to11_c[47];
  l2_pp10[48] = l1_pp12to14_c[48];
  l2_pp10[49] = l1_pp15to17_c[49];
  l2_pp10[50] = l1_pp18to20_c[50];
  l2_pp10[51] = l1_pp21to23_c[51];
  l2_pp10.set_slc(52, l1_pp0to2_s.slc<7>(52));
  l2_pp10[59] = l1_pp24to26_c[59];
  l2_pp10[60] = l1_pp21to23_c[60];
  l2_pp10[61] = l1_pp18to20_c[61];
  l2_pp10[62] = l1_pp15to17_c[62];
  l2_pp10[63] = l1_pp12to14_c[63];
  l2_pp10[64] = l1_pp9to11_c[64];
  l2_pp10[65] = l1_pp6to8_c[65];
  l2_pp10[66] = l1_pp3to5_c[66];
  l2_pp10[67] = l1_pp0to2_c[67];
  l2_pp10[68] = l1_pp21[68];
  l2_pp10[69] = l1_pp19[69];
  l2_pp10[70] = l1_pp18[70];
  l2_pp10[71] = l1_pp16[71];
  l2_pp10[72] = l1_pp15[72];
  l2_pp10[73] = l1_pp13[73];
  l2_pp10[74] = l1_pp12[74];
  l2_pp10.set_slc(75, l1_pp10.slc<16>(75));

  ui106 l2_pp11 = 0;
  l2_pp11[20] = l1_pp11[20];
  l2_pp11.set_slc(22, l1_pp11.slc<14>(22));
  l2_pp11.set_slc(36, l1_pp13.slc<2>(36));
  l2_pp11.set_slc(38, l1_pp16.slc<2>(38));
  l2_pp11.set_slc(40, l1_pp19.slc<2>(40));
  l2_pp11[42] = l1_pp22[42];
  l2_pp11[43] = l1_pp0to2_c[43];
  l2_pp11[44] = l1_pp3to5_c[44];
  l2_pp11[45] = l1_pp6to8_c[45];
  l2_pp11[46] = l1_pp9to11_c[46];
  l2_pp11[47] = l1_pp12to14_c[47];
  l2_pp11[48] = l1_pp15to17_c[48];
  l2_pp11[49] = l1_pp18to20_c[49];
  l2_pp11.set_slc(50, l1_pp0to2_s.slc<2>(50));
  l2_pp11.set_slc(52, l1_pp3to5_s.slc<7>(52));
  l2_pp11.set_slc(59, l1_pp0to2_s.slc<2>(59));
  l2_pp11[61] = l1_pp21to23_c[61];
  l2_pp11[62] = l1_pp18to20_c[62];
  l2_pp11[63] = l1_pp15to17_c[63];
  l2_pp11[64] = l1_pp12to14_c[64];
  l2_pp11[65] = l1_pp9to11_c[65];
  l2_pp11[66] = l1_pp6to8_c[66];
  l2_pp11[67] = l1_pp3to5_c[67];
  l2_pp11[68] = l1_pp0to2_c[68];
  l2_pp11[69] = l1_pp20[69];
  l2_pp11[70] = l1_pp19[70];
  l2_pp11[71] = l1_pp17[71];
  l2_pp11[72] = l1_pp16[72];
  l2_pp11[73] = l1_pp14[73];
  l2_pp11[74] = l1_pp13[74];
  l2_pp11.set_slc(75, l1_pp11.slc<14>(75));

  ui106 l2_pp12 = 0;
  l2_pp12[22] = l1_pp12[22];
  l2_pp12.set_slc(24, l1_pp12.slc<12>(24));
  l2_pp12.set_slc(36, l1_pp14.slc<2>(36));
  l2_pp12.set_slc(38, l1_pp17.slc<2>(38));
  l2_pp12.set_slc(40, l1_pp20.slc<2>(40));
  l2_pp12[42] = l1_pp0to2_c[42];
  l2_pp12[43] = l1_pp3to5_c[43];
  l2_pp12[44] = l1_pp6to8_c[44];
  l2_pp12[45] = l1_pp9to11_c[45];
  l2_pp12[46] = l1_pp12to14_c[46];
  l2_pp12[47] = l1_pp15to17_c[47];
  l2_pp12.set_slc(48, l1_pp0to2_s.slc<2>(48));
  l2_pp12.set_slc(50, l1_pp3to5_s.slc<2>(50));
  l2_pp12.set_slc(52, l1_pp6to8_s.slc<7>(52));
  l2_pp12.set_slc(59, l1_pp3to5_s.slc<2>(59));
  l2_pp12.set_slc(61, l1_pp0to2_s.slc<2>(61));
  l2_pp12[63] = l1_pp18to20_c[63];
  l2_pp12[64] = l1_pp15to17_c[64];
  l2_pp12[65] = l1_pp12to14_c[65];
  l2_pp12[66] = l1_pp9to11_c[66];
  l2_pp12[67] = l1_pp6to8_c[67];
  l2_pp12[68] = l1_pp3to5_c[68];
  l2_pp12[69] = l1_pp0to2_c[69];
  l2_pp12[70] = l1_pp20[70];
  l2_pp12[71] = l1_pp18[71];
  l2_pp12[72] = l1_pp17[72];
  l2_pp12[73] = l1_pp15[73];
  l2_pp12[74] = l1_pp14[74];
  l2_pp12.set_slc(75, l1_pp12.slc<12>(75));

  ui106 l2_pp13 = 0;
  l2_pp13[24] = l1_pp13[24];
  l2_pp13.set_slc(26, l1_pp13.slc<10>(26));
  l2_pp13.set_slc(36, l1_pp15.slc<2>(36));
  l2_pp13.set_slc(38, l1_pp18.slc<2>(38));
  l2_pp13[40] = l1_pp21[40];
  l2_pp13[41] = l1_pp0to2_c[41];
  l2_pp13[42] = l1_pp3to5_c[42];
  l2_pp13[43] = l1_pp6to8_c[43];
  l2_pp13[44] = l1_pp9to11_c[44];
  l2_pp13[45] = l1_pp12to14_c[45];
  l2_pp13.set_slc(46, l1_pp0to2_s.slc<2>(46));
  l2_pp13.set_slc(48, l1_pp3to5_s.slc<2>(48));
  l2_pp13.set_slc(50, l1_pp6to8_s.slc<2>(50));
  l2_pp13.set_slc(52, l1_pp9to11_s.slc<7>(52));
  l2_pp13.set_slc(59, l1_pp6to8_s.slc<2>(59));
  l2_pp13.set_slc(61, l1_pp3to5_s.slc<2>(61));
  l2_pp13.set_slc(63, l1_pp0to2_s.slc<2>(63));
  l2_pp13[65] = l1_pp15to17_c[65];
  l2_pp13[66] = l1_pp12to14_c[66];
  l2_pp13[67] = l1_pp9to11_c[67];
  l2_pp13[68] = l1_pp6to8_c[68];
  l2_pp13[69] = l1_pp3to5_c[69];
  l2_pp13[70] = l1_pp0to2_c[70];
  l2_pp13[71] = l1_pp19[71];
  l2_pp13[72] = l1_pp18[72];
  l2_pp13[73] = l1_pp16[73];
  l2_pp13[74] = l1_pp15[74];
  l2_pp13.set_slc(75, l1_pp13.slc<10>(75));

  ui106 l2_pp14 = 0;
  l2_pp14[26] = l1_pp14[26];
  l2_pp14.set_slc(28, l1_pp14.slc<8>(28));
  l2_pp14.set_slc(36, l1_pp16.slc<2>(36));
  l2_pp14.set_slc(38, l1_pp19.slc<2>(38));
  l2_pp14[40] = l1_pp0to2_c[40];
  l2_pp14[41] = l1_pp3to5_c[41];
  l2_pp14[42] = l1_pp6to8_c[42];
  l2_pp14[43] = l1_pp9to11_c[43];
  l2_pp14.set_slc(44, l1_pp0to2_s.slc<2>(44));
  l2_pp14.set_slc(46, l1_pp3to5_s.slc<2>(46));
  l2_pp14.set_slc(48, l1_pp6to8_s.slc<2>(48));
  l2_pp14.set_slc(50, l1_pp9to11_s.slc<2>(50));
  l2_pp14.set_slc(52, l1_pp12to14_s.slc<7>(52));
  l2_pp14.set_slc(59, l1_pp9to11_s.slc<2>(59));
  l2_pp14.set_slc(61, l1_pp6to8_s.slc<2>(61));
  l2_pp14.set_slc(63, l1_pp3to5_s.slc<2>(63));
  l2_pp14.set_slc(65, l1_pp0to2_s.slc<2>(65));
  l2_pp14[67] = l1_pp12to14_c[67];
  l2_pp14[68] = l1_pp9to11_c[68];
  l2_pp14[69] = l1_pp6to8_c[69];
  l2_pp14[70] = l1_pp3to5_c[70];
  l2_pp14[71] = l1_pp0to2_c[71];
  l2_pp14[72] = l1_pp19[72];
  l2_pp14[73] = l1_pp17[73];
  l2_pp14[74] = l1_pp16[74];
  l2_pp14.set_slc(75, l1_pp14.slc<8>(75));

  ui106 l2_pp15 = 0;
  l2_pp15[28] = l1_pp15[28];
  l2_pp15.set_slc(30, l1_pp15.slc<6>(30));
  l2_pp15.set_slc(36, l1_pp17.slc<2>(36));
  l2_pp15[38] = l1_pp20[38];
  l2_pp15[39] = l1_pp0to2_c[39];
  l2_pp15[40] = l1_pp3to5_c[40];
  l2_pp15[41] = l1_pp6to8_c[41];
  l2_pp15.set_slc(42, l1_pp0to2_s.slc<2>(42));
  l2_pp15.set_slc(44, l1_pp3to5_s.slc<2>(44));
  l2_pp15.set_slc(46, l1_pp6to8_s.slc<2>(46));
  l2_pp15.set_slc(48, l1_pp9to11_s.slc<2>(48));
  l2_pp15.set_slc(50, l1_pp12to14_s.slc<2>(50));
  l2_pp15.set_slc(52, l1_pp15to17_s.slc<7>(52));
  l2_pp15.set_slc(59, l1_pp12to14_s.slc<2>(59));
  l2_pp15.set_slc(61, l1_pp9to11_s.slc<2>(61));
  l2_pp15.set_slc(63, l1_pp6to8_s.slc<2>(63));
  l2_pp15.set_slc(65, l1_pp3to5_s.slc<2>(65));
  l2_pp15.set_slc(67, l1_pp0to2_s.slc<2>(67));
  l2_pp15[69] = l1_pp9to11_c[69];
  l2_pp15[70] = l1_pp6to8_c[70];
  l2_pp15[71] = l1_pp3to5_c[71];
  l2_pp15[72] = l1_pp0to2_c[72];
  l2_pp15[73] = l1_pp18[73];
  l2_pp15[74] = l1_pp17[74];
  l2_pp15.set_slc(75, l1_pp15.slc<6>(75));

  ui106 l2_pp16 = 0;
  l2_pp16[30] = l1_pp16[30];
  l2_pp16.set_slc(32, l1_pp16.slc<4>(32));
  l2_pp16.set_slc(36, l1_pp18.slc<2>(36));
  l2_pp16[38] = l1_pp0to2_c[38];
  l2_pp16[39] = l1_pp3to5_c[39];
  l2_pp16.set_slc(40, l1_pp0to2_s.slc<2>(40));
  l2_pp16.set_slc(42, l1_pp3to5_s.slc<2>(42));
  l2_pp16.set_slc(44, l1_pp6to8_s.slc<2>(44));
  l2_pp16.set_slc(46, l1_pp9to11_s.slc<2>(46));
  l2_pp16.set_slc(48, l1_pp12to14_s.slc<2>(48));
  l2_pp16.set_slc(50, l1_pp15to17_s.slc<2>(50));
  l2_pp16.set_slc(52, l1_pp18to20_s.slc<7>(52));
  l2_pp16.set_slc(59, l1_pp15to17_s.slc<2>(59));
  l2_pp16.set_slc(61, l1_pp12to14_s.slc<2>(61));
  l2_pp16.set_slc(63, l1_pp9to11_s.slc<2>(63));
  l2_pp16.set_slc(65, l1_pp6to8_s.slc<2>(65));
  l2_pp16.set_slc(67, l1_pp3to5_s.slc<2>(67));
  l2_pp16.set_slc(69, l1_pp0to2_s.slc<2>(69));
  l2_pp16[71] = l1_pp6to8_c[71];
  l2_pp16[72] = l1_pp3to5_c[72];
  l2_pp16[73] = l1_pp0to2_c[73];
  l2_pp16[74] = l1_pp18[74];
  l2_pp16.set_slc(75, l1_pp16.slc<4>(75));

  ui106 l2_pp17 = 0;
  l2_pp17[32] = l1_pp17[32];
  l2_pp17.set_slc(34, l1_pp17.slc<2>(34));
  l2_pp17[36] = l1_pp19[36];
  l2_pp17[37] = l1_pp0to2_c[37];
  l2_pp17.set_slc(38, l1_pp0to2_s.slc<2>(38));
  l2_pp17.set_slc(40, l1_pp3to5_s.slc<2>(40));
  l2_pp17.set_slc(42, l1_pp6to8_s.slc<2>(42));
  l2_pp17.set_slc(44, l1_pp9to11_s.slc<2>(44));
  l2_pp17.set_slc(46, l1_pp12to14_s.slc<2>(46));
  l2_pp17.set_slc(48, l1_pp15to17_s.slc<2>(48));
  l2_pp17.set_slc(50, l1_pp18to20_s.slc<2>(50));
  l2_pp17.set_slc(52, l1_pp21to23_s.slc<7>(52));
  l2_pp17.set_slc(59, l1_pp18to20_s.slc<2>(59));
  l2_pp17.set_slc(61, l1_pp15to17_s.slc<2>(61));
  l2_pp17.set_slc(63, l1_pp12to14_s.slc<2>(63));
  l2_pp17.set_slc(65, l1_pp9to11_s.slc<2>(65));
  l2_pp17.set_slc(67, l1_pp6to8_s.slc<2>(67));
  l2_pp17.set_slc(69, l1_pp3to5_s.slc<2>(69));
  l2_pp17.set_slc(71, l1_pp0to2_s.slc<2>(71));
  l2_pp17[73] = l1_pp3to5_c[73];
  l2_pp17[74] = l1_pp0to2_c[74];
  l2_pp17.set_slc(75, l1_pp17.slc<2>(75));

  ui106 l2_pp18 = 0;
  l2_pp18[34] = l1_pp18[34];
  l2_pp18.set_slc(36, l1_pp0to2_s.slc<2>(36));
  l2_pp18.set_slc(38, l1_pp3to5_s.slc<2>(38));
  l2_pp18.set_slc(40, l1_pp6to8_s.slc<2>(40));
  l2_pp18.set_slc(42, l1_pp9to11_s.slc<2>(42));
  l2_pp18.set_slc(44, l1_pp12to14_s.slc<2>(44));
  l2_pp18.set_slc(46, l1_pp15to17_s.slc<2>(46));
  l2_pp18.set_slc(48, l1_pp18to20_s.slc<2>(48));
  l2_pp18.set_slc(50, l1_pp21to23_s.slc<2>(50));
  l2_pp18.set_slc(52, l1_pp24to26_s.slc<7>(52));
  l2_pp18.set_slc(59, l1_pp21to23_s.slc<2>(59));
  l2_pp18.set_slc(61, l1_pp18to20_s.slc<2>(61));
  l2_pp18.set_slc(63, l1_pp15to17_s.slc<2>(63));
  l2_pp18.set_slc(65, l1_pp12to14_s.slc<2>(65));
  l2_pp18.set_slc(67, l1_pp9to11_s.slc<2>(67));
  l2_pp18.set_slc(69, l1_pp6to8_s.slc<2>(69));
  l2_pp18.set_slc(71, l1_pp3to5_s.slc<2>(71));
  l2_pp18.set_slc(73, l1_pp0to2_s.slc<2>(73));
  l2_pp18[75] = l1_pp0to2_c[75];


  // Max bit column depth after Dadda level #2 is 13
  ui106 l2_pp0to2_s = 0, l2_pp0to2_c = 0;
  l2_pp0to2_s.set_slc(24, ui2(l2_pp0.slc<2>(24) ^ l2_pp1.slc<2>(24)));
  l2_pp0to2_c.set_slc(25, ui2(l2_pp0.slc<2>(24) & l2_pp1.slc<2>(24)));
  l2_pp0to2_s.set_slc(26, ui60(l2_pp0.slc<60>(26) ^ l2_pp1.slc<60>(26) ^ l2_pp2.slc<60>(26)));
  l2_pp0to2_c.set_slc(27, ui60(l2_pp0.slc<60>(26) & l2_pp1.slc<60>(26) | l2_pp0.slc<60>(26) & l2_pp2.slc<60>(26) | l2_pp1.slc<60>(26) & l2_pp2.slc<60>(26)));
  l2_pp0to2_s[86] = l2_pp0[86] ^ l2_pp1[86];
  l2_pp0to2_c[87] = l2_pp0[86] & l2_pp1[86];
  ui106 l2_pp3to5_s = 0, l2_pp3to5_c = 0;
  l2_pp3to5_s.set_slc(26, ui2(l2_pp3.slc<2>(26) ^ l2_pp4.slc<2>(26)));
  l2_pp3to5_c.set_slc(27, ui2(l2_pp3.slc<2>(26) & l2_pp4.slc<2>(26)));
  l2_pp3to5_s.set_slc(28, ui56(l2_pp3.slc<56>(28) ^ l2_pp4.slc<56>(28) ^ l2_pp5.slc<56>(28)));
  l2_pp3to5_c.set_slc(29, ui56(l2_pp3.slc<56>(28) & l2_pp4.slc<56>(28) | l2_pp3.slc<56>(28) & l2_pp5.slc<56>(28) | l2_pp4.slc<56>(28) & l2_pp5.slc<56>(28)));
  l2_pp3to5_s[84] = l2_pp3[84] ^ l2_pp4[84];
  l2_pp3to5_c[85] = l2_pp3[84] & l2_pp4[84];
  ui106 l2_pp6to8_s = 0, l2_pp6to8_c = 0;
  l2_pp6to8_s.set_slc(28, ui2(l2_pp6.slc<2>(28) ^ l2_pp7.slc<2>(28)));
  l2_pp6to8_c.set_slc(29, ui2(l2_pp6.slc<2>(28) & l2_pp7.slc<2>(28)));
  l2_pp6to8_s.set_slc(30, ui52(l2_pp6.slc<52>(30) ^ l2_pp7.slc<52>(30) ^ l2_pp8.slc<52>(30)));
  l2_pp6to8_c.set_slc(31, ui52(l2_pp6.slc<52>(30) & l2_pp7.slc<52>(30) | l2_pp6.slc<52>(30) & l2_pp8.slc<52>(30) | l2_pp7.slc<52>(30) & l2_pp8.slc<52>(30)));
  l2_pp6to8_s[82] = l2_pp6[82] ^ l2_pp7[82];
  l2_pp6to8_c[83] = l2_pp6[82] & l2_pp7[82];
  ui106 l2_pp9to11_s = 0, l2_pp9to11_c = 0;
  l2_pp9to11_s.set_slc(30, ui2(l2_pp9.slc<2>(30) ^ l2_pp10.slc<2>(30)));
  l2_pp9to11_c.set_slc(31, ui2(l2_pp9.slc<2>(30) & l2_pp10.slc<2>(30)));
  l2_pp9to11_s.set_slc(32, ui48(l2_pp9.slc<48>(32) ^ l2_pp10.slc<48>(32) ^ l2_pp11.slc<48>(32)));
  l2_pp9to11_c.set_slc(33, ui48(l2_pp9.slc<48>(32) & l2_pp10.slc<48>(32) | l2_pp9.slc<48>(32) & l2_pp11.slc<48>(32) | l2_pp10.slc<48>(32) & l2_pp11.slc<48>(32)));
  l2_pp9to11_s[80] = l2_pp9[80] ^ l2_pp10[80];
  l2_pp9to11_c[81] = l2_pp9[80] & l2_pp10[80];
  ui106 l2_pp12to14_s = 0, l2_pp12to14_c = 0;
  l2_pp12to14_s.set_slc(32, ui2(l2_pp12.slc<2>(32) ^ l2_pp13.slc<2>(32)));
  l2_pp12to14_c.set_slc(33, ui2(l2_pp12.slc<2>(32) & l2_pp13.slc<2>(32)));
  l2_pp12to14_s.set_slc(34, ui44(l2_pp12.slc<44>(34) ^ l2_pp13.slc<44>(34) ^ l2_pp14.slc<44>(34)));
  l2_pp12to14_c.set_slc(35, ui44(l2_pp12.slc<44>(34) & l2_pp13.slc<44>(34) | l2_pp12.slc<44>(34) & l2_pp14.slc<44>(34) | l2_pp13.slc<44>(34) & l2_pp14.slc<44>(34)));
  l2_pp12to14_s[78] = l2_pp12[78] ^ l2_pp13[78];
  l2_pp12to14_c[79] = l2_pp12[78] & l2_pp13[78];
  ui106 l2_pp15to17_s = 0, l2_pp15to17_c = 0;
  l2_pp15to17_s.set_slc(34, ui2(l2_pp15.slc<2>(34) ^ l2_pp16.slc<2>(34)));
  l2_pp15to17_c.set_slc(35, ui2(l2_pp15.slc<2>(34) & l2_pp16.slc<2>(34)));
  l2_pp15to17_s.set_slc(36, ui40(l2_pp15.slc<40>(36) ^ l2_pp16.slc<40>(36) ^ l2_pp17.slc<40>(36)));
  l2_pp15to17_c.set_slc(37, ui40(l2_pp15.slc<40>(36) & l2_pp16.slc<40>(36) | l2_pp15.slc<40>(36) & l2_pp17.slc<40>(36) | l2_pp16.slc<40>(36) & l2_pp17.slc<40>(36)));
  l2_pp15to17_s[76] = l2_pp15[76] ^ l2_pp16[76];
  l2_pp15to17_c[77] = l2_pp15[76] & l2_pp16[76];

  // Dadda level 3 beginning dot diagram:
  // 111111
  // 000000999999999988888888887777777777666666666655555555554444444444333333333322222222221111111111
  // 5432109876543210987654321098765432109876543210987654321098765432109876543210987654321098765432109876543210
  // ********************************************************************************************************
  //  *******************************************************************************************************
  //  ***************************************************************************************************** *
  //   ************************************************************************************************** *
  //    *********************************************************************************************** *
  //      ******************************************************************************************* *
  //        *************************************************************************************** *
  //          *********************************************************************************** *
  //            ******************************************************************************* *
  //              *************************************************************************** *
  //                *********************************************************************** *
  //                  ******************************************************************* *
  //                   **************************************************************** *

  ui106 l3_pp0 = 0;
  l3_pp0.set_slc(2, l2_pp0.slc<22>(2));
  l3_pp0.set_slc(24, l2_pp2.slc<2>(24));
  l3_pp0.set_slc(26, l2_pp5.slc<2>(26));
  l3_pp0.set_slc(28, l2_pp8.slc<2>(28));
  l3_pp0.set_slc(30, l2_pp11.slc<2>(30));
  l3_pp0.set_slc(32, l2_pp14.slc<2>(32));
  l3_pp0.set_slc(34, l2_pp17.slc<2>(34));
  l3_pp0.set_slc(36, l2_pp18.slc<40>(36));
  l3_pp0[76] = l2_pp17[76];
  l3_pp0[77] = l2_pp15[77];
  l3_pp0[78] = l2_pp14[78];
  l3_pp0[79] = l2_pp12[79];
  l3_pp0[80] = l2_pp11[80];
  l3_pp0[81] = l2_pp9[81];
  l3_pp0[82] = l2_pp8[82];
  l3_pp0[83] = l2_pp6[83];
  l3_pp0[84] = l2_pp5[84];
  l3_pp0[85] = l2_pp3[85];
  l3_pp0[86] = l2_pp2[86];
  l3_pp0.set_slc(87, l2_pp0.slc<19>(87));

  ui106 l3_pp1 = 0;
  l3_pp1.set_slc(2, l2_pp1.slc<22>(2));
  l3_pp1.set_slc(24, l2_pp3.slc<2>(24));
  l3_pp1.set_slc(26, l2_pp6.slc<2>(26));
  l3_pp1.set_slc(28, l2_pp9.slc<2>(28));
  l3_pp1.set_slc(30, l2_pp12.slc<2>(30));
  l3_pp1.set_slc(32, l2_pp15.slc<2>(32));
  l3_pp1[34] = l2_pp18[34];
  l3_pp1.set_slc(35, l2_pp0to2_c.slc<42>(35));
  l3_pp1[77] = l2_pp16[77];
  l3_pp1[78] = l2_pp15[78];
  l3_pp1[79] = l2_pp13[79];
  l3_pp1[80] = l2_pp12[80];
  l3_pp1[81] = l2_pp10[81];
  l3_pp1[82] = l2_pp9[82];
  l3_pp1[83] = l2_pp7[83];
  l3_pp1[84] = l2_pp6[84];
  l3_pp1[85] = l2_pp4[85];
  l3_pp1[86] = l2_pp3[86];
  l3_pp1.set_slc(87, l2_pp1.slc<18>(87));

  ui106 l3_pp2 = 0;
  l3_pp2[2] = l2_pp2[2];
  l3_pp2.set_slc(4, l2_pp2.slc<20>(4));
  l3_pp2.set_slc(24, l2_pp4.slc<2>(24));
  l3_pp2.set_slc(26, l2_pp7.slc<2>(26));
  l3_pp2.set_slc(28, l2_pp10.slc<2>(28));
  l3_pp2.set_slc(30, l2_pp13.slc<2>(30));
  l3_pp2.set_slc(32, l2_pp16.slc<2>(32));
  l3_pp2[34] = l2_pp0to2_c[34];
  l3_pp2.set_slc(35, l2_pp3to5_c.slc<42>(35));
  l3_pp2[77] = l2_pp0to2_c[77];
  l3_pp2[78] = l2_pp16[78];
  l3_pp2[79] = l2_pp14[79];
  l3_pp2[80] = l2_pp13[80];
  l3_pp2[81] = l2_pp11[81];
  l3_pp2[82] = l2_pp10[82];
  l3_pp2[83] = l2_pp8[83];
  l3_pp2[84] = l2_pp7[84];
  l3_pp2[85] = l2_pp5[85];
  l3_pp2[86] = l2_pp4[86];
  l3_pp2.set_slc(87, l2_pp2.slc<18>(87));

  ui106 l3_pp3 = 0;
  l3_pp3[4] = l2_pp3[4];
  l3_pp3.set_slc(6, l2_pp3.slc<18>(6));
  l3_pp3.set_slc(24, l2_pp5.slc<2>(24));
  l3_pp3.set_slc(26, l2_pp8.slc<2>(26));
  l3_pp3.set_slc(28, l2_pp11.slc<2>(28));
  l3_pp3.set_slc(30, l2_pp14.slc<2>(30));
  l3_pp3[32] = l2_pp17[32];
  l3_pp3[33] = l2_pp0to2_c[33];
  l3_pp3[34] = l2_pp3to5_c[34];
  l3_pp3.set_slc(35, l2_pp6to8_c.slc<42>(35));
  l3_pp3[77] = l2_pp3to5_c[77];
  l3_pp3[78] = l2_pp0to2_c[78];
  l3_pp3[79] = l2_pp15[79];
  l3_pp3[80] = l2_pp14[80];
  l3_pp3[81] = l2_pp12[81];
  l3_pp3[82] = l2_pp11[82];
  l3_pp3[83] = l2_pp9[83];
  l3_pp3[84] = l2_pp8[84];
  l3_pp3[85] = l2_pp6[85];
  l3_pp3[86] = l2_pp5[86];
  l3_pp3.set_slc(87, l2_pp3.slc<17>(87));

  ui106 l3_pp4 = 0;
  l3_pp4[6] = l2_pp4[6];
  l3_pp4.set_slc(8, l2_pp4.slc<16>(8));
  l3_pp4.set_slc(24, l2_pp6.slc<2>(24));
  l3_pp4.set_slc(26, l2_pp9.slc<2>(26));
  l3_pp4.set_slc(28, l2_pp12.slc<2>(28));
  l3_pp4.set_slc(30, l2_pp15.slc<2>(30));
  l3_pp4[32] = l2_pp0to2_c[32];
  l3_pp4[33] = l2_pp3to5_c[33];
  l3_pp4[34] = l2_pp6to8_c[34];
  l3_pp4.set_slc(35, l2_pp9to11_c.slc<42>(35));
  l3_pp4[77] = l2_pp6to8_c[77];
  l3_pp4[78] = l2_pp3to5_c[78];
  l3_pp4[79] = l2_pp0to2_c[79];
  l3_pp4[80] = l2_pp15[80];
  l3_pp4[81] = l2_pp13[81];
  l3_pp4[82] = l2_pp12[82];
  l3_pp4[83] = l2_pp10[83];
  l3_pp4[84] = l2_pp9[84];
  l3_pp4[85] = l2_pp7[85];
  l3_pp4[86] = l2_pp6[86];
  l3_pp4.set_slc(87, l2_pp4.slc<16>(87));

  ui106 l3_pp5 = 0;
  l3_pp5[8] = l2_pp5[8];
  l3_pp5.set_slc(10, l2_pp5.slc<14>(10));
  l3_pp5.set_slc(24, l2_pp7.slc<2>(24));
  l3_pp5.set_slc(26, l2_pp10.slc<2>(26));
  l3_pp5.set_slc(28, l2_pp13.slc<2>(28));
  l3_pp5[30] = l2_pp16[30];
  l3_pp5[31] = l2_pp0to2_c[31];
  l3_pp5[32] = l2_pp3to5_c[32];
  l3_pp5[33] = l2_pp6to8_c[33];
  l3_pp5[34] = l2_pp9to11_c[34];
  l3_pp5.set_slc(35, l2_pp12to14_c.slc<42>(35));
  l3_pp5[77] = l2_pp9to11_c[77];
  l3_pp5[78] = l2_pp6to8_c[78];
  l3_pp5[79] = l2_pp3to5_c[79];
  l3_pp5[80] = l2_pp0to2_c[80];
  l3_pp5[81] = l2_pp14[81];
  l3_pp5[82] = l2_pp13[82];
  l3_pp5[83] = l2_pp11[83];
  l3_pp5[84] = l2_pp10[84];
  l3_pp5[85] = l2_pp8[85];
  l3_pp5[86] = l2_pp7[86];
  l3_pp5.set_slc(87, l2_pp5.slc<14>(87));

  ui106 l3_pp6 = 0;
  l3_pp6[10] = l2_pp6[10];
  l3_pp6.set_slc(12, l2_pp6.slc<12>(12));
  l3_pp6.set_slc(24, l2_pp8.slc<2>(24));
  l3_pp6.set_slc(26, l2_pp11.slc<2>(26));
  l3_pp6.set_slc(28, l2_pp14.slc<2>(28));
  l3_pp6[30] = l2_pp0to2_c[30];
  l3_pp6[31] = l2_pp3to5_c[31];
  l3_pp6[32] = l2_pp6to8_c[32];
  l3_pp6[33] = l2_pp9to11_c[33];
  l3_pp6[34] = l2_pp12to14_c[34];
  l3_pp6.set_slc(35, l2_pp15to17_c.slc<42>(35));
  l3_pp6[77] = l2_pp12to14_c[77];
  l3_pp6[78] = l2_pp9to11_c[78];
  l3_pp6[79] = l2_pp6to8_c[79];
  l3_pp6[80] = l2_pp3to5_c[80];
  l3_pp6[81] = l2_pp0to2_c[81];
  l3_pp6[82] = l2_pp14[82];
  l3_pp6[83] = l2_pp12[83];
  l3_pp6[84] = l2_pp11[84];
  l3_pp6[85] = l2_pp9[85];
  l3_pp6[86] = l2_pp8[86];
  l3_pp6.set_slc(87, l2_pp6.slc<12>(87));

  ui106 l3_pp7 = 0;
  l3_pp7[12] = l2_pp7[12];
  l3_pp7.set_slc(14, l2_pp7.slc<10>(14));
  l3_pp7.set_slc(24, l2_pp9.slc<2>(24));
  l3_pp7.set_slc(26, l2_pp12.slc<2>(26));
  l3_pp7[28] = l2_pp15[28];
  l3_pp7[29] = l2_pp0to2_c[29];
  l3_pp7[30] = l2_pp3to5_c[30];
  l3_pp7[31] = l2_pp6to8_c[31];
  l3_pp7[32] = l2_pp9to11_c[32];
  l3_pp7[33] = l2_pp12to14_c[33];
  l3_pp7.set_slc(34, l2_pp0to2_s.slc<43>(34));
  l3_pp7[77] = l2_pp15to17_c[77];
  l3_pp7[78] = l2_pp12to14_c[78];
  l3_pp7[79] = l2_pp9to11_c[79];
  l3_pp7[80] = l2_pp6to8_c[80];
  l3_pp7[81] = l2_pp3to5_c[81];
  l3_pp7[82] = l2_pp0to2_c[82];
  l3_pp7[83] = l2_pp13[83];
  l3_pp7[84] = l2_pp12[84];
  l3_pp7[85] = l2_pp10[85];
  l3_pp7[86] = l2_pp9[86];
  l3_pp7.set_slc(87, l2_pp7.slc<10>(87));

  ui106 l3_pp8 = 0;
  l3_pp8[14] = l2_pp8[14];
  l3_pp8.set_slc(16, l2_pp8.slc<8>(16));
  l3_pp8.set_slc(24, l2_pp10.slc<2>(24));
  l3_pp8.set_slc(26, l2_pp13.slc<2>(26));
  l3_pp8[28] = l2_pp0to2_c[28];
  l3_pp8[29] = l2_pp3to5_c[29];
  l3_pp8[30] = l2_pp6to8_c[30];
  l3_pp8[31] = l2_pp9to11_c[31];
  l3_pp8.set_slc(32, l2_pp0to2_s.slc<2>(32));
  l3_pp8.set_slc(34, l2_pp3to5_s.slc<43>(34));
  l3_pp8.set_slc(77, l2_pp0to2_s.slc<2>(77));
  l3_pp8[79] = l2_pp12to14_c[79];
  l3_pp8[80] = l2_pp9to11_c[80];
  l3_pp8[81] = l2_pp6to8_c[81];
  l3_pp8[82] = l2_pp3to5_c[82];
  l3_pp8[83] = l2_pp0to2_c[83];
  l3_pp8[84] = l2_pp13[84];
  l3_pp8[85] = l2_pp11[85];
  l3_pp8[86] = l2_pp10[86];
  l3_pp8.set_slc(87, l2_pp8.slc<8>(87));

  ui106 l3_pp9 = 0;
  l3_pp9[16] = l2_pp9[16];
  l3_pp9.set_slc(18, l2_pp9.slc<6>(18));
  l3_pp9.set_slc(24, l2_pp11.slc<2>(24));
  l3_pp9[26] = l2_pp14[26];
  l3_pp9[27] = l2_pp0to2_c[27];
  l3_pp9[28] = l2_pp3to5_c[28];
  l3_pp9[29] = l2_pp6to8_c[29];
  l3_pp9.set_slc(30, l2_pp0to2_s.slc<2>(30));
  l3_pp9.set_slc(32, l2_pp3to5_s.slc<2>(32));
  l3_pp9.set_slc(34, l2_pp6to8_s.slc<43>(34));
  l3_pp9.set_slc(77, l2_pp3to5_s.slc<2>(77));
  l3_pp9.set_slc(79, l2_pp0to2_s.slc<2>(79));
  l3_pp9[81] = l2_pp9to11_c[81];
  l3_pp9[82] = l2_pp6to8_c[82];
  l3_pp9[83] = l2_pp3to5_c[83];
  l3_pp9[84] = l2_pp0to2_c[84];
  l3_pp9[85] = l2_pp12[85];
  l3_pp9[86] = l2_pp11[86];
  l3_pp9.set_slc(87, l2_pp9.slc<6>(87));

  ui106 l3_pp10 = 0;
  l3_pp10[18] = l2_pp10[18];
  l3_pp10.set_slc(20, l2_pp10.slc<4>(20));
  l3_pp10.set_slc(24, l2_pp12.slc<2>(24));
  l3_pp10[26] = l2_pp0to2_c[26];
  l3_pp10[27] = l2_pp3to5_c[27];
  l3_pp10.set_slc(28, l2_pp0to2_s.slc<2>(28));
  l3_pp10.set_slc(30, l2_pp3to5_s.slc<2>(30));
  l3_pp10.set_slc(32, l2_pp6to8_s.slc<2>(32));
  l3_pp10.set_slc(34, l2_pp9to11_s.slc<43>(34));
  l3_pp10.set_slc(77, l2_pp6to8_s.slc<2>(77));
  l3_pp10.set_slc(79, l2_pp3to5_s.slc<2>(79));
  l3_pp10.set_slc(81, l2_pp0to2_s.slc<2>(81));
  l3_pp10[83] = l2_pp6to8_c[83];
  l3_pp10[84] = l2_pp3to5_c[84];
  l3_pp10[85] = l2_pp0to2_c[85];
  l3_pp10[86] = l2_pp12[86];
  l3_pp10.set_slc(87, l2_pp10.slc<4>(87));

  ui106 l3_pp11 = 0;
  l3_pp11[20] = l2_pp11[20];
  l3_pp11.set_slc(22, l2_pp11.slc<2>(22));
  l3_pp11[24] = l2_pp13[24];
  l3_pp11[25] = l2_pp0to2_c[25];
  l3_pp11.set_slc(26, l2_pp0to2_s.slc<2>(26));
  l3_pp11.set_slc(28, l2_pp3to5_s.slc<2>(28));
  l3_pp11.set_slc(30, l2_pp6to8_s.slc<2>(30));
  l3_pp11.set_slc(32, l2_pp9to11_s.slc<2>(32));
  l3_pp11.set_slc(34, l2_pp12to14_s.slc<43>(34));
  l3_pp11.set_slc(77, l2_pp9to11_s.slc<2>(77));
  l3_pp11.set_slc(79, l2_pp6to8_s.slc<2>(79));
  l3_pp11.set_slc(81, l2_pp3to5_s.slc<2>(81));
  l3_pp11.set_slc(83, l2_pp0to2_s.slc<2>(83));
  l3_pp11[85] = l2_pp3to5_c[85];
  l3_pp11[86] = l2_pp0to2_c[86];
  l3_pp11.set_slc(87, l2_pp11.slc<2>(87));

  ui106 l3_pp12 = 0;
  l3_pp12[22] = l2_pp12[22];
  l3_pp12.set_slc(24, l2_pp0to2_s.slc<2>(24));
  l3_pp12.set_slc(26, l2_pp3to5_s.slc<2>(26));
  l3_pp12.set_slc(28, l2_pp6to8_s.slc<2>(28));
  l3_pp12.set_slc(30, l2_pp9to11_s.slc<2>(30));
  l3_pp12.set_slc(32, l2_pp12to14_s.slc<2>(32));
  l3_pp12.set_slc(34, l2_pp15to17_s.slc<43>(34));
  l3_pp12.set_slc(77, l2_pp12to14_s.slc<2>(77));
  l3_pp12.set_slc(79, l2_pp9to11_s.slc<2>(79));
  l3_pp12.set_slc(81, l2_pp6to8_s.slc<2>(81));
  l3_pp12.set_slc(83, l2_pp3to5_s.slc<2>(83));
  l3_pp12.set_slc(85, l2_pp0to2_s.slc<2>(85));
  l3_pp12[87] = l2_pp0to2_c[87];


  // Max bit column depth after Dadda level #3 is 9
  ui106 l3_pp0to2_s = 0, l3_pp0to2_c = 0;
  l3_pp0to2_s.set_slc(16, ui2(l3_pp0.slc<2>(16) ^ l3_pp1.slc<2>(16)));
  l3_pp0to2_c.set_slc(17, ui2(l3_pp0.slc<2>(16) & l3_pp1.slc<2>(16)));
  l3_pp0to2_s.set_slc(18, ui76(l3_pp0.slc<76>(18) ^ l3_pp1.slc<76>(18) ^ l3_pp2.slc<76>(18)));
  l3_pp0to2_c.set_slc(19, ui76(l3_pp0.slc<76>(18) & l3_pp1.slc<76>(18) | l3_pp0.slc<76>(18) & l3_pp2.slc<76>(18) | l3_pp1.slc<76>(18) & l3_pp2.slc<76>(18)));
  l3_pp0to2_s[94] = l3_pp0[94] ^ l3_pp1[94];
  l3_pp0to2_c[95] = l3_pp0[94] & l3_pp1[94];
  ui106 l3_pp3to5_s = 0, l3_pp3to5_c = 0;
  l3_pp3to5_s.set_slc(18, ui2(l3_pp3.slc<2>(18) ^ l3_pp4.slc<2>(18)));
  l3_pp3to5_c.set_slc(19, ui2(l3_pp3.slc<2>(18) & l3_pp4.slc<2>(18)));
  l3_pp3to5_s.set_slc(20, ui72(l3_pp3.slc<72>(20) ^ l3_pp4.slc<72>(20) ^ l3_pp5.slc<72>(20)));
  l3_pp3to5_c.set_slc(21, ui72(l3_pp3.slc<72>(20) & l3_pp4.slc<72>(20) | l3_pp3.slc<72>(20) & l3_pp5.slc<72>(20) | l3_pp4.slc<72>(20) & l3_pp5.slc<72>(20)));
  l3_pp3to5_s[92] = l3_pp3[92] ^ l3_pp4[92];
  l3_pp3to5_c[93] = l3_pp3[92] & l3_pp4[92];
  ui106 l3_pp6to8_s = 0, l3_pp6to8_c = 0;
  l3_pp6to8_s.set_slc(20, ui2(l3_pp6.slc<2>(20) ^ l3_pp7.slc<2>(20)));
  l3_pp6to8_c.set_slc(21, ui2(l3_pp6.slc<2>(20) & l3_pp7.slc<2>(20)));
  l3_pp6to8_s.set_slc(22, ui68(l3_pp6.slc<68>(22) ^ l3_pp7.slc<68>(22) ^ l3_pp8.slc<68>(22)));
  l3_pp6to8_c.set_slc(23, ui68(l3_pp6.slc<68>(22) & l3_pp7.slc<68>(22) | l3_pp6.slc<68>(22) & l3_pp8.slc<68>(22) | l3_pp7.slc<68>(22) & l3_pp8.slc<68>(22)));
  l3_pp6to8_s[90] = l3_pp6[90] ^ l3_pp7[90];
  l3_pp6to8_c[91] = l3_pp6[90] & l3_pp7[90];
  ui106 l3_pp9to11_s = 0, l3_pp9to11_c = 0;
  l3_pp9to11_s.set_slc(22, ui2(l3_pp9.slc<2>(22) ^ l3_pp10.slc<2>(22)));
  l3_pp9to11_c.set_slc(23, ui2(l3_pp9.slc<2>(22) & l3_pp10.slc<2>(22)));
  l3_pp9to11_s.set_slc(24, ui64(l3_pp9.slc<64>(24) ^ l3_pp10.slc<64>(24) ^ l3_pp11.slc<64>(24)));
  l3_pp9to11_c.set_slc(25, ui64(l3_pp9.slc<64>(24) & l3_pp10.slc<64>(24) | l3_pp9.slc<64>(24) & l3_pp11.slc<64>(24) | l3_pp10.slc<64>(24) & l3_pp11.slc<64>(24)));
  l3_pp9to11_s[88] = l3_pp9[88] ^ l3_pp10[88];
  l3_pp9to11_c[89] = l3_pp9[88] & l3_pp10[88];

  // Dadda level 4 beginning dot diagram:
  // 111111
  // 000000999999999988888888887777777777666666666655555555554444444444333333333322222222221111111111
  // 5432109876543210987654321098765432109876543210987654321098765432109876543210987654321098765432109876543210
  // ********************************************************************************************************
  //  *******************************************************************************************************
  //  ***************************************************************************************************** *
  //   ************************************************************************************************** *
  //    *********************************************************************************************** *
  //      ******************************************************************************************* *
  //        *************************************************************************************** *
  //          *********************************************************************************** *
  //           ******************************************************************************** *

  ui106 l4_pp0 = 0;
  l4_pp0.set_slc(2, l3_pp0.slc<14>(2));
  l4_pp0.set_slc(16, l3_pp2.slc<2>(16));
  l4_pp0.set_slc(18, l3_pp5.slc<2>(18));
  l4_pp0.set_slc(20, l3_pp8.slc<2>(20));
  l4_pp0.set_slc(22, l3_pp11.slc<2>(22));
  l4_pp0.set_slc(24, l3_pp12.slc<64>(24));
  l4_pp0[88] = l3_pp11[88];
  l4_pp0[89] = l3_pp9[89];
  l4_pp0[90] = l3_pp8[90];
  l4_pp0[91] = l3_pp6[91];
  l4_pp0[92] = l3_pp5[92];
  l4_pp0[93] = l3_pp3[93];
  l4_pp0[94] = l3_pp2[94];
  l4_pp0.set_slc(95, l3_pp0.slc<11>(95));

  ui106 l4_pp1 = 0;
  l4_pp1.set_slc(2, l3_pp1.slc<14>(2));
  l4_pp1.set_slc(16, l3_pp3.slc<2>(16));
  l4_pp1.set_slc(18, l3_pp6.slc<2>(18));
  l4_pp1.set_slc(20, l3_pp9.slc<2>(20));
  l4_pp1[22] = l3_pp12[22];
  l4_pp1.set_slc(23, l3_pp0to2_c.slc<66>(23));
  l4_pp1[89] = l3_pp10[89];
  l4_pp1[90] = l3_pp9[90];
  l4_pp1[91] = l3_pp7[91];
  l4_pp1[92] = l3_pp6[92];
  l4_pp1[93] = l3_pp4[93];
  l4_pp1[94] = l3_pp3[94];
  l4_pp1.set_slc(95, l3_pp1.slc<10>(95));

  ui106 l4_pp2 = 0;
  l4_pp2[2] = l3_pp2[2];
  l4_pp2.set_slc(4, l3_pp2.slc<12>(4));
  l4_pp2.set_slc(16, l3_pp4.slc<2>(16));
  l4_pp2.set_slc(18, l3_pp7.slc<2>(18));
  l4_pp2.set_slc(20, l3_pp10.slc<2>(20));
  l4_pp2[22] = l3_pp0to2_c[22];
  l4_pp2.set_slc(23, l3_pp3to5_c.slc<66>(23));
  l4_pp2[89] = l3_pp0to2_c[89];
  l4_pp2[90] = l3_pp10[90];
  l4_pp2[91] = l3_pp8[91];
  l4_pp2[92] = l3_pp7[92];
  l4_pp2[93] = l3_pp5[93];
  l4_pp2[94] = l3_pp4[94];
  l4_pp2.set_slc(95, l3_pp2.slc<10>(95));

  ui106 l4_pp3 = 0;
  l4_pp3[4] = l3_pp3[4];
  l4_pp3.set_slc(6, l3_pp3.slc<10>(6));
  l4_pp3.set_slc(16, l3_pp5.slc<2>(16));
  l4_pp3.set_slc(18, l3_pp8.slc<2>(18));
  l4_pp3[20] = l3_pp11[20];
  l4_pp3[21] = l3_pp0to2_c[21];
  l4_pp3[22] = l3_pp3to5_c[22];
  l4_pp3.set_slc(23, l3_pp6to8_c.slc<66>(23));
  l4_pp3[89] = l3_pp3to5_c[89];
  l4_pp3[90] = l3_pp0to2_c[90];
  l4_pp3[91] = l3_pp9[91];
  l4_pp3[92] = l3_pp8[92];
  l4_pp3[93] = l3_pp6[93];
  l4_pp3[94] = l3_pp5[94];
  l4_pp3.set_slc(95, l3_pp3.slc<9>(95));

  ui106 l4_pp4 = 0;
  l4_pp4[6] = l3_pp4[6];
  l4_pp4.set_slc(8, l3_pp4.slc<8>(8));
  l4_pp4.set_slc(16, l3_pp6.slc<2>(16));
  l4_pp4.set_slc(18, l3_pp9.slc<2>(18));
  l4_pp4[20] = l3_pp0to2_c[20];
  l4_pp4[21] = l3_pp3to5_c[21];
  l4_pp4[22] = l3_pp6to8_c[22];
  l4_pp4.set_slc(23, l3_pp9to11_c.slc<66>(23));
  l4_pp4[89] = l3_pp6to8_c[89];
  l4_pp4[90] = l3_pp3to5_c[90];
  l4_pp4[91] = l3_pp0to2_c[91];
  l4_pp4[92] = l3_pp9[92];
  l4_pp4[93] = l3_pp7[93];
  l4_pp4[94] = l3_pp6[94];
  l4_pp4.set_slc(95, l3_pp4.slc<8>(95));

  ui106 l4_pp5 = 0;
  l4_pp5[8] = l3_pp5[8];
  l4_pp5.set_slc(10, l3_pp5.slc<6>(10));
  l4_pp5.set_slc(16, l3_pp7.slc<2>(16));
  l4_pp5[18] = l3_pp10[18];
  l4_pp5[19] = l3_pp0to2_c[19];
  l4_pp5[20] = l3_pp3to5_c[20];
  l4_pp5[21] = l3_pp6to8_c[21];
  l4_pp5.set_slc(22, l3_pp0to2_s.slc<67>(22));
  l4_pp5[89] = l3_pp9to11_c[89];
  l4_pp5[90] = l3_pp6to8_c[90];
  l4_pp5[91] = l3_pp3to5_c[91];
  l4_pp5[92] = l3_pp0to2_c[92];
  l4_pp5[93] = l3_pp8[93];
  l4_pp5[94] = l3_pp7[94];
  l4_pp5.set_slc(95, l3_pp5.slc<6>(95));

  ui106 l4_pp6 = 0;
  l4_pp6[10] = l3_pp6[10];
  l4_pp6.set_slc(12, l3_pp6.slc<4>(12));
  l4_pp6.set_slc(16, l3_pp8.slc<2>(16));
  l4_pp6[18] = l3_pp0to2_c[18];
  l4_pp6[19] = l3_pp3to5_c[19];
  l4_pp6.set_slc(20, l3_pp0to2_s.slc<2>(20));
  l4_pp6.set_slc(22, l3_pp3to5_s.slc<67>(22));
  l4_pp6.set_slc(89, l3_pp0to2_s.slc<2>(89));
  l4_pp6[91] = l3_pp6to8_c[91];
  l4_pp6[92] = l3_pp3to5_c[92];
  l4_pp6[93] = l3_pp0to2_c[93];
  l4_pp6[94] = l3_pp8[94];
  l4_pp6.set_slc(95, l3_pp6.slc<4>(95));

  ui106 l4_pp7 = 0;
  l4_pp7[12] = l3_pp7[12];
  l4_pp7.set_slc(14, l3_pp7.slc<2>(14));
  l4_pp7[16] = l3_pp9[16];
  l4_pp7[17] = l3_pp0to2_c[17];
  l4_pp7.set_slc(18, l3_pp0to2_s.slc<2>(18));
  l4_pp7.set_slc(20, l3_pp3to5_s.slc<2>(20));
  l4_pp7.set_slc(22, l3_pp6to8_s.slc<67>(22));
  l4_pp7.set_slc(89, l3_pp3to5_s.slc<2>(89));
  l4_pp7.set_slc(91, l3_pp0to2_s.slc<2>(91));
  l4_pp7[93] = l3_pp3to5_c[93];
  l4_pp7[94] = l3_pp0to2_c[94];
  l4_pp7.set_slc(95, l3_pp7.slc<2>(95));

  ui106 l4_pp8 = 0;
  l4_pp8[14] = l3_pp8[14];
  l4_pp8.set_slc(16, l3_pp0to2_s.slc<2>(16));
  l4_pp8.set_slc(18, l3_pp3to5_s.slc<2>(18));
  l4_pp8.set_slc(20, l3_pp6to8_s.slc<2>(20));
  l4_pp8.set_slc(22, l3_pp9to11_s.slc<67>(22));
  l4_pp8.set_slc(89, l3_pp6to8_s.slc<2>(89));
  l4_pp8.set_slc(91, l3_pp3to5_s.slc<2>(91));
  l4_pp8.set_slc(93, l3_pp0to2_s.slc<2>(93));
  l4_pp8[95] = l3_pp0to2_c[95];


  // Max bit column depth after Dadda level #4 is 6
  ui106 l4_pp0to2_s = 0, l4_pp0to2_c = 0;
  l4_pp0to2_s.set_slc(10, ui2(l4_pp0.slc<2>(10) ^ l4_pp1.slc<2>(10)));
  l4_pp0to2_c.set_slc(11, ui2(l4_pp0.slc<2>(10) & l4_pp1.slc<2>(10)));
  l4_pp0to2_s.set_slc(12, ui88(l4_pp0.slc<88>(12) ^ l4_pp1.slc<88>(12) ^ l4_pp2.slc<88>(12)));
  l4_pp0to2_c.set_slc(13, ui88(l4_pp0.slc<88>(12) & l4_pp1.slc<88>(12) | l4_pp0.slc<88>(12) & l4_pp2.slc<88>(12) | l4_pp1.slc<88>(12) & l4_pp2.slc<88>(12)));
  l4_pp0to2_s[100] = l4_pp0[100] ^ l4_pp1[100];
  l4_pp0to2_c[101] = l4_pp0[100] & l4_pp1[100];
  ui106 l4_pp3to5_s = 0, l4_pp3to5_c = 0;
  l4_pp3to5_s.set_slc(12, ui2(l4_pp3.slc<2>(12) ^ l4_pp4.slc<2>(12)));
  l4_pp3to5_c.set_slc(13, ui2(l4_pp3.slc<2>(12) & l4_pp4.slc<2>(12)));
  l4_pp3to5_s.set_slc(14, ui84(l4_pp3.slc<84>(14) ^ l4_pp4.slc<84>(14) ^ l4_pp5.slc<84>(14)));
  l4_pp3to5_c.set_slc(15, ui84(l4_pp3.slc<84>(14) & l4_pp4.slc<84>(14) | l4_pp3.slc<84>(14) & l4_pp5.slc<84>(14) | l4_pp4.slc<84>(14) & l4_pp5.slc<84>(14)));
  l4_pp3to5_s[98] = l4_pp3[98] ^ l4_pp4[98];
  l4_pp3to5_c[99] = l4_pp3[98] & l4_pp4[98];
  ui106 l4_pp6to8_s = 0, l4_pp6to8_c = 0;
  l4_pp6to8_s.set_slc(14, ui2(l4_pp6.slc<2>(14) ^ l4_pp7.slc<2>(14)));
  l4_pp6to8_c.set_slc(15, ui2(l4_pp6.slc<2>(14) & l4_pp7.slc<2>(14)));
  l4_pp6to8_s.set_slc(16, ui80(l4_pp6.slc<80>(16) ^ l4_pp7.slc<80>(16) ^ l4_pp8.slc<80>(16)));
  l4_pp6to8_c.set_slc(17, ui80(l4_pp6.slc<80>(16) & l4_pp7.slc<80>(16) | l4_pp6.slc<80>(16) & l4_pp8.slc<80>(16) | l4_pp7.slc<80>(16) & l4_pp8.slc<80>(16)));
  l4_pp6to8_s[96] = l4_pp6[96] ^ l4_pp7[96];
  l4_pp6to8_c[97] = l4_pp6[96] & l4_pp7[96];

  // Dadda level 5 beginning dot diagram:
  // 111111
  // 000000999999999988888888887777777777666666666655555555554444444444333333333322222222221111111111
  // 5432109876543210987654321098765432109876543210987654321098765432109876543210987654321098765432109876543210
  // ********************************************************************************************************
  //  *******************************************************************************************************
  //  ***************************************************************************************************** *
  //   ************************************************************************************************** *
  //    *********************************************************************************************** *
  //     ******************************************************************************************** *

  ui106 l5_pp0 = 0;
  l5_pp0.set_slc(2, l4_pp0.slc<8>(2));
  l5_pp0.set_slc(10, l4_pp2.slc<2>(10));
  l5_pp0.set_slc(12, l4_pp5.slc<2>(12));
  l5_pp0[14] = l4_pp8[14];
  l5_pp0.set_slc(15, l4_pp0to2_c.slc<82>(15));
  l5_pp0[97] = l4_pp6[97];
  l5_pp0[98] = l4_pp5[98];
  l5_pp0[99] = l4_pp3[99];
  l5_pp0[100] = l4_pp2[100];
  l5_pp0.set_slc(101, l4_pp0.slc<5>(101));

  ui106 l5_pp1 = 0;
  l5_pp1.set_slc(2, l4_pp1.slc<8>(2));
  l5_pp1.set_slc(10, l4_pp3.slc<2>(10));
  l5_pp1.set_slc(12, l4_pp6.slc<2>(12));
  l5_pp1[14] = l4_pp0to2_c[14];
  l5_pp1.set_slc(15, l4_pp3to5_c.slc<82>(15));
  l5_pp1[97] = l4_pp0to2_c[97];
  l5_pp1[98] = l4_pp6[98];
  l5_pp1[99] = l4_pp4[99];
  l5_pp1[100] = l4_pp3[100];
  l5_pp1.set_slc(101, l4_pp1.slc<4>(101));

  ui106 l5_pp2 = 0;
  l5_pp2[2] = l4_pp2[2];
  l5_pp2.set_slc(4, l4_pp2.slc<6>(4));
  l5_pp2.set_slc(10, l4_pp4.slc<2>(10));
  l5_pp2[12] = l4_pp7[12];
  l5_pp2[13] = l4_pp0to2_c[13];
  l5_pp2[14] = l4_pp3to5_c[14];
  l5_pp2.set_slc(15, l4_pp6to8_c.slc<82>(15));
  l5_pp2[97] = l4_pp3to5_c[97];
  l5_pp2[98] = l4_pp0to2_c[98];
  l5_pp2[99] = l4_pp5[99];
  l5_pp2[100] = l4_pp4[100];
  l5_pp2.set_slc(101, l4_pp2.slc<4>(101));

  ui106 l5_pp3 = 0;
  l5_pp3[4] = l4_pp3[4];
  l5_pp3.set_slc(6, l4_pp3.slc<4>(6));
  l5_pp3.set_slc(10, l4_pp5.slc<2>(10));
  l5_pp3[12] = l4_pp0to2_c[12];
  l5_pp3[13] = l4_pp3to5_c[13];
  l5_pp3.set_slc(14, l4_pp0to2_s.slc<83>(14));
  l5_pp3[97] = l4_pp6to8_c[97];
  l5_pp3[98] = l4_pp3to5_c[98];
  l5_pp3[99] = l4_pp0to2_c[99];
  l5_pp3[100] = l4_pp5[100];
  l5_pp3.set_slc(101, l4_pp3.slc<3>(101));

  ui106 l5_pp4 = 0;
  l5_pp4[6] = l4_pp4[6];
  l5_pp4.set_slc(8, l4_pp4.slc<2>(8));
  l5_pp4[10] = l4_pp6[10];
  l5_pp4[11] = l4_pp0to2_c[11];
  l5_pp4.set_slc(12, l4_pp0to2_s.slc<2>(12));
  l5_pp4.set_slc(14, l4_pp3to5_s.slc<83>(14));
  l5_pp4.set_slc(97, l4_pp0to2_s.slc<2>(97));
  l5_pp4[99] = l4_pp3to5_c[99];
  l5_pp4[100] = l4_pp0to2_c[100];
  l5_pp4.set_slc(101, l4_pp4.slc<2>(101));

  ui106 l5_pp5 = 0;
  l5_pp5[8] = l4_pp5[8];
  l5_pp5.set_slc(10, l4_pp0to2_s.slc<2>(10));
  l5_pp5.set_slc(12, l4_pp3to5_s.slc<2>(12));
  l5_pp5.set_slc(14, l4_pp6to8_s.slc<83>(14));
  l5_pp5.set_slc(97, l4_pp3to5_s.slc<2>(97));
  l5_pp5.set_slc(99, l4_pp0to2_s.slc<2>(99));
  l5_pp5[101] = l4_pp0to2_c[101];


  // Max bit column depth after Dadda level #5 is 4
  ui106 l5_pp0to2_s = 0, l5_pp0to2_c = 0;
  l5_pp0to2_s.set_slc(6, ui2(l5_pp0.slc<2>(6) ^ l5_pp1.slc<2>(6)));
  l5_pp0to2_c.set_slc(7, ui2(l5_pp0.slc<2>(6) & l5_pp1.slc<2>(6)));
  l5_pp0to2_s.set_slc(8, ui96(l5_pp0.slc<96>(8) ^ l5_pp1.slc<96>(8) ^ l5_pp2.slc<96>(8)));
  l5_pp0to2_c.set_slc(9, ui96(l5_pp0.slc<96>(8) & l5_pp1.slc<96>(8) | l5_pp0.slc<96>(8) & l5_pp2.slc<96>(8) | l5_pp1.slc<96>(8) & l5_pp2.slc<96>(8)));
  ui106 l5_pp3to5_s = 0, l5_pp3to5_c = 0;
  l5_pp3to5_s.set_slc(8, ui2(l5_pp3.slc<2>(8) ^ l5_pp4.slc<2>(8)));
  l5_pp3to5_c.set_slc(9, ui2(l5_pp3.slc<2>(8) & l5_pp4.slc<2>(8)));
  l5_pp3to5_s.set_slc(10, ui92(l5_pp3.slc<92>(10) ^ l5_pp4.slc<92>(10) ^ l5_pp5.slc<92>(10)));
  l5_pp3to5_c.set_slc(11, ui92(l5_pp3.slc<92>(10) & l5_pp4.slc<92>(10) | l5_pp3.slc<92>(10) & l5_pp5.slc<92>(10) | l5_pp4.slc<92>(10) & l5_pp5.slc<92>(10)));
  l5_pp3to5_s[102] = l5_pp3[102] ^ l5_pp4[102];
  l5_pp3to5_c[103] = l5_pp3[102] & l5_pp4[102];

  // Dadda level 6 beginning dot diagram:
  // 111111
  // 000000999999999988888888887777777777666666666655555555554444444444333333333322222222221111111111
  // 5432109876543210987654321098765432109876543210987654321098765432109876543210987654321098765432109876543210
  // ********************************************************************************************************
  //  *******************************************************************************************************
  //  ***************************************************************************************************** *
  //  *************************************************************************************************** *

  ui106 l6_pp0 = 0;
  l6_pp0.set_slc(2, l5_pp0.slc<4>(2));
  l6_pp0.set_slc(6, l5_pp2.slc<2>(6));
  l6_pp0[8] = l5_pp5[8];
  l6_pp0.set_slc(9, l5_pp0to2_c.slc<94>(9));
  l6_pp0[103] = l5_pp3[103];
  l6_pp0.set_slc(104, l5_pp0.slc<2>(104));

  ui106 l6_pp1 = 0;
  l6_pp1.set_slc(2, l5_pp1.slc<4>(2));
  l6_pp1.set_slc(6, l5_pp3.slc<2>(6));
  l6_pp1[8] = l5_pp0to2_c[8];
  l6_pp1.set_slc(9, l5_pp3to5_c.slc<94>(9));
  l6_pp1[103] = l5_pp0to2_c[103];
  l6_pp1[104] = l5_pp1[104];

  ui106 l6_pp2 = 0;
  l6_pp2[2] = l5_pp2[2];
  l6_pp2.set_slc(4, l5_pp2.slc<2>(4));
  l6_pp2[6] = l5_pp4[6];
  l6_pp2[7] = l5_pp0to2_c[7];
  l6_pp2.set_slc(8, l5_pp0to2_s.slc<95>(8));
  l6_pp2[103] = l5_pp3to5_c[103];
  l6_pp2[104] = l5_pp2[104];

  ui106 l6_pp3 = 0;
  l6_pp3[4] = l5_pp3[4];
  l6_pp3.set_slc(6, l5_pp0to2_s.slc<2>(6));
  l6_pp3.set_slc(8, l5_pp3to5_s.slc<95>(8));
  l6_pp3[103] = l5_pp0to2_s[103];
  l6_pp3[104] = l5_pp0to2_c[104];


  // Max bit column depth after Dadda level #6 is 3
  ui106 l6_pp0to2_s = 0, l6_pp0to2_c = 0;
  l6_pp0to2_s.set_slc(4, ui2(l6_pp0.slc<2>(4) ^ l6_pp1.slc<2>(4)));
  l6_pp0to2_c.set_slc(5, ui2(l6_pp0.slc<2>(4) & l6_pp1.slc<2>(4)));
  l6_pp0to2_s.set_slc(6, ui99(l6_pp0.slc<99>(6) ^ l6_pp1.slc<99>(6) ^ l6_pp2.slc<99>(6)));
  l6_pp0to2_c.set_slc(7, ui99(l6_pp0.slc<99>(6) & l6_pp1.slc<99>(6) | l6_pp0.slc<99>(6) & l6_pp2.slc<99>(6) | l6_pp1.slc<99>(6) & l6_pp2.slc<99>(6)));

  // Dadda level 7 beginning dot diagram:
  // 111111
  // 000000999999999988888888887777777777666666666655555555554444444444333333333322222222221111111111
  // 5432109876543210987654321098765432109876543210987654321098765432109876543210987654321098765432109876543210
  // ********************************************************************************************************
  // ********************************************************************************************************
  //  ***************************************************************************************************** *

  ui106 l7_pp0 = 0;
  l7_pp0.set_slc(2, l6_pp0.slc<2>(2));
  l7_pp0.set_slc(4, l6_pp2.slc<2>(4));
  l7_pp0.set_slc(6, l6_pp3.slc<99>(6));
  l7_pp0[105] = l6_pp0[105];

  ui106 l7_pp1 = 0;
  l7_pp1.set_slc(2, l6_pp1.slc<2>(2));
  l7_pp1[4] = l6_pp3[4];
  l7_pp1.set_slc(5, l6_pp0to2_c.slc<101>(5));

  ui106 l7_pp2 = 0;
  l7_pp2[2] = l6_pp2[2];
  l7_pp2.set_slc(4, l6_pp0to2_s.slc<101>(4));


  // Max bit column depth after Dadda level #7 is 2
  ui106 l7_pp0to2_s = 0, l7_pp0to2_c = 0;
  l7_pp0to2_s.set_slc(2, ui2(l7_pp0.slc<2>(2) ^ l7_pp1.slc<2>(2)));
  l7_pp0to2_c.set_slc(3, ui2(l7_pp0.slc<2>(2) & l7_pp1.slc<2>(2)));
  l7_pp0to2_s.set_slc(4, ui101(l7_pp0.slc<101>(4) ^ l7_pp1.slc<101>(4) ^ l7_pp2.slc<101>(4)));
  l7_pp0to2_c.set_slc(5, ui101(l7_pp0.slc<101>(4) & l7_pp1.slc<101>(4) | l7_pp0.slc<101>(4) & l7_pp2.slc<101>(4) | l7_pp1.slc<101>(4) & l7_pp2.slc<101>(4)));
  l7_pp0to2_s[105] = l7_pp0[105] ^ l7_pp1[105];

  // Final dot diagram:
  // 111111
  // 000000999999999988888888887777777777666666666655555555554444444444333333333322222222221111111111
  // 5432109876543210987654321098765432109876543210987654321098765432109876543210987654321098765432109876543210
  // **********************************************************************************************************
  // ******************************************************************************************************** *

  ui106 final_pp0 = 0;
  final_pp0.set_slc(0, pp0.slc<2>(0));
  final_pp0[2] = l7_pp2[2];
  final_pp0.set_slc(3, l7_pp0to2_c.slc<103>(3));

  ui106 final_pp1 = 0;
  final_pp1[0] = pp1[0];
  final_pp1.set_slc(2, l7_pp0to2_s.slc<104>(2));


  return final_pp0 + final_pp1;
}

// Booth multiplier:

ui106 imul(ui52 mana, ui52 manb, bool expaZero, bool expbZero) {
  array<ui57, 27> pp; // partial product array
  ui53 multiplier = manb;
  multiplier <<= 1;
  for (uint i=0; i<27; i++) {
    ui3 slice = multiplier.slc<3>(2*i);
    bool sign = slice[2], signLast = slice[0];
    int enc = slice[0] + slice[1] - 2 * slice[2];
    ui53 mux;
    switch (enc) {
    case 0: mux = 0; break;
    case 1: case -1: mux = mana; break;
    case 2: case -2: mux = ui53(mana) << 1;
    }
    if (sign) {
      mux = ~mux;
    }

    pp[i] = 0;

    if (i == 0) {
      pp[i].set_slc(0, mux);
      pp[i][53] = sign;
      pp[i][54] = sign;
      pp[i][55] = !sign;
      pp[i][56] = 0;
    }
    else {
      pp[i][0] = signLast;
      pp[i][1] = 0;
      pp[i].set_slc(2, mux);
      pp[i][55] = !sign;
      pp[i][56] = i < 26;
    }
  }

  ui52 ia = expaZero ? ui52(0) : manb;
  ui53 ib = expbZero ? ui52(0) : mana;
  ib[52] = !expaZero && !expbZero;

  ui106 sum;
  sum = compress (
    ui106(pp[0]),
    ui106(pp[1]),
    ui106(pp[2]) << 2,
    ui106(pp[3]) << 4,
    ui106(pp[4]) << 6,
    ui106(pp[5]) << 8,
    ui106(pp[6]) << 10,
    ui106(pp[7]) << 12,
    ui106(pp[8]) << 14,
    ui106(pp[9]) << 16,
    ui106(pp[10]) << 18,
    ui106(pp[11]) << 20,
    ui106(pp[12]) << 22,
    ui106(pp[13]) << 24,
    ui106(pp[14]) << 26,
    ui106(pp[15]) << 28,
    ui106(pp[16]) << 30,
    ui106(pp[17]) << 32,
    ui106(pp[18]) << 34,
    ui106(pp[19]) << 36,
    ui106(pp[20]) << 38,
    ui106(pp[21]) << 40,
    ui106(pp[22]) << 42,
    ui106(pp[23]) << 44,
    ui106(pp[24]) << 46,
    ui106(pp[25]) << 48,
    ui106(pp[26]) << 50,
    ui106(ib) << 52,
    ui106(ia) << 52
  );
  return sum;
}

// RAC end

int main() {

  bool expa_zero = 0;
  bool expb_zero = 0;
  ui52 fraca = 3;
  ui52 fracb = 5;

  ui106 sum = imul(fraca, fracb, expa_zero, expb_zero);

  DBG(sum);

  return 0;
}
