// #define SLEC

#include <stdio.h>
#include <math.h>
#include <string>
#include <vector>

#include "ac_fixed.h"
#include "ac_int.h"
#include "rac.h"

using namespace std;

#ifdef SLEC

#include "ac_probe.h"

#else

namespace ac {
  template <typename T>
  void probe_map(const char*prbnm, T inp) {}
}

#endif

// RAC begin

typedef ac_int<2, false> ui2;
typedef ac_int<3, false> ui3;
typedef ac_int<4, false> ui4;
typedef ac_int<5, false> ui5;
typedef ac_int<6, false> ui6;
typedef ac_int<7, false> ui7;
typedef ac_int<8, false> ui8;
typedef ac_int<9, false> ui9;
typedef ac_int<10, false> ui10;
typedef ac_int<11, false> ui11;
typedef ac_int<12, false> ui12;
typedef ac_int<16, false> ui16;
typedef ac_int<17, false> ui17;
typedef ac_int<23, false> ui23;
typedef ac_int<24, false> ui24;
typedef ac_int<26, false> ui26;
typedef ac_int<31, false> ui31;
typedef ac_int<32, false> ui32;
typedef ac_int<33, false> ui33;
typedef ac_int<48, false> ui48;
typedef ac_int<50, false> ui50;
typedef ac_int<51, false> ui51;
typedef ac_int<52, false> ui52;
typedef ac_int<53, false> ui53;
typedef ac_int<64, false> ui64;
typedef ac_int<65, false> ui65;
typedef ac_int<76, false> ui76;
typedef ac_int<77, false> ui77;
typedef ac_int<78, false> ui78;
typedef ac_int<113, false> ui113;
typedef ac_int<128, false> ui128;
typedef ac_int<10, true> si10;
typedef ac_int<32, true> si32;

// The multiplier returns an unnormalized representation of the product, {pSign, pExp[8:0], pMant[47:0]},
// with exponent bias 255 and 47 fractional bits, i.e., the value represented is
//    (-1)^pSign * 2^(pExp - 255 - 47) * pMant.
// The special cases of a NaN, infinity, and zero result are signaled by the special exponent values
// 511, 1, and 0, respectively.  (In the remaining case, the exponent lies in the interval [4, 510].)

tuple<bool, ui9, ui48> fmul32(ui32 a, ui32 b) {

  // Special cases:
  bool aZero = a.slc<31>(0) == 0;
  bool bZero = b.slc<31>(0) == 0;
  bool aNaN = a.slc<8>(23) == 0xFF && a.slc<23>(0) != 0;
  bool bNaN = b.slc<8>(23) == 0xFF && b.slc<23>(0) != 0;
  bool aInf = a.slc<8>(23) == 0xFF && a.slc<23>(0) == 0;
  bool bInf = b.slc<8>(23) == 0xFF && b.slc<23>(0) == 0;

  // Product sign:
  bool pSign = a[31] ^ b[31];

  // Product exponent:
  ui8 aExp = a.slc<8>(23) == 0 ? ui8(1) : a.slc<8>(23);
  ui8 bExp = b.slc<8>(23) == 0 ? ui8(1) : b.slc<8>(23);
  ui9 pExp;
  if (aNaN || bNaN || aInf && bZero || aZero && bInf) {
    pExp = 511;
  }
  else if (aInf || bInf) {
    pExp = 1;
  }
  else if (aZero || bZero) {
    pExp = 0;
  }
  else {
    pExp = aExp + bExp + 2;
  }

  // Product significand:
  ui24 aMant = a.slc<23>(0);
  aMant[23] = a.slc<8>(23) != 0;
  ui24 bMant = b.slc<23>(0);
  bMant[23] = b.slc<8>(23) != 0;
  ui48 pMant = aMant * bMant;

  return tuple<bool, ui9, ui48> (pSign, pExp, pMant);
 }

// Count leading zeroes of a nonzero 77-bit vector.
// After k iterations of the loop, where 0 <= k <= 7, the value of n
// is 2^(6-k) and the low n entries of z and c are as follows:
// Consider the partition of x into n bit slices of width 2^k.
// For 0 <= i < n, the i^th slice is x[2^k*(i+1)-1:2^k*i].
// Let L(i) be the number of leading zeroes of this slice.  Then
//   z[i] = 1 <=> L(i) = 2^k;
//   L(i) < 2^k => c[i] = L(i).

ui7 CLZ77(ui77 s) {
  ui128 x = 0;
  x.set_slc(51, s);
  array<bool, 128> z;
  array<ui7, 128> c;
  for (uint i=0; i<128; i++) {
    z[i] = !x[i];
    c[i] = 0;
  }
  uint n = 128;
  for (uint k=0; k<7; k++) {
    n = n/2; // n = 2^(6-k)
    for (uint i=0; i<n; i++) {
      c[i] = z[2*i+1] ? c[2*i] : c[2*i+1];
      c[i][k] = z[2*i+1];
      z[i] = z[2*i+1] && z[2*i];
    }
  }
  return c[0];
}

// Count the leading zeroes of a 24-bit vector:

ui7 CLZ24(ui24 s) {
  ui32 x = 0;
  x.set_slc(8, s);
  array<bool, 32> z;
  array<ui5, 32> c;
  for (uint i=0; i<32; i++) {
    z[i] = !x[i];
    c[i] = 0;
  }
  uint n = 32;
  for (uint k=0; k<5; k++) {
    n = n/2; // n = 2^(4-k)
    for (uint i=0; i<n; i++) {
      c[i] = z[2*i+1] ? c[2*i] : c[2*i+1];
      c[i][k] = z[2*i+1];
      z[i] = z[2*i+1] && z[2*i];
    }
  }
  return c[0];
}

// Predict leading zero count of a sum of 52-bit vectors:

ui7 LZA52(ui52 add1, ui52 add2, ui11 sumExp) {
  ui52 gen = add1 & add2;
  ui52 prop = add1 ^ add2;
  ui52 kill = ~(add1 | add2);
  ui51 patSub = prop.slc<52>(1) ^ gen;
  ui51 patAdd = prop.slc<52>(1) ^ kill;
  ui50 w = ~(patSub.slc<50>(0) & patSub.slc<50>(1) | patAdd.slc<50>(0) & patAdd.slc<50>(1));
  ui77 vec = w;
  if (sumExp <= 971) {
    vec[972 - sumExp] = 1;  // 0 <= 972 - sumExp <= 972 - 896 = 76
  }
  return CLZ77(vec);
}

// Compute addends:

tuple<ui52, ui52, bool>
computeAddends(ui9 cExp, ui9 pExp, ui48 cMant, ui48 pMant, bool noZero, bool sub, bool cLarger) {

  // Compute right-shifted addend:
  ui9 cMpExp = cExp - pExp; // If pExp > cExp, then cMpExp = cExp - pExp + 2^9
  ui9 rShft;
  ui113 preShft = 0;
  if (cLarger) {
    rShft = cMpExp;
    preShft.set_slc(65, pMant);
  }
  else {
    rShft = ~cMpExp;  // 2^9 - cMpExp - 1 = pExp - cExp - 1
    preShft.set_slc(64, cMant);
  }
  ui52 add1 = 0x8000000000000, add2 = 0x8000000000000; //  add1[51] = add2[51] = 1
  bool inx;
  if (rShft >= 64) {
    inx = noZero;
  }
  else {
    ui113 postShft = preShft >> rShft;
    add1.set_slc(0, postShft.slc<50>(63));
    inx = postShft.slc<63>(0) != 0;
  }
  add2.set_slc(2, ui48(cLarger ? cMant : pMant));
  if (sub) {
    add2 = ~add2;
  }

  return tuple<ui52, ui52, bool> (add1, add2, inx);
}

// 64-bit Han-Carlson adder:

tuple<ui64, ui64> HC64(ui64 g0, ui64 p0) {

  // Brent-Kung array of depth 3:
  ui32 g1, p1;
  for (uint i=0; i<32; i++) {
    g1[i] = g0[2*i+1] || g0[2*i] && p0[2*i+1];
    p1[i] = p0[2*i+1] && p0[2*i];
  }
  ui16 g2, p2;
  for (uint i=0; i<16; i++) {
    g2[i] = g1[2*i+1] || g1[2*i] && p1[2*i+1];
    p2[i] = p1[2*i+1] && p1[2*i];
  }
  ui8 g3, p3;
  for (uint i=0;i<8;i++) {
    g3[i] = g2[2*i+1] || g2[2*i] && p2[2*i+1];
    p3[i] = p2[2*i+1] && p2[2*i];
  }

  // Kogge-Stone array of depth 3 with inputs g3, p3:
  ui8 gx0 = g3, npx0 = ~p3;
  ui8 gx1 = gx0 | ~npx0 & (gx0 << 1);
  ui8 npx1 = npx0 | (npx0 << 1);
  ui8 gx2 = gx1 | ~npx1 & (gx1 << 2);
  ui8 npx2 = npx1 | (npx1 << 2);
  ui8 gx3 = gx2 | ~npx2 & (gx2 << 4);
  ui8 npx3 = npx2 | (npx2 << 4);
  ui8 px3 = ~npx3;

  // Final array combines outputs of BK and KS arrays:
  ui9 gz3, pz3;
  gz3[0] = 0;
  pz3[0] = 1;
  gz3.set_slc(1, gx3);
  pz3.set_slc(1, px3);
  ui17 gz2, pz2;
  gz2[0] = 0;
  pz2[0] = 1;
  for (uint i=0; i<8; i++) {
    gz2[2*i+2] = gz3[i+1];
    pz2[2*i+2] = pz3[i+1];
    gz2[2*i+1] = g2[2*i] || p2[2*i] && gz3[i];
    pz2[2*i+1] = pz3[i] && p2[2*i];
  }
  ui33 gz1, pz1;
  gz1[0] = 0;
  pz1[0] = 1;
  for (uint i=0; i<16; i++) {
    gz1[2*i+2] = gz2[i+1];
    pz1[2*i+2] = pz2[i+1];
    gz1[2*i+1] = g1[2*i] || p1[2*i] && gz2[i];
    pz1[2*i+1] = pz2[i] && p1[2*i];
  }
  ui65 gz0, pz0;
  for (uint i=0; i<32; i++) {
    gz0[2*i+2] = gz1[i+1];
    pz0[2*i+2] = pz1[i+1];
    gz0[2*i+1] = g0[2*i] || p0[2*i] && gz1[i];
    pz0[2*i+1] = pz1[i] && p0[2*i];
  }

  return tuple<ui64, ui64>(gz0.slc<64>(1), pz0.slc<64>(1));
}

// 52-bit Han-Carlson adder:

tuple<ui52, ui52> HC52(ui52 gIn, ui52 pIn) {

  // Extend to 64 bits:
  ui64 g0, p0;
  g0.set_slc(12, gIn);
  p0.set_slc(12, pIn);
  g0.set_slc(0, ui12(0));
  p0.set_slc(0, ui12(0xFFF));

  // Run 64-bit Han-Carlson adder:
  ui64 gz0, pz0;
  tie(gz0, pz0) = HC64(g0, p0);

  // Extract 52-bit generate and propagate vectors:
  ui52 gOut = gz0.slc<52>(12), pOut = pz0.slc<52>(12);

  return tuple<ui52, ui52>(gOut, pOut);
}

tuple<ui51, bool, bool> computeSum(ui52 add1, ui52 add2, bool sub, bool signLarger, bool inx) {

  // 52-bit addends:
  ui52 gIn = add1 & add2, pIn = add1 ^ add2;

  ui52 gOut, pOut;
  tie(gOut, pOut) = HC52(gIn, pIn);

  // Toggle sign:
  bool toggleSign = !gOut[51];

  // Severe cancellation:
  bool severe = pOut[51];

  // Compute carryIn vector:
  ui51 gShft, pShft;
  gShft.set_slc(1, gOut.slc<50>(0));
  gShft[0] = 0;
  pShft.set_slc(1, pOut.slc<50>(0));
  pShft[0] = 1;
  bool inc = sub && (gOut[51] || inx);
  ui51 carryIn = inc ? gShft | pShft : gShft;

  // Compute sum:
  ui51 sum = toggleSign ? ui51(~(pIn.slc<51>(0) ^ carryIn)) : pIn.slc<51>(0) ^ carryIn;

  // Result sign:
  bool sign = signLarger ^ (sub && !toggleSign) ^ severe;

  return tuple<ui51, bool, bool>(sum, sign, severe);
}

//  Compoute rounding increment.

bool computeInc(ui3 rMode, bool sign, ui23 mant, bool grd, bool stk) {
  ui4 inc;
  switch (rMode) {
  case 0: // RUP
    inc = !sign && (stk || grd);
    break;
  case 1: // RDN
    inc = sign && (stk || grd);
    break;
  case 2: // RTZ
    inc = 0;
    break;
  case 3: // RNE
    inc = grd && (stk || mant[0]);
    break;
  case 4: // RNA
    inc = grd;
    break;
  case 5: // RTO
    inc = !mant[0] && (grd || stk);
    break;
  default:
    assert(false);
  }
  return inc;
}

// The first addend, c[31:0], is a SP encoding.
// The second addend is given by {pSign, pExp[8:0], pMant[47:0]}, an unnormalized representation of
// the multiplier output with exponent bias 255 and 47 fractional bits, i.e., the value represented is
//    P = (-1)^pSign * 2^(pExp - 255 - 47) * pMant.
// rMode is a 3-bit encoding of the rounding mode.
// scale is a 10-bit signed integer to be added to the result exponent when scaleOp = 1.

ui32 fadd32(ui32 c, bool pSign, ui9 pExp, ui48 pMant, ui3 rMode, bool scaleOp, si10 scale) {

  // Result fields:
  bool resSign;
  ui8 resExp;
  ui23 resMant;

  // Rounding increment:
  bool rndInc = 0;

  // Identify special cases:
  bool cZero = c.slc<31>(0) == 0;
  bool cInf = c.slc<8>(23) == 0xFF && c.slc<23>(0) == 0;
  bool cNaN = c.slc<8>(23) == 0xFF && c.slc<23>(0) != 0;
  bool pZero = pExp == 0;
  bool pInf = pExp == 1;
  bool pNaN = pExp == 0x1FF;

  // Convert c to same format as p:
  bool cSign = c[31];
  ui9 cExp = c.slc<8>(23) + 128;
  ui48 cMant = 0;
  if (c.slc<8>(23) == 0) {
    cMant.set_slc(25, c.slc<23>(0));
  }
  else {
    cMant.set_slc(24, c.slc<23>(0));
    cMant[47] = 1;
  }

  // Subtraction?
  bool sub = (cSign ^ pSign) && !cZero && !pZero;

  // Larger operand?
  bool cLarger = !cZero && cExp >= pExp;

  // Compute addends:
  ui52 add1, add2;
  bool inx; // add1 is inexact
  tie(add1, add2, inx) = computeAddends(cExp, pExp, cMant, pMant, !cZero && !pZero, sub, cLarger);

  // Add:
  ui51 sum;
  bool severe;
  tie(sum, resSign, severe) = computeSum(add1, add2, sub, cLarger ? cSign : pSign, inx);

  // Special cases:
  if (cNaN || pNaN || cInf && pInf && (cSign ^ pSign)) {
    resSign = 0;
    resExp = 0xFF;
    resMant = 0x400000;
  }
  else if (cInf || pInf) {
    resSign = cInf ? cSign : pSign;
    resExp = 0xFF;
    resMant = 0;
  }
  else if (cZero && pZero || severe && !inx) {
    resSign = cSign && pSign || (rMode == 1) && (cSign || pSign);
    resExp = 0;
    resMant = 0;
  }

  else {

    // Rebias max exponent to 11 bits, add 26, add scale factor:
    ui11 sumExp = (cLarger ? cExp : pExp) + 1023 - 255 + 26;
    if (scaleOp) {
      sumExp += scale;
    }

    // Truncated result is now represented as {remSign, sumExp[10:0], sum[50:0]} with exponent bias
    // 1023 + 26 = 1049 and 49 fractional bits, i.e.,
    //   R = (-1)^remSign * 2^(sumExp - 1049 - 49) * sum
    //     = (-1)^remSign * 2^(sumExp - 1098) * sum

    // If sumExp < 896, then
    //  |R| < 2^(896 - 1098) * 2^(51) = 2^(-151) < 2^(-150) = spd(SP)/2:
    if (severe || sumExp < 896) {
      resExp = 0;
      resMant = 0;
      rndInc = (rMode == 5) || (resSign ? rMode == 1 : rMode == 0);
    }

    else { // sumExp >= 896

      // Predict leading zero count and perform left shift:
      ui7 clz = LZA52(add1, add2, sumExp);
      ui78 sumShft = ui78(sum) << clz;

      // Determine whether clz is an overestimate and adjust accordingly:
      bool overShft = sumShft[77];
      ui7 clzPrime = overShft ? ui7(clz - 1) : clz;

       // Overflow case:
      if (sumExp - clzPrime > 1149) {
        resExp = 0xFE;
        resMant = 0x7FFFFF;
        rndInc = !((rMode == 2) || resSign && (rMode == 0) || !resSign && (rMode == 1));
      }

      else {

        // Mantissa, guard, and sticky:
        bool grd, stk;
        if (overShft) {
          resMant = sumShft.slc<23>(54);
          grd = sumShft[53];
	  stk = inx || (sumShft.slc<53>(0) != 0);
        }
        else {
          resMant = sumShft.slc<23>(53);
	  grd = sumShft[52];
	  stk = inx || (sumShft.slc<52>(0) != 0);
        }

        // Exponent:
        resExp = sumExp - clzPrime + 1;
        resExp[7] = !resExp[7];

        // In the denormal case, the computed exponent is 1 and must be replaced with 0.
        if (clz == sumExp - 896 && !overShft && !sumShft[76]) {
	  resExp[0] = 0;
	}

        // Rounding increment:
        rndInc = computeInc(rMode, resSign, resMant, grd, stk);
      }
    }
  }

  // Assemble result:
  ui32 res;
  res[31] = resSign;
  res.set_slc(23, resExp);
  res.set_slc(0, resMant);
  ui32 resRnd = res + rndInc;
  return resRnd;
}

// Under certain conditions, the scale is decreased by 128 and the product and addend
// are adjusted accordingly:

tuple<ui32, ui9, si10> scale128(ui32 a, ui32 b, ui32 c, ui32 d, ui9 pExp) {
  si32 scale = d;
  bool aZeroInfNaN = a.slc<31>(0) == 0 || a.slc<8>(23) == 0xFF;
  bool bZeroInfNaN = b.slc<31>(0) == 0 || b.slc<8>(23) == 0xFF;
  bool cDenorm = c.slc<8>(23) == 0 && c.slc<23>(0) != 0;
  ui9 abExp = a.slc<8>(23) + b.slc<8>(23);
  if (!aZeroInfNaN && !bZeroInfNaN && cDenorm && abExp >= 64 && abExp < 256 && scale >= 16) {
    ui5 clz = CLZ24(c.slc<23>(0));
    c.set_slc(23, ui8(0x81 - clz));
    c.set_slc(0, ui23(c.slc<23>(0) << clz));
    pExp = pExp + 128;
    scale = scale >= 512 ? 511 : int(scale) - 128;
    }
  else {
    scale = scale >= 512 ? 511 : scale < -512 ? -512 : int(scale);
  }
  return tuple<ui32, ui9, si10>(c, pExp, scale);
  }

ui32 fma32(ui32 a, ui32 b, ui32 c, ui32 d, ui3 rMode, bool scaleOp) {

  bool pSign;
  ui9 pExp;
  ui48 pMant;
  tie(pSign, pExp, pMant) = fmul32(a, b);

  si10 scale = 0;
  if (scaleOp) {
    tie(c, pExp, scale) = scale128(a, b, c, d, pExp);
  }

  // ac::probe_map("c", c);
  // ac::probe_map("pSign", pSign);
  // ac::probe_map("pExp", pExp);
  // ac::probe_map("pMant", pMant);
  // ac::probe_map("scaleOp", scaleOp);
  // ac::probe_map("scale", scale);

  return fadd32(c, pSign, pExp, pMant, rMode, scaleOp, scale);
}

// RAC end

#ifdef SLEC

SC_MODULE(fma32_wrapper) {

  sc_in_clk    clk;
  sc_in<bool>  reset;
  sc_in<bool>  ftz;
  sc_in<bool>  scaleOp;
  sc_in<ui2>   rMode;
  sc_in<ui32>  src0;
  sc_in<ui32>  src1;
  sc_in<ui32>  src2;
  sc_in<ui32>  src3;

  sc_out<ui32> res;

  void doit() {

    if (reset.read()) {
      return;
    }

    ftz.read();
    scaleOp.read();
    rMode.read();
    src0.read();
    src1.read();
    src2.read();
    src3.read();

    ui2 rMode2 = rMode;
    if (scaleOp) {
      rMode2 = rMode2[0] ? 2 : 3;
    }
    else {
      rMode2 = rMode2 + 3;
    }

    ui32 data = fma32(src0, src1, src2, src3, rMode2, scaleOp);
    res.write(data);

  }

  SC_CTOR(fma32_wrapper) {
    SC_METHOD(doit);
    sensitive_pos << clk;
  }

};

#else

int main() {
/*
ui64 x = 0x800000, y;
for (uint i=0; i<0x800000; i++) {
  x = x + 1;
  y = 0x800000;
  for (uint j=0; j<0x800000; j++) {
    y = y + 1;
    ui64 z = x * y;
    if ((z.slc<27>(10) == 0) && !z[47]) {
printf("x = %s\n", x.to_string(AC_HEX, false).c_str());
printf("y = %s\n", y.to_string(AC_HEX, false).c_str());
      break;
    }
  }
}
*/
ui32 a = 0xa1eaa0f1;
ui32 b = 0x007d33ad;
ui32 c = 0x43000000;
ui32 d = 0x00000070;
ui2 rMode = 2;
bool scaleOp = 1;

printf("a = %s\n", a.to_string(AC_HEX, false).c_str());
printf("b = %s\n", b.to_string(AC_HEX, false).c_str());
printf("c = %s\n", c.to_string(AC_HEX, false).c_str());
printf("d = %s\n", d.to_string(AC_HEX, false).c_str());
//printf("rMode = %s\n", rMode.to_string(AC_HEX, false).c_str());
//cout << "scaleOp = " << scaleOp << endl;

ui32 res = fma32(a, b, c, d, rMode, scaleOp);

printf("res = %s\n", res.to_string(AC_HEX, false).c_str());

return 0;
}

#endif
