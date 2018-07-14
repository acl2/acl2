#define SLEC

#include <stdio.h>
#include <math.h>
#include <rac.h>
#include <string>
#include <vector>

#include "ac_fixed.h"
#include "ac_int.h"
#include "ac_probe.h"

using namespace std;

#include "shared.cpp"

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
typedef ac_int<23, false> ui23;
typedef ac_int<29, false> ui29;
typedef ac_int<32, false> ui32;
typedef ac_int<42, false> ui42;
typedef ac_int<52, false> ui52;
typedef ac_int<53, false> ui53;
typedef ac_int<54, false> ui54;
typedef ac_int<56, false> ui56;
typedef ac_int<57, false> ui57;
typedef ac_int<59, false> ui59;
typedef ac_int<60, false> ui60;
typedef ac_int<64, false> ui64;
typedef ac_int<7, true> si7;
typedef ac_int<8, true> si8;
typedef ac_int<13, true> si13;

// Formats:

enum Format {HP, SP, DP};

// Data classes:

enum Class {ZERO, INF, SNAN, QNAN, NORM, DENORM};

// Rounding modes:

const ui2 rmodeNear = 0;
const ui2 rmodeUP = 1;
const ui2 rmodeDN = 2;
const ui2 rmodeZero = 3;

// Flags:

const uint IDC = 7; // denormal exxception
const uint IXC = 4; // inexact exception
const uint UFC = 3; // underflow
const uint OFC = 2; // overflow
const uint DZC = 1; // divide-by-zero exception
const uint IOC = 0; // invalid operand exception

// Extract operand components, apply FZ, identify data class, and record denormal:

tuple<bool, ui11, ui52, Class, ui8> analyze(ui64 op, ui2 fmt, bool fz, ui8 flags) {

  // Extract fields:

  bool sign;
  si13 exp;
  ui52 man, manMSB;
  bool expIsMax;
  switch (fmt) {
  case DP:
    sign = op[63];
    exp = op.slc<11>(52);
    expIsMax = exp == 0x7FF;
    man = op.slc<52>(0);
    manMSB = 0x8000000000000;
    break;
  case SP:
    sign = op[31];
    exp = op.slc<8>(23);
    expIsMax = exp == 0xFF;
    man = op.slc<23>(0);
    manMSB = 0x400000;
    break;
  case HP:
    sign = op[15];
    exp = op.slc<5>(10);
    expIsMax = exp == 0x1F;
    man = op.slc<10>(0);
    manMSB = 0x200;
  }

  // Classify:

  Class c;
  if (expIsMax) { // NaN or infinity
    if (man == 0) {
      c = INF;
    }
    else if (man & manMSB) {
      c = QNAN;
    }
    else {
      c = SNAN;
    }
  }
  else if (exp == 0) { // zero or denormal
    if (man == 0) {
     c = ZERO;
    }
    else if (fz) {
     c = ZERO;
     if (fmt != HP) {
       flags[IDC] = 1; // denormal exception
     }
    }
    else {
      c = DENORM;
    }
  }
  else { // normal
    c = NORM;
  }

  return tuple<bool, ui11, ui52, Class, ui8>(sign, exp, man, c, flags);
}

// Count leading zeroes of a nonzero 53-bit vector.
// After k iterations of the loop, where 0 <= k <= 6, the value of n 
// is 2^(6-k) and the low n entries of z and c are as follows:
// Consider the partition of x into n bit slices of width 2^k.
// For 0 <= i < n, the i^th slice is x[2^k*(i+1)-1:2^k*i].
// Let L(i) be the number of leading zeroes of this slice.  Then
//   z[i] = 1 <=> L(i) = 2^k;
//   L(i) < 2^k => c[i] = L(i).

ui7 CLZ53(ui53 s) {
  ui64 x = 0;
  x.set_slc(11, s);
  array<bool, 64> z;
  array<ui6, 64> c;
  for (uint i=0; i<64; i++) {
    z[i] = !x[i];
    c[i] = 0;
  }
  uint n = 64;
  for (uint k=0; k<6; k++) {
    n = n/2; // n = 2^(5-k)
    for (uint i=0; i<n; i++) {
      c[i] = z[2*i+1] ? c[2*i] : c[2*i+1];
      c[i][k] = z[2*i+1];
      z[i] = z[2*i+1] && z[2*i];
    }
  }
  return c[0];
}

// Compute Q, incremented Q, and sticky bit: 

tuple<ui53, ui53, bool> computeQ(ui54 QP, ui54 QN, ui59 RP, ui59 RN, ui2 fmt, bool isSqrt) {

  // Sign of remainder:

  ui59 rem = RP + ~RN + 1;
  bool remSign = rem[58];
  bool remZero = (RP ^ RN) == 0;

  // If the remainder is negative, then the quotient must be decremented.  This is
  // achieved by eliminating the carry-in bit:

  bool cin = !remSign;

  // If the sum is to be rounded up, then a rounding increment is added.  Note that
  // the position of the increment is the lsb of the result.  For fdiv, this is bit 1 
  // for SP and bit 2 for DP and HP; for fsqrt, it is the opposite:

  bool lsbIs2 = isSqrt == (fmt == SP);

  ui3 inc = lsbIs2 ? 4 : 2;

  // RTL computes 4 sums in parallel with the rounding increment:
  //   Q0     cin = 0, inc = 0
  //   Q0inc  cin = 0, inc > 0
  //   Q1     cin = 1, inc = 0
  //   Q1inc  cin = 1, inc > 0

  // Two adders are used to compute Q0 and Q1inc; the other sums are derived from these.
  // The simplest sum is Q0:

  ui54 Q0 = QP + ~QN;

  // In order to compute Q1inc, inc is added in via a 3-2 compressor.

  ui54 QN1inc = QP ^ ~QN ^ inc;
  ui54 QP1inc = (QP & ~QN | (QP | ~QN) & inc) << 1;
  ui54 Q1inc = QP1inc + QN1inc + 1;

  // For the other two sums, first we compute the bottom 3 bits:

  ui3 Q1Low = QP.slc<3>(0) + ~QN.slc<3>(0) + 1;
  ui3 Q0incLow = QP1inc.slc<3>(0) + QN1inc.slc<3>(0);
  ui54 Q1 = Q1Low;
  ui54 Q0inc = Q0incLow;

  // The upper bits are just copied (note the difference between fdiv and fsqrt):

  if (Q1 == 0) {
    Q1.set_slc(3, Q1inc.slc<51>(3));
  }
  else {
    Q1.set_slc(3, Q0.slc<51>(3));
  }
  if (Q0inc <= 1 || Q0inc <= 3 && lsbIs2) {
    Q0inc.set_slc(3, Q1inc.slc<51>(3));
  }
  else {
    Q0inc.set_slc(3, Q0.slc<51>(3));
  }
  
  // When cin is finally available, the following selections are made: 

  ui54 Q01 = cin ? Q1 : Q0;
  ui54 Q01inc = cin ? Q1inc : Q0inc;

  // Discard the extra bit if present:

  ui53 Qtrunc = lsbIs2 ? Q01 >> 1 : Q01;
  ui53 Qinc = lsbIs2 ? Q01inc >> 1 : Q01inc;
  return tuple<ui53, ui53, bool>(Qtrunc, Qinc, !remZero);
}

// Right-shift a 64-bit vector:

tuple<ui64, bool> rShft64(ui64 x, ui6 s) {
  ui64 xs = x >> s;
  bool stk = x != (xs << s);
  return tuple<ui64, bool>(xs, stk);
}

// Compute rounded result for both normal and denormal cases:

tuple<ui53, bool, ui53, bool> rounder
(ui53 Qtrunc, ui53 Qinc, bool stk, bool sign, si13 expQ, ui2 rmode, ui2 fmt) {

  // Rounding decision for normal case:

  bool lsb = Qtrunc[1], grd = Qtrunc[0];
  ui53 Qrnd;
  if ((rmode == rmodeNear) && grd && (lsb || stk) ||
      (rmode == rmodeUP) && !sign && (grd || stk) ||
      (rmode == rmodeDN) && sign && (grd || stk)) {
    Qrnd = Qinc.slc<53>(1);
  }
  else {
    Qrnd = Qtrunc.slc<53>(1);
  }
  bool inx = grd || stk;

  // Right-shifted quotient and rounding decision for subnormal case:

  ui64 QDen = 0; // Insert integer bit
  switch (fmt) {
  case DP: QDen[53] = 1; QDen.set_slc(0, Qtrunc.slc<53>(0)); break;
  case SP: QDen[24] = 1; QDen.set_slc(0, Qtrunc.slc<24>(0)); break;
  case HP: QDen[11] = 1; QDen.set_slc(0, Qtrunc.slc<11>(0));
  }

  ui12 shft12 = 1 - expQ; // shift is at most 63
  ui6 shft = shft12 >= 64 ? ui6(63) : ui6(shft12);
  bool lsbDen, grdDen, stkDen;
  ui64 Qshft;
  tie(Qshft, stkDen) = rShft64(QDen, shft);
  lsbDen = Qshft[1];
  grdDen = Qshft[0];
  stkDen  = stkDen || stk;
  ui54 QrndDen;
  if ((rmode == rmodeNear) && grdDen && (lsbDen || stkDen) ||
      (rmode == rmodeUP) && !sign && (grdDen || stkDen) ||
      (rmode == rmodeDN) && sign && (grdDen || stkDen)) {
    QrndDen = Qshft.slc<53>(1) + 1;
  }
  else {
    QrndDen = Qshft.slc<53>(1);
  }
  bool inxDen = grdDen || stkDen;
  return tuple<ui53, bool, ui53, bool>(Qrnd, inx, QrndDen, inxDen);
}

// Final result:

tuple<ui64, ui8> final
(ui53 Qrnd, bool inx, ui53 QrndDen, bool inxDen, bool sign, si13 expQ, ui2 rmode, bool fz, ui2 fmt, ui8 flags) {

  // Selection of infinity or max normal for overflow case:

  bool selMaxNorm = rmode == rmodeDN && !sign || rmode == rmodeUP && sign || rmode == rmodeZero;

  ui64 D = 0;  // data result

  switch (fmt) {

  case DP:
    D[63] = sign;
    if (expQ >= 0x7FF) { // overflow
      if (selMaxNorm) {
        D.set_slc(52, ui11(0x7FE));
	D.set_slc(0, ui52(0xFFFFFFFFFFFFF));
      }
      else {
        D.set_slc(52, ui11(0x7FF));
	D.set_slc(0, ui52(0));
      }
      flags[OFC] = 1; // overflow
      flags[IXC] = 1; // inexact    
    }
    else if (expQ <= 0) { // subnormal
      if (fz) {
	flags[UFC] = 1; // underflow but not inexact
      }
      else {
        ui11 exp = QrndDen[52];
        D.set_slc(52, exp);
        D.set_slc(0, QrndDen.slc<52>(0));
        flags[IXC] = flags[IXC] || inxDen;
        flags[UFC] = flags[UFC] || inxDen;
      }
    }
    else { // normal
      D.set_slc(52, ui11(expQ));
      D.set_slc(0, Qrnd.slc<52>(0));
      flags[IXC] = flags[IXC] || inx;
    }
    break;
    
  case SP:
    D[31] = sign;
    if (expQ >= 0xFF) { // overflow
      if (selMaxNorm) {
        D.set_slc(23, ui8(0xFE));
	D.set_slc(0, ui23(0x7FFFFF));
      }
      else {
        D.set_slc(23, ui8(0xFF));
	D.set_slc(0, ui23(0));
      }
      flags[OFC] = 1; // overflow
      flags[IXC] = 1; // inexact    
    }
    else if (expQ <= 0) { // subnormal
      if (fz) {
	flags[UFC] = 1; // underflow but not inexact
      }
      else {
        ui8 exp = QrndDen[23];
        D.set_slc(23, exp);
        D.set_slc(0, QrndDen.slc<23>(0));
        flags[IXC] = flags[IXC] || inxDen;
        flags[UFC] = flags[UFC] || inxDen;
      }
    }
    else { // normal
      D.set_slc(23, ui8(expQ));
      D.set_slc(0, Qrnd.slc<23>(0));
      flags[IXC] = flags[IXC] || inx;
    }
    break;
    
  case HP:
    D[15] = sign;
    if (expQ >= 0x1F) { // overflow
      if (selMaxNorm) {
        D.set_slc(10, ui5(0x1E));
	D.set_slc(0, ui10(0x3FF));
      }
      else {
        D.set_slc(10, ui5(0x1F));
	D.set_slc(0, ui10(0));
      }
      flags[OFC] = 1; // overflow
      flags[IXC] = 1; // inexact    
    }
    else if (expQ <= 0) { // subnormal
      if (fz) {
	flags[UFC] = 1; // underflow but not inexact
      }
      else {
        ui5 exp = QrndDen[10];
        D.set_slc(10, exp);
        D.set_slc(0, QrndDen.slc<10>(0));
        flags[IXC] = flags[IXC] || inxDen;
        flags[UFC] = flags[UFC] || inxDen;
      }
    }
    else { // normal
      D.set_slc(10, ui5(expQ));
      D.set_slc(0, Qrnd.slc<10>(0));
      flags[IXC] = flags[IXC] || inx;
    }
    break;
  }     
 
  return tuple<ui64, ui8>(D, flags);
}

tuple<ui64, ui8> specialCase
  (bool sign, ui64 opa, ui64 opb, Class classa, Class classb, ui2 fmt, bool dn, ui8 flags) {

  bool isSpecial = false;
  ui64 D = 0;

  ui64 aNan, bNan, manMSB, infinity, defNaN, zero = 0;
  switch (fmt) {
  case DP:
    aNan = opa.slc<64>(0);
    bNan = opb.slc<64>(0);
    zero[63] = sign;
    infinity = 0x7FF0000000000000;
    manMSB = 0x8000000000000;
    break;
  case SP:
    aNan = opa.slc<32>(0);
    bNan = opb.slc<32>(0);
    zero[31] = sign;
    infinity = 0x7F800000;
    manMSB = 0x400000;
    break;
  case HP:
    aNan = opa.slc<16>(0);
    bNan = opb.slc<16>(0);
    zero[15] = sign;
    infinity = 0x7C00;
    manMSB = 0x200;
    break;
  }
  defNaN = infinity | manMSB;

  if (classa == SNAN) {
    D = dn ? defNaN : aNan | manMSB;
    flags[IOC] = 1; // invalid operand
  }
  else if (classb == SNAN) {
    D = dn ? defNaN : bNan | manMSB;
    flags[IOC] = 1; // invalid operand
  }
  else if (classa == QNAN) {
    D = dn ? defNaN : aNan;
  }
  else if (classb == QNAN) {
    D = dn ? defNaN : bNan;
  }
  else if (classa == INF) {
    if (classb == INF) {
      D = defNaN;
      flags[IOC] = 1; // invalid operand
    }
    else {
      D = infinity | zero;
    }
  }
  else if (classb == INF) {
    D = zero;
  }
  else if (classa == ZERO) {
    if (classb == ZERO) {
      D = defNaN;
      flags[IOC] = 1; // invalid operand
    }
    else {
      D = zero;
    }
  }
  else if (classb == ZERO) {
    D = infinity | zero;
    flags[DZC] = 1;
  }

  return tuple<ui64, ui8>(D, flags);
}

// Normalize denormal operands and compute exponent difference:

tuple<ui53, ui53, si13> normalize(ui11 expa, ui11 expb, ui52 mana, ui52 manb, ui2 fmt) {

  ui53 siga = 0, sigb = 0;
  uint bias;
  switch (fmt) {
  case DP:
    siga = mana;
    sigb = manb;
    bias = 0x3FF;
    break;
  case SP:
    siga.set_slc(29, ui23(mana));
    sigb.set_slc(29, ui23(manb));
    bias = 0x7F;
    break;
  case HP:
    siga.set_slc(42, ui10(mana));
    sigb.set_slc(42, ui10(manb));
    bias = 0xF;
  }
  si13 expaShft, expbShft;
  if (expa == 0) {
    ui6 clz = CLZ53(siga);
    siga <<= clz;
    expaShft = 1 - clz;
  }
  else {
    siga[52] = 1;
    expaShft = expa;
  }
  if (expb == 0) {
    ui6 clz = CLZ53(sigb);
    sigb <<= clz;
    expbShft = 1 - clz;
  }
  else {
    sigb[52] = 1;
    expbShft = expb;
  }
  si13 expDiff = expaShft - expbShft + bias;

return tuple<ui53, ui53, si13>(siga, sigb, expDiff);

}

// Prescale the divisor d and the dividend x = 4R0.
// Use the redundant form of x to compute q1.
// Convert d and x to non-redundant form.
// Shift x 1 bit if necessary to ensure that the quotient is in [1, 2) and
// decrement the quotient exponent accordingly.
// Return d along with q1*d and x, which are the sum and carry vectors of R1,
// and the quotient exponent.

tuple<ui57, ui59, ui59, si13, int> prescale(ui56 siga, ui56 sigb, si13 expDiff) {

  // Prescale the divisor, deriving the scaling factor from sigb[51:49]:

  ui56 div1, div2, div3, divSum, divCar;

  if (!sigb[51] && (sigb[50] || !sigb[49])) {
    div1 = sigb << 2;
  }
  else if (!sigb[50] && (sigb[51] || sigb[49])) {
    div1 = sigb << 1;
  }
  else {
    div1 = 0;
  }
  if (!sigb[51] && !sigb[50]) {
    div2 = sigb << 2;
  }
  else if ((sigb[51] || sigb[50]) && !sigb[49] || sigb[51] && sigb[50]) {
    div2 = sigb;
  }
  else {
    div2 = 0;
  }
  div3 = sigb << 3;

  divSum = div1 ^ div2 ^ div3;
  divCar = (div1 & div2 | div1 & div3 | div2 & div3) << 1;
  ui57 div = divSum + divCar;

  // Prescale the dividend using the same scaling factor:
  
  ui56 rem1, rem2, rem3, remSum, remCar;
  if (!sigb[51] && (sigb[50] || !sigb[49])) {
    rem1 = siga << 2;
  }
  else if (!sigb[50] && (sigb[51] || sigb[49])) {
    rem1 = siga << 1;
  }
  else {
    rem1 = 0;
  }
  if (!sigb[51] && !sigb[50]) {
    rem2 = siga << 2;
  }
  else if ((sigb[51] || sigb[50]) && !sigb[49] || sigb[51] && sigb[50]) {
    rem2 = siga;
  }
  else {
    rem2 = 0;
  }
  rem3 = siga << 3;

  remSum = rem1 ^ rem2 ^ rem3;
  remCar = (rem1 & rem2 | rem1 & rem3 | rem2 & rem3) << 1;

  // Compare siga and sigb:

  ui53 sigaBar = ~siga;
  ui54 sigCmp = sigb + sigaBar;
  bool sigaLTsigb = sigCmp[53];

  // Compute 5-bit approximation of scaled dividend:

  ui5 remCarBits, remSumBits;
  bool remCin;
  if (sigaLTsigb) {
    remCarBits = remCar.slc<4>(52);
    remSumBits = remSum.slc<4>(52);
    remCin = remCar[51] || remSum[51];
  }
  else {
    remCarBits = remCar.slc<3>(53);
    remSumBits = remSum.slc<3>(53);
    remCin = remCar[52] || remSum[52];
  }
  ui5 remBits = remCarBits + remSumBits + remCin;

  // q1 = 2 if remBits[4:0] >= 13, otherwise q1 = 1:
  
  int q1 = remBits[4] || remBits[3] && remBits[2] & (remBits[1] || remBits[0]) ? 2 : 1;
  
  // Carry vector of R1 and exponent of the quotient:

  ui59 RP = remSum + remCar;
  if (sigaLTsigb) {
    RP <<= 1;
    expDiff--;
  }

  // sum vector of R1:

  ui59 RN = 0;
  if (q1 == 2) {
    RN.set_slc(1, div);
  }
  else {
    RN.set_slc(0, div);
  }

  return tuple<ui57, ui59, ui59, si13, int>(div, RP, RN, expDiff, q1);
}

// Derive the next quotient digit qi+1 from a 6-bit approximation of the remainder Ri:

int nextDigit(ui6 remS6) {

  // remS6 >= 13:
  if (!remS6[5] && (remS6[4] || (remS6[3] && remS6[2] && (remS6[1] || remS6[0])))) {
    return 2;
  }

  // remS6 >= 4
  else if (!remS6[5] && (remS6[3] || remS6[2])) {
    return 1;
  }

  // remS6 >= -3
  else if (!remS6[5] || remS6[5] && remS6[4] && remS6[3] &&
           remS6[2] && (remS6[1] || remS6[0])) {
    return 0;
  }

  // remS6 >= -12
  else if (remS6[4] && (remS6[3] || remS6[2])) {
    return -1;
  }
  
  else {
    return -2;
  }
}

// Derive the next remainder Ri+1 from the remainder Ri, quotient digit qi+1,
// and divisor:

tuple<ui59, ui59> nextRem(ui59 RP, ui59 RN, ui59 div, int q, ui2 fmt) {

  ui59 divMult = div;
  switch (q) {
  case 2:
    divMult <<= 1;
    divMult = ~divMult;
    break;
  case 1:
    divMult = ~divMult;
    break;
  case 0:
    divMult = 0;
    break;
  case -1:
    break;
  case -2:
    divMult <<= 1;
  }

  ui59 RP4 = RP << 2;
  ui59 RN4 = RN << 2;
  ui59 sum = RN4 ^ RP4 ^ divMult;
  ui59 car = ~RN4 & RP4 | (~RN4 | RP4) & divMult;
  ui59 car2 = car << 1;
  switch (fmt) {
  case DP:
    RP = car2;
    RP[0] = q > 0;
    RN = sum;
    break;
  case SP:
    RP.set_slc(29, car2.slc<30>(29));
    RP[29] = q > 0;
    RN.set_slc(29, sum.slc<30>(29));
    break;
  case HP:
    RP.set_slc(42, car2.slc<17>(42));
    RP[42] = q > 0;
    RN.set_slc(42, sum.slc<17>(42));
  }
  return tuple<ui59, ui59>(RP, RN);
}

// Update signed-digit quotient with next digit:

tuple<ui54, ui54> nextQuot(ui54 QP, ui54 QN, int q) {
  QP <<= 2;
  QN <<= 2;
  if (q >= 0) {
    QP.set_slc(0, ui2(q));
  }
  else {
    QN.set_slc(0, ui2(-q));
  }
  return tuple<ui54, ui54>(QP, QN);
}

// In each of the three iterations of a cycle, the next quotient digit and remainder
// (in redundant form) are computed.  The remainder upon entering the cycle is Ri.
// The quotient digits and remainders computed in the cycle are qi1, qi2, qi3, and Ri1, Ri2, Ri3.
// The remainders are redundantly represented by RPi* and RNi*.

// In the first iteration, two non-redundant approximations of Ri1 are returned along with qi1, RPi1, and RNi1:
// (1) a 6-bit sum Ri1S6, which is used in the second iteration to compute qi2;
// (2) a 9-bit sum Ri1S9, which is used in the second iteration in combination with the divisor
//     to compute a 7-bit approximation of Ri2, which is used in the third iteration to compute qi3.

tuple<int, ui59, ui59, ui6, ui9> iter1(ui59 RPi, ui59 RNi, ui57 div, ui2 fmt) {

  ui6 RiS6 = RPi.slc<6>(51) + ~RNi.slc<6>(51) + 1;
  int qi1 = nextDigit(RiS6);

  ui59 RPi1, RNi1;
  tie(RPi1, RNi1)  = nextRem(RPi, RNi, div, qi1, fmt);

  ui6 Ri1S6 = RPi1.slc<6>(51) + ~RNi1.slc<6>(51) + 1;
  ui9 Ri1S9 = RPi1.slc<9>(48) + ~RNi1.slc<9>(48) + 1;

  return tuple<int, ui59, ui59, ui6, ui9>(qi1, RPi1, RNi1, Ri1S6, Ri1S9);

}

// In the second iteration, a 7-bit non-redundant approximation of Ri2 is returned along with
// qi2, RPi2, and RNi2:

tuple<int, ui59, ui59, ui7> iter2(ui59 RPi1, ui59 RNi1, ui6 Ri1S6, ui9 Ri1S9, ui57 div, ui2 fmt) {

  int qi2 = nextDigit(Ri1S6);

  ui59 RPi2, RNi2;
  tie(RPi2, RNi2)  = nextRem(RPi1, RNi1, div, qi2, fmt);

  ui7 divShft7;
  switch (qi2) {
  case 2: divShft7 = ~div.slc<7>(49); break;
  case 1: divShft7 = ~div.slc<7>(50); break;
  case 0: divShft7 = 0; break;
  case -1: divShft7 = div.slc<7>(50); break;
  case -2: divShft7 = div.slc<7>(49);
  }

  ui7 Ri2S7 = Ri1S9.slc<7>(0) + divShft7 + 1;

  return tuple<int, ui59, ui59, ui7>(qi2, RPi2, RNi2, Ri2S7);

}

// The third iteration returns qi3, RPi3, and RNi3:

tuple<int, ui59, ui59> iter3(ui59 RPi2, ui59 RNi2, ui7 Ri2S7, ui57 div, ui2 fmt) {

  int qi3 = nextDigit(Ri2S7.slc<6>(1));

  ui59 RPi3, RNi3;
  tie(RPi3, RNi3)  = nextRem(RPi2, RNi2, div, qi3, fmt);

  return tuple<int, ui59, ui59>(qi3, RPi3, RNi3);
}

// Inputs of fdiv64:
//   opa[63:0], opb[63:0]: Encodings of dividend and divisor (for SP and HP, operands are low bits)
//   fmt: 2-bit encoding of FP format (DP = 2, SP = 1, HP = 0)
//   fz: force denormals to 0
//   dn: replace NaN operand with default
//   mode[1:0]: encoding of rounding mode

// Outputs of fdiv64:
//   D[63:0]: Data result (in low bits)
//   flags[7:0]: exception flags

tuple<ui64, ui8> fdiv64(ui64 opa, ui64 opb, ui2 fmt, bool fz, bool dn, ui2 rmode) {

  // Analyze operands and process special cases:

  bool signa, signb;    // operand signs
  ui11 expa, expb;      // operand exponents
  ui52 mana, manb;      // operand mantissas
  Class classa, classb; // operand classes
  ui8 flags = 0;        // exception flags
  tie(signa, expa, mana, classa, flags) = analyze(opa, fmt, fz, flags);
  tie(signb, expb, manb, classb, flags) = analyze(opb, fmt, fz, flags);
  bool sign = signa ^ signb; // sign of quotient

  // Detect early exit:

  if (classa == ZERO || classa == INF || classa == SNAN || classa == QNAN ||
      classb == ZERO || classb == INF || classb == SNAN || classb == QNAN) {
    return specialCase(sign, opa, opb, classa, classb, fmt, dn, flags);
  }
  
  else {

    // Detect division by a power of 2:
    
    bool divPow2 = classa == NORM && classb == NORM && manb == 0;

    // Normalize denormals and compute exponent difference:

    ui53 siga, sigb; // significands
    si13 expDiff;    // exponent difference
    tie(siga, sigb, expDiff) = normalize(expa, expb, mana, manb, fmt);

    ui57 div;    // non-redundant prescaled divisor
    ui59 RP, RN; // redundant prescaled remainder
    ui54  QP = 0, QN = 0; // redundant quotient
    si13 expQ; // quotient exponent
    int q; // quotient digit

    // Prescale divisor and remainder

    tie(div, RP, RN, expQ, q) = prescale(siga, sigb, expDiff);
    //    ac::probe_map("div", div);
    //    ac::probe_map("RP", RP);
    //    ac::probe_map("RN", RN); 
    //    ac::probe_map("QP", QP);
    //    ac::probe_map("QN", QN); 
   
    ui5 N; // number of cycles in the iterative phase
    if (divPow2) {
      N = 0;
    }
    else {
      switch (fmt) {
      case DP: N = 9; break;
      case SP: N = 4; break;
      case HP: N = 2;
      }
    }

    for (uint i=0; i<N; i++) { // ith cycle, consisting of 3 iterations
    
      // 1st iteration:
      
      ui6 RS6; // 6-bit approximation of remainder
      ui9 RS9; // 9-bit approximation of remainder
      tie (q, RP, RN, RS6, RS9) = iter1(RP, RN, div, fmt);
      tie (QP, QN) = nextQuot(QP, QN, q);

      // 2nd iteration:
      
      ui7 RS7; // 7-bit approximation of remainder
      tie (q, RP, RN, RS7) = iter2(RP, RN, RS6, RS9, div, fmt);
      tie (QP, QN) = nextQuot(QP, QN, q);
      
      // 3rd iteration:
      
      tie (q, RP, RN) = iter3(RP, RN, RS7, div, fmt);
      tie (QP, QN) = nextQuot(QP, QN, q);
      
      //      ac::probe_map("RP", RP);
      //      ac::probe_map("RN", RN);
      //      ac::probe_map("QP", QP);
      //      ac::probe_map("QN", QN);

    }

    // Assimilate quotient:

    ui53 Qtrunc, Qinc; // Non-redundant quotient and incrementded quotient
    bool stk;     // sticky bit
    if (divPow2) {
      Qtrunc = ui53(mana) << 1;
      stk = 0;
    }
    else {
      tie(Qtrunc, Qinc, stk) = computeQ(QP, QN, RP, RN, fmt, false);
    }

    // Round:

    ui53 Qrnd, QrndDen; // rounded quotient for normal and denormal cases
    bool inx, inxDen;   // inexact indication for normal and denormal cases
    tie(Qrnd, inx, QrndDen, inxDen) = rounder(Qtrunc, Qinc, stk, sign, expQ, rmode, fmt);

    // Compute exceptions and assemble final result:

    return final(Qrnd, inx, QrndDen, inxDen, sign, expQ, rmode, fz, fmt, flags);
  }
}

// RAC end

#ifdef SLEC

SC_MODULE(fdiv64) {

  sc_in_clk    clk;
  sc_in<bool>  reset;
  sc_in<bool>  fz;
  sc_in<bool>  dn;
  sc_in<ui2>   rmode;
  sc_in<ui2>   fmt;
  sc_in<ui64>  opa;
  sc_in<ui64>  opb;

  sc_out<ui64> D;
  sc_out<ui6>  flags;

  void doit() {

    if (reset.read()) {
      return;
    }
  
    fz.read();
    dn.read();
    rmode.read();
    fmt.read();
    opa.read();
    opb.read();

    ui64 data;
    ui8 excps;
    tie(data, excps) = fdiv64(opa, opb, fmt, fz, dn, rmode);

    // Contract excps to 6 bits to match RTL:
    ui6 excps6 = excps;
    excps6[5] = excps[7];

    D.write(data);
    flags.write(excps6);

  }

  SC_CTOR(fdiv64) {
    SC_METHOD(doit);  
    sensitive_pos << clk;
  }

};

#else

int main() {

ui64 opa = 0x119c;
ui64 opb = 0x0501;
ui2 rmode = 0;
bool dn = 0, fz = 0;
ui2 fmt = HP;

ui64 D;
ui6 flags;
tie(D, flags) = fdiv64(opa, opb, fmt, fz, dn, rmode);

printf("opa = %s\n", opa.to_string(AC_HEX, false).c_str());
printf("opb = %s\n", opb.to_string(AC_HEX, false).c_str());
printf("D = %s\n", D.to_string(AC_HEX, false).c_str());
printf("flags = %s\n", flags.to_string(AC_HEX, false).c_str());

 return 0;
}	 

#endif

