//#define SLEC

#include <stdio.h>
#include <math.h>
#include <rac.h>
#include <string>
#include <vector>

#include "ac_fixed.h"
#include "ac_int.h"

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
typedef ac_int<23, false> ui23;
typedef ac_int<29, false> ui29;
typedef ac_int<32, false> ui32;
typedef ac_int<42, false> ui42;
typedef ac_int<52, false> ui52;
typedef ac_int<53, false> ui53;
typedef ac_int<54, false> ui54;
typedef ac_int<55, false> ui55;
typedef ac_int<56, false> ui56;
typedef ac_int<57, false> ui57;
typedef ac_int<59, false> ui59;
typedef ac_int<60, false> ui60;
typedef ac_int<64, false> ui64;
typedef ac_int<65, false> ui65;
typedef ac_int<7, true> si7;
typedef ac_int<8, true> si8;
typedef ac_int<13, true> si13;

// Formats:

enum Format {HP, SP, DP};

// Data classes:

enum Class {ZERO, INF, SNAN, QNAN, NORM, DENORM};

// Rounding modes:

enum Rmode {RNE, RUP, RDN, RTZ};

// Flags:

enum Flags {IOC, DZC, OFC, UFC, IXC, IDC=7};

// Extract operand components, apply FZ, identify data class, and record denormal:

tuple<bool, ui11, ui52, Class, ui8> analyze(ui64 op, Format fmt, bool fz, ui8 flags) {

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

tuple<ui53, ui53, bool> computeQ(ui55 root, ui55 rootM1, ui55 rootP, ui55 rootM1P, ui59 RP, ui59 RN, bool lsbIs2) {

  ui53 Qtrunc, Qinc;
  bool stk;

  // Sign of remainder:
  ui59 rem = RP + ~RN + 1;
  bool remSign = rem[58];
  bool remZero = (RP ^ RN) == 0;

  ui55 rootLo = remSign ? rootM1 : root;
  ui55 rootLoP = remSign ? rootM1P : rootP;

  if (lsbIs2) {
    stk = rootLo[0] || !remZero;
    Qtrunc = rootLo.slc<53>(1);
    Qinc = rootLoP.slc<53>(1);
  }
  else {
    stk = !remZero;
    Qtrunc = rootLo;
    Qinc = rootLoP;
  }

  return tuple<ui53, ui53, bool>(Qtrunc, Qinc, stk);
}

// Right-shift a 64-bit vector.  (This may have to be redefined to match RTL.)

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
  if ((rmode == RNE) && grd && (lsb || stk) ||
      (rmode == RUP) && !sign && (grd || stk) ||
      (rmode == RDN) && sign && (grd || stk)) {
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
  if ((rmode == RNE) && grdDen && (lsbDen || stkDen) ||
      (rmode == RUP) && !sign && (grdDen || stkDen) ||
      (rmode == RDN) && sign && (grdDen || stkDen)) {
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
  bool selMaxNorm = rmode == RDN && !sign || rmode == RUP && sign || rmode == RTZ;

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

tuple<ui64, ui8> specialCase(bool signa, ui64 opa, Class classa, ui2 fmt, bool dn, ui8 flags) {

  ui64 D = 0;

  ui64 aTrunc, manMSB, defNaN, zero = 0;
  switch (fmt) {
  case DP:
    aTrunc = opa.slc<64>(0);
    zero[63] = signa;
    defNaN = 0x7FF8000000000000;
    manMSB = 0x8000000000000;
    break;
  case SP:
    aTrunc = opa.slc<32>(0);
    zero[31] = signa;
    defNaN = 0x7FC00000;
    manMSB = 0x400000;
    break;
  case HP:
    aTrunc = opa.slc<16>(0);
    zero[15] = signa;
    defNaN = 0x7E00;
    manMSB = 0x200;
    break;
  }

  if (classa == SNAN) {
    D = dn ? defNaN : aTrunc | manMSB;
    flags[IOC] = 1; // invalid operand
  }
  else if (classa == QNAN) {
    D = dn ? defNaN : aTrunc;
  }
  else if (classa == ZERO) {
    D = zero;
  }
  else if (signa) {
    D = defNaN;
    flags[IOC] = 1; // invalid operand
  }    
  else {
    D = aTrunc;
  }

  return tuple<ui64, ui8>(D, flags);
}

// Normalize denormal operand and compute predicted result exponent:

tuple<ui53, si13, ui11> normalize(si13 expa, ui52 mana, ui2 fmt) {

  ui53 siga = 0;
  uint bias;
  switch (fmt) {
  case DP:
    siga = mana;
    bias = 0x3FF;
    break;
  case SP:
    siga.set_slc(29, ui23(mana));
    bias = 0x7F;
    break;
  case HP:
    siga.set_slc(42, ui10(mana));
    bias = 0xF;
  }
  if (expa == 0) {
    ui6 clz = CLZ53(siga);
    siga <<= clz;
    expa = 1 - clz;
  }
  else {
    siga[52] = 1;
  }
  ui12 expQ = expa + bias;

  return tuple<ui53, si13, ui11>(siga, expa, expQ.slc<11>(1));

}

// Power of 2:

tuple<ui64, ui8> sqrtPow2(ui11 expQ, bool expOdd, ui2 rmode, ui2 fmt) {

  ui64 D = 0;
  ui8 flags = 0;

  uint manWidth;
  ui52 manSqrt2;
  switch (fmt) {
  case DP:
    manWidth = 52;
    manSqrt2 = rmode == RNE || rmode == RUP ? 0x6A09E667F3BCD : 0x6A09E667F3BCC;
    break;
  case SP:
    manWidth = 23;
    manSqrt2 = rmode == RUP ?  0x3504F4 : 0x3504F3;
    break;
  case HP:
    manWidth = 10;
    manSqrt2 = rmode == RUP ? 0x5A9 : 0x5A8;
    break;
  }

  if (!expOdd) {
    D = manSqrt2;
    flags[IXC] = 1;
  }
  D.set_slc(manWidth, expQ);
  
  return tuple<ui64, ui8>(D, flags);
}

// First iteration:
      
tuple<ui59, ui59, ui55, ui55, int, uint> firstIter(ui53 siga, bool expOdd) {

  ui59 RP = 0, RN = 0;
  ui55 root = 0, rootM1 = 0;
  int q;
  uint i;

  if (expOdd) {
    // x = siga/4 = .01xxx...
    // R0 = x - 1 = 1111.01xxx...
    // RP = 4*R0 = 1101.xxx...
    RP.set_slc(56, ui3(6));
    RP.set_slc(3, siga);
    if (siga[51]) {
      // -5/2 <= 4*R0 < -2
      q = -1;
      root.set_slc(52, ui2(3)); // 0.11000...
      rootM1.set_slc(52, ui2(2)); // 0.10000...
      // R1 = 4*R0 - (-1) * (2*Q0 + (-1)/4) = 4*R0 + 7/4
      // RN = -7/4 = 1110.0100..
      RN.set_slc(53, ui6(0x39)); // 1110.0100...
      i = 4; // Q1 = 0.1100
    }
    else {
      // 4*R0 < -5/2
      q = -2;
      root.set_slc(52, ui2(2)); // 0.10000...
      rootM1.set_slc(52, ui2(1)); // 0.01000...
      // R1 = 4*R0 - (-2) * (2*Q0 + (-2)/4) = 4*R0 + 3
      // RN = -3 = 1101.00...
      RN.set_slc(55, ui4(0xD)); // 1110.0100...
      i = 0; // Q1 = 0.1000
    }
  }

  else { // expa even
    // x = siga/2 = .1xxx...
    // R0 = x - 1 = 1111.1xxx...
    // RP = 4*R0 = 111x.xx...
    RP.set_slc(57, ui2(3));
    RP.set_slc(4, siga);
    if (siga[51]) {
      // -1 <= 4*R0 < 0
      q = 0;
      root[54] = 1; // 1.0000
      rootM1.set_slc(52, ui2(3)); // .11000...
      // R1 = 4*R0 = RP, RN = 0
      i = 8; // Q1 = 1.0000
    }
    else {
      // -2 <= 4*R0 < -1
      q = -1;
      root.set_slc(52, ui2(3)); // 0.11000...
      rootM1.set_slc(52, ui2(2)); // 0.10000...
      // R1 = 4*R0 - (-1) * (2*Q0 + (-1)/4) = 4*R0 + 7/4
      // RN = -7/4 = 1110.0100...
      RN.set_slc(53, ui6(0x39));
      i = 4; // Q1 = 0.1100
    }
  }

  return tuple<ui59, ui59, ui55, ui55, int, uint> (RP, RN, root, rootM1, q, i);
}
  

//   Derive the next quotient digit q_(j+1) from the root interval i and remainder R_j:

int nextDigit(ui59 RP, ui59 RN, uint i, uint j) {

  ui59 RP4 = RP << 2, RN4 = RN << 2;

  ui8 RS8 = RP4.slc<8>(51) + ~RN4.slc<8>(51) + (RP4[50] || !RN4[50]);
  si7 RS7 = RS8.slc<7>(1);

  si7 mp2, mp1, mz0, mn1;
  switch (i) {
  case 0: mp2 = 12; mp1 = 4; mz0 = -4; mn1 = j == 1 ? -11 : -12; break;
  case 1: mp2 = j == 2 ? 15 : 13; mp1 = 4; mz0 = -4; mn1 = -13; break;
  case 2: mp2 = 15; mp1 = 4; mz0 = -4; mn1 = -15; break;
  case 3: mp2 = 16; mp1 = 6; mz0 = -6; mn1 = -16; break;
  case 4: mp2 = 18; mp1 = 6; mz0 = -6; mn1 = -18; break;
  case 5: mp2 = 20; mp1 = 8; mz0 = -6; mn1 = -20; break;
  case 6: mp2 = 20; mp1 = 8; mz0 = -8; mn1 = -20; break;
  case 7: mp2 = 22; mp1 = 8; mz0 = -8; mn1 = -22; break;
  case 8: mp2 = 24; mp1 = 8; mz0 = -8; mn1 = -24;
  }

  int q;
  if (RS7 >= mp2) {
    q = 2;
  }
  else if (RS7 >= mp1) {
    q = 1;
  }
  else if (RS7 >= mz0) {
    q = 0;
  }
  else if (RS7 >= mn1) {
    q = -1;
  }
  else {
    q = -2;
  }
  return q;
}

// Derive the next remainder R_(j+1) from the remainder R_j and the quotient digit q_(j+1):

tuple<ui59, ui59> nextRem(ui59 RP, ui59 RN, ui55 root, ui55 rootM1, int q, uint j, ui2 fmt) {

  // RP4 - RN4 = 4 * R_j:

  ui59 RP4 = RP << 2, RN4 = RN << 2;

  ui59 D = 0, Dcomp = 0;
  switch (q) {
  case 1:
    Dcomp.set_slc(2, root);
    Dcomp.set_slc(53 - 2 * j, ui3(1));
    D = ~Dcomp;
    break;
  case 2:
    Dcomp.set_slc(3, root);
    Dcomp.set_slc(54 - 2 * j, ui3(2));
    D = ~Dcomp;
    break;
  case -1:
    D.set_slc(2, rootM1);
    D.set_slc(53 - 2 * j, ui3(7));
    break;
  case -2:
    D.set_slc(3, rootM1);
    D.set_slc(54 - 2 * j, ui3(6));
    break;
  default:
    break;
  }
  ui59 sum = RP4 ^ RN4 ^ D;
  ui59 car = RP4 & ~RN4 | (RP4 | ~RN4) & D;

  if (q == 0) {
    return tuple<ui59, ui59>(RP4, RN4);
  }
  else {
    ui59 nextRP = 0, nextRN = 0;
    switch (fmt) {
    case DP: 
      nextRP[0] = q > 0;
      nextRP.set_slc(1, car.slc<58>(0)); 
      nextRN = sum;
      break;
    case SP:
      nextRP[29] = q > 0;
      nextRP.set_slc(30, car.slc<29>(29));
      nextRN.set_slc(29, sum.slc<30>(29));
      break; 
    case HP:
      nextRP[42] = q > 0;
      nextRP.set_slc(43, car.slc<16>(42));
      nextRN.set_slc(42, sum.slc<17>(42));
    }
    return tuple<ui59, ui59>(nextRP, nextRN);
  }
}

// Update root and decremented root with next digit:

tuple<ui55, ui55> nextRoot(ui55 root, ui55 rootM1, int q, uint j) {
  ui55 rootNew, rootM1New;
  rootNew = q >= 0 ? root : rootM1;
  rootNew.set_slc(52 - 2 * j, ui2(q));
  rootM1New = q > 0 ? root : rootM1;
  rootM1New.set_slc(52 - 2 * j, ui2(q - 1));
  return tuple<ui55, ui55>(rootNew, rootM1New);
}

// Add rounding increment to root and decremented root:

tuple<ui55, ui55> incRoot(int q, ui55 root, ui55 rootM1, int qLast, ui55 rootLast, ui55 rootM1Last, bool lsbIs2, ui5 N) {
  ui55 rootP, rootM1P;
  uint base = 54 - 2*N;
  if (lsbIs2) {
    if (q >= 0) {
      rootP = qLast >= -1 ? rootLast : rootM1Last;
      rootP.set_slc(base + 2, ui2(qLast + 1));
    }
    else {
      rootP = root;
    }
    rootP.set_slc(base, ui2(q));
    if (q >= 1) {
      rootM1P = qLast >= -1 ? rootLast : rootM1Last;
      rootM1P.set_slc(base + 2, ui2(qLast + 1));
    }
    else {
      rootM1P = root;
    }
    rootM1P.set_slc(base, ui2(q - 1));
  }
  else {
    if (q == 2) {
      rootP = qLast >= -1 ? rootLast : rootM1Last;
      rootP.set_slc(base + 2, ui2(qLast + 1));
      rootP.set_slc(base, ui2(0));
      rootM1P = root;
      rootM1P.set_slc(base, ui2(3));
    }
    else {
      rootP = root;
      rootP.set_slc(base, ui2(q + 2));
      rootM1P = q >= -1 ? root : rootM1;
      rootM1P.set_slc(base, ui2(q + 1));
    }
  }  
  return tuple<ui55, ui55>(rootP, rootM1P);
}

// Inputs of fsqrt4:
//   opa[63:0]: Encoding of radicand (for SP and HP, operand is low bits)
//   fmt: 2-bit encoding of FP format (DP = 2, SP = 1, HP = 0)
//   fz: force denormals to 0
//   dn: replace NaN operand with default
//   mode[1:0]: encoding of rounding mode

// Outputs of fsqrt4:
//   D[63:0]: Data result (in low bits)
//   flags[7:0]: exception flags

tuple<ui64, ui8> fsqrt4(ui64 opa, ui2 fmt, bool fz, bool dn, ui2 rmode) {

  // Analyze operand:
  bool signa;     // operand signs
  ui11 expa;      // operand exponents
  ui52 mana;      // operand mantissas
  Class classa;   // operand classes
  ui8 flags = 0;  // exception flags
  tie(signa, expa, mana, classa, flags) = analyze(opa, fmt, fz, flags);

  // Detect early exit:
  if (classa == ZERO || classa == INF || classa == SNAN || classa == QNAN || signa) {
    return specialCase(signa, opa, classa, fmt, dn, flags);
  }

  else {

    bool expInc = classa == NORM && rmode == RUP;

    // Normalize denormal and compute predicted result exponent:
    ui53 siga;    // significand
    si13 expShft; // adjusted exponent
    ui11 expQ;    // predicted result exponent
    tie(siga, expShft, expQ) = normalize(expa, mana, fmt);

    bool expOdd = expShft[0]; // parity of adjusted exponent

    if (classa == NORM && mana == 0) { // power of 2
      return sqrtPow2(expQ, expOdd, rmode, fmt);
    }

    else {  

      ui59 RP, RN;               // redundant remainder
      int q;                     // root digit;
      int qLast;                 // root digit before penultimate iteration
      ui55 root, rootM1;         // root and decremented root
      ui55 rootLast, rootM1Last; // root and decremented root upon entering final cycle
      ui55 rootP, rootM1P;       // final root and decremented root plus rounding increment
      uint i;                    // root interval, 0 <= i <= 8

      // First iteration:
      
      tie(RP, RN, root, rootM1, q, i) = firstIter(siga, expOdd);

      expInc &= q == 0;
      /*
      ac::probe_map("RP", RP);
      ac::probe_map("RN", RN);
      ac::probe_map("QP", QP);
      ac::probe_map("QN", QN);
      */
      ui5 N; // number of iterations
      switch (fmt) {
      case DP: N = 27; break;
      case SP: N = 13; break;
      case HP: N = 6;
      }
      bool lsbIs2 = fmt == SP; // lsb of final root is bit 2 rather than bit 1

      for (uint j=1; j<N; j++) {

        q = nextDigit(RP, RN, i, j);

	if (j == N - 2) {
          // Save these values during the first iteration of the final cycle,
          // to be used during the final iteration to compute quotP and quotM1P:
	  qLast = q;
	  rootLast = root;
	  rootM1Last = rootM1;
	}

        if (j == 1) {
          i = i + q;
        }
	
        tie(RP, RN) = nextRem(RP, RN, root, rootM1, q, j, fmt);
	
	if (j == N - 1) {
          // Compute rounded root and decremented root on last iteration:
 	  tie (rootP, rootM1P) = incRoot(q, root, rootM1, qLast, rootLast, rootM1Last, lsbIs2, N);
	}
        tie(root, rootM1) = nextRoot(root, rootM1, q, j);

        expInc &= j < N - 1 ? q == 0 : fmt == SP ? q == -2 : q == -1;
	/*      
        ac::probe_map("RP", RP);
        ac::probe_map("RN", RN);
        ac::probe_map("QP", QP);
        ac::probe_map("QN", QN);
	*/
      }

      ui11 expRnd = expInc ? ui11(expQ + 1): expQ;

      // Shift root to low bits:

      ui55 rootShft, rootM1Shft, rootPShft, rootM1PShft;
      switch (fmt) {
      case HP: 
        rootShft = root.slc<13>(42);
        rootM1Shft = rootM1.slc<13>(42);
        rootPShft = rootP.slc<13>(42);
        rootM1PShft = rootM1P.slc<13>(42);
        break;
      case SP: 
        rootShft = root.slc<27>(28);
        rootM1Shft = rootM1.slc<27>(28);
        rootPShft = rootP.slc<27>(28);
        rootM1PShft = rootM1P.slc<27>(28);
        break;
      case DP:
        rootShft = root;
        rootM1Shft = rootM1;
        rootPShft = rootP;
        rootM1PShft = rootM1P;
        break;
      default:
        break;
      }
      // Select inputs to rounder:
      ui53 Qtrunc, Qinc; // root and incremented root
      bool stk;          // sticky bit
      tie(Qtrunc, Qinc, stk) = computeQ(rootShft, rootM1Shft, rootPShft, rootM1PShft, RP, RN, lsbIs2);

      // Round:
      ui53 Qrnd, QrndDen; // rounded root
      bool inx, inxDen;   // inexact indication
      tie(Qrnd, inx, QrndDen, inxDen) = rounder(Qtrunc, Qinc, stk, 0, expRnd, rmode, fmt);

      // Compute exceptions and assemble final result:
      return final(Qrnd, inx, QrndDen, inxDen, 0, expRnd, rmode, fz, fmt, flags);
    }
  }
}

// RAC end

#ifdef SLEC

SC_MODULE(fsqrt4_wrapper) {

  sc_in_clk    clk;
  sc_in<bool>  reset;
  sc_in<bool>  fz;
  sc_in<bool>  dn;
  sc_in<ui2>   rmode;
  sc_in<ui2>   fmt;
  sc_in<ui64>  opa;

  sc_out<ui64> D;
  sc_out<ui8>  flags;

  void doit() {

    if (reset.read()) {
      return;
    }
  
    fz.read();
    dn.read();
    rmode.read();
    fmt.read();
    opa.read();

    ui64 data;
    ui8 excps;
    tie(data, excps) = fsqrt4(opa, fmt, fz, dn, rmode);

    // Contract excps to 6 bits to match RTL:
    ui6 excps6 = excps;
    excps6[5] = excps[7];

    D.write(data);
    flags.write(excps6);

  }

  SC_CTOR(fsqrt4_wrapper) {
    SC_METHOD(doit);  
    sensitive_pos << clk;
  }

};

#else

int main() {

ui64 opa = 0x33ff;
ui2 rmode = 1;
bool dn = 0, fz = 1;
ui2 fmt = HP;

ui64 D;
ui8 flags;
tie(D, flags) = fsqrt4(opa, fmt, fz, dn, rmode);

printf("opa = %s\n", opa.to_string(AC_HEX, false).c_str());
printf("D = %s\n", D.to_string(AC_HEX, false).c_str());
printf("flags = %s\n", flags.to_string(AC_HEX, false).c_str());

 return 0;
}	 

#endif

