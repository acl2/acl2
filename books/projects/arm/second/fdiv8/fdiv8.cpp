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
typedef ac_int<5, false> ui5;
typedef ac_int<6, false> ui6;
typedef ac_int<7, false> ui7;
typedef ac_int<8, false> ui8;
typedef ac_int<10, false> ui10;
typedef ac_int<11, false> ui11;
typedef ac_int<12, false> ui12;
typedef ac_int<13, false> ui13;
typedef ac_int<23, false> ui23;
typedef ac_int<40, false> ui40;
typedef ac_int<52, false> ui52;
typedef ac_int<53, false> ui53;
typedef ac_int<54, false> ui54;
typedef ac_int<59, false> ui59;
typedef ac_int<64, false> ui64;
typedef ac_int<65, false> ui65;
typedef ac_int<71, false> ui71;
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

tuple<ui53, ui53, bool> computeQ(ui65 quot, ui65 quotM1, ui65 quotP, ui65 quotM1P, ui71 RP, ui71 RN, bool lsbIs2) {

  ui53 Qtrunc, Qinc;
  bool stk;

  // Sign of remainder:
  ui71 rem = RP + ~RN + 1;
  bool remSign = rem[70];
  bool remZero = (RP ^ RN) == 0;

  ui65 quotLo = remSign ? quotM1 : quot;
  ui65 quotLoP = remSign ? quotM1P : quotP;

  if (lsbIs2) {
    stk = quotLo[0] || !remZero;
    Qtrunc = quotLo.slc<53>(1);
    Qinc = quotLoP.slc<53>(1);
  }
  else {
    stk = !remZero;
    Qtrunc = quotLo;
    Qinc = quotLoP;
  }

  return tuple<ui53, ui53, bool>(Qtrunc, Qinc, stk);
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

array<ui10, 8> computeCmpConst(ui6 divTop) {

  array<ui10, 8> a;
  switch (divTop.slc<5>(1)) {
  case 0:
    a[7] = divTop[0] ? 0x38d : 0x38f; a[6] = 0x3ae; a[5] = 0x3ce; a[4] = 0x3f0; a[3] = 0x010; a[2] = 0x030; a[1] = 0x051; a[0] = divTop[0] ? 0x072 : 0x070; break;
  case 1:
    a[7] = divTop[0] ? 0x38a : 0x38b; a[6] = 0x3ac; a[5] = 0x3ce; a[4] = 0x3f0; a[3] = 0x010; a[2] = 0x032; a[1] = 0x053; a[0] = divTop[0] ? 0x075 : 0x074; break;
  case 2:
    a[7] = 0x387; a[6] = 0x3aa; a[5] = 0x3cc; a[4] = 0x3f0; a[3] = 0x010; a[2] = 0x034; a[1] = 0x056; a[0] = 0x078; break;
  case 3:
    a[7] = 0x383; a[6] = 0x3a6; a[5] = 0x3ca; a[4] = 0x3ee; a[3] = 0x012; a[2] = 0x036; a[1] = 0x058; a[0] = 0x07c; break;
  case 4:
    a[7] = 0x380; a[6] = 0x3a4; a[5] = 0x3ca; a[4] = 0x3ee; a[3] = 0x012; a[2] = 0x036; a[1] = 0x05a; a[0] = 0x07f; break;
  case 5:
    a[7] = 0x37c; a[6] = 0x3a2; a[5] = 0x3c8; a[4] = 0x3ee; a[3] = 0x012; a[2] = 0x038; a[1] = 0x05e; a[0] = 0x083; break;
  case 6:
    a[7] = 0x379; a[6] = 0x3a0; a[5] = 0x3c6; a[4] = 0x3ee; a[3] = 0x012; a[2] = 0x03a; a[1] = 0x060; a[0] = 0x086; break;
  case 7:
    a[7] = 0x375; a[6] = 0x39c; a[5] = 0x3c4; a[4] = 0x3ec; a[3] = 0x014; a[2] = 0x03c; a[1] = 0x062; a[0] = 0x08a; break;
  case 8:
    a[7] = 0x372; a[6] = 0x39a; a[5] = 0x3c4; a[4] = 0x3ec; a[3] = 0x014; a[2] = 0x03c; a[1] = 0x064; a[0] = 0x08d; break;
  case 9:
    a[7] = 0x36e; a[6] = 0x398; a[5] = 0x3c2; a[4] = 0x3ec; a[3] = 0x014; a[2] = 0x03e; a[1] = 0x068; a[0] = 0x090; break;
  case 10:
    a[7] = 0x36a; a[6] = 0x396; a[5] = 0x3c0; a[4] = 0x3ec; a[3] = 0x014; a[2] = 0x040; a[1] = 0x06a; a[0] = 0x094; break;
  case 11:
    a[7] = 0x368; a[6] = 0x394; a[5] = 0x3c0; a[4] = 0x3ec; a[3] = 0x014; a[2] = 0x040; a[1] = 0x06c; a[0] = 0x098; break;
  case 12:
    a[7] = 0x364; a[6] = 0x390; a[5] = 0x3be; a[4] = 0x3ea; a[3] = 0x016; a[2] = 0x042; a[1] = 0x070; a[0] = 0x09c; break;
  case 13:
    a[7] = 0x360; a[6] = 0x38e; a[5] = 0x3bc; a[4] = 0x3ea; a[3] = 0x016; a[2] = 0x044; a[1] = 0x072; a[0] = 0x09e; break;
  case 14:
    a[7] = 0x35c; a[6] = 0x38c; a[5] = 0x3ba; a[4] = 0x3e8; a[3] = 0x018; a[2] = 0x046; a[1] = 0x074; a[0] = 0x0a2; break;
  case 15:
    a[7] = 0x35a; a[6] = 0x38a; a[5] = 0x3ba; a[4] = 0x3e8; a[3] = 0x018; a[2] = 0x046; a[1] = 0x076; a[0] = 0x0a6; break;
  case 16:
    a[7] = 0x356; a[6] = 0x388; a[5] = 0x3b8; a[4] = 0x3e8; a[3] = 0x018; a[2] = 0x048; a[1] = 0x078; a[0] = 0x0aa; break;
  case 17:
//  a[7] = 0x354; a[6] = 0x384; a[5] = 0x3b8; a[4] = 0x3e8; a[3] = 0x018; a[2] = 0x048; a[1] = 0x07c; a[0] = 0x0ac; break;
    a[7] = 0x353; a[6] = 0x384; a[5] = 0x3b7; a[4] = 0x3e8; a[3] = 0x018; a[2] = 0x048; a[1] = 0x07c; a[0] = 0x0ac; break;
  case 18:
    a[7] = 0x350; a[6] = 0x382; a[5] = 0x3b4; a[4] = 0x3e8; a[3] = 0x018; a[2] = 0x04c; a[1] = 0x07c; a[0] = 0x0b0; break;
  case 19:
    a[7] = 0x34c; a[6] = 0x380; a[5] = 0x3b4; a[4] = 0x3e8; a[3] = 0x018; a[2] = 0x04c; a[1] = 0x080; a[0] = 0x0b4; break;
  case 20:
    a[7] = 0x348; a[6] = 0x37c; a[5] = 0x3b2; a[4] = 0x3e8; a[3] = 0x018; a[2] = 0x04e; a[1] = 0x084; a[0] = 0x0b8; break;
  case 21:
    a[7] = 0x344; a[6] = 0x37a; a[5] = 0x3b0; a[4] = 0x3e4; a[3] = 0x01c; a[2] = 0x050; a[1] = 0x086; a[0] = 0x0bc; break;
  case 22:
    a[7] = 0x342; a[6] = 0x378; a[5] = 0x3ae; a[4] = 0x3e4; a[3] = 0x01c; a[2] = 0x052; a[1] = 0x088; a[0] = 0x0be; break;
  case 23:
    a[7] = 0x33e; a[6] = 0x376; a[5] = 0x3ae; a[4] = 0x3e4; a[3] = 0x01c; a[2] = 0x052; a[1] = 0x08a; a[0] = 0x0c2; break;
  case 24:
    a[7] = 0x33a; a[6] = 0x374; a[5] = 0x3ac; a[4] = 0x3e4; a[3] = 0x01c; a[2] = 0x054; a[1] = 0x08c; a[0] = 0x0c6; break;
  case 25:
    a[7] = 0x338; a[6] = 0x372; a[5] = 0x3ac; a[4] = 0x3e4; a[3] = 0x01c; a[2] = 0x054; a[1] = 0x08e; a[0] = 0x0c8; break;
  case 26:
    a[7] = 0x334; a[6] = 0x36e; a[5] = 0x3aa; a[4] = 0x3e4; a[3] = 0x01c; a[2] = 0x056; a[1] = 0x092; a[0] = 0x0cc; break;
  case 27:
    a[7] = 0x330; a[6] = 0x36c; a[5] = 0x3a8; a[4] = 0x3e4; a[3] = 0x01c; a[2] = 0x058; a[1] = 0x094; a[0] = 0x0d0; break;
  case 28:
    a[7] = 0x32c; a[6] = 0x368; a[5] = 0x3a6; a[4] = 0x3e4; a[3] = 0x01c; a[2] = 0x05a; a[1] = 0x098; a[0] = 0x0d4; break;
  case 29:
    a[7] = 0x32a; a[6] = 0x368; a[5] = 0x3a6; a[4] = 0x3e4; a[3] = 0x01c; a[2] = 0x05a; a[1] = 0x098; a[0] = 0x0d6; break;
  case 30:
    a[7] = 0x326; a[6] = 0x366; a[5] = 0x3a2; a[4] = 0x3e4; a[3] = 0x01c; a[2] = 0x05e; a[1] = 0x09a; a[0] = 0x0da; break; 
  case 31:
    a[7] = 0x322; a[6] = 0x362; a[5] = 0x3a2; a[4] = 0x3e0; a[3] = 0x020; a[2] = 0x05e; a[1] = 0x09e; a[0] = 0x0de;
  }

  return a;
}

// Derive the next quotient digit from a 10-bit approximation of the remainder:

int nextDigit(ui10 RS10, array<ui10, 8> cmpConst) {

  ui11 geP4 = RS10 + cmpConst[7];
  ui11 geP3 = RS10 + cmpConst[6];
  ui11 geP2 = RS10 + cmpConst[5];
  ui11 geP1 = RS10 + cmpConst[4];
  ui11 geZ0 = RS10 + cmpConst[3];
  ui11 geN1 = RS10 + cmpConst[2];
  ui11 geN2 = RS10 + cmpConst[1];
  ui11 geN3 = RS10 + cmpConst[0];

  int q;
  if (geP4[10] && !RS10[9]) {q = 4;}
  else if (!geP4[10] && geP3[10]) {q = 3;}
  else if (!geP3[10] && geP2[10]) {q = 2;}
  else if (!geP2[10] && geP1[10]) {q = 1;}
  else if (!geP1[10] && !RS10[9] || geZ0[10]) {q = 0;}
  else if (!geZ0[10] && geN1[10]) {q = -1;}
  else if (!geN1[10] && geN2[10]) {q = -2;}
  else if (!geN2[10] && geN3[10]) {q = -3;}
  else if (!geN3[10] && RS10[9]) {q = -4;}

  return q;
}

// Derive the next remainder:

tuple<ui71, ui71> nextRem(ui71 RP, ui71 RN, bool remSign, int q, ui71 divSigned, ui71 div3Signed, ui2 fmt) {

  ui71 divMult;
  switch (q) {
  case 4: case -4:
    divMult = divSigned << 2;
    divMult[0] = !remSign;
    divMult[1] = !remSign;
    break;
  case 3: case -3:
    divMult = div3Signed;
    break;
  case 2: case -2:
    divMult = divSigned << 1;
    divMult[0] = !remSign;
    break;
  case 1: case -1:
    divMult = divSigned;
  }

  ui71 RP8 = RP << 3;
  ui71 RN8 = RN << 3;
  ui71 sum = RN8 ^ RP8 ^ divMult;
  ui71 carry = ~RN8 & RP8 | (~RN8 | RP8) & divMult;
  switch (fmt) {
  case DP:
    RP.set_slc(12, carry.slc<59>(11));
    RP[11] = !remSign;
    RN.set_slc(11, sum.slc<60>(11));
    break;
  case SP:
    RP.set_slc(41, carry.slc<30>(40));
    RP[40] = !remSign;
    RN.set_slc(40, sum.slc<31>(40));
    break;
  case HP:
    RP.set_slc(54, carry.slc<17>(53));
    RP[53] = !remSign;
    RN.set_slc(53, sum.slc<18>(53));
  }

  if (q == 0) {
    return tuple<ui71, ui71>(RP8, RN8);
  }
  else {
    return tuple<ui71, ui71>(RP, RN);
  }
}

// Update quotient and decremented quotient with next digit:

tuple<ui65, ui65> nextQuot(int q, ui65 quot, ui65 quotM1) {
  ui65 quotNew, quotM1New;
  quotNew = q >= 0 ? quot << 3 : quotM1 << 3;
  quotNew.set_slc(0, ui3(q));
  quotM1New = q > 0 ? quot << 3 : quotM1 << 3;
  quotM1New.set_slc(0, ui3(q - 1));
  return tuple<ui65, ui65>(quotNew, quotM1New);
}

// Add rounding increment to quotient and decremented quotient:

tuple<ui65, ui65> incQuot(int q, ui65 quot, ui65 quotM1, int qLast, ui65 quotLast, ui65 quotM1Last, bool lsbIs2) {
  ui65 quotP, quotM1P;
  if (lsbIs2) {
    if (q == 4) {
      // This is the case in which the final q together with the rounding increment produces a carry
      // into the penultimate quotient bit, requiring backtracking.
      quotP = qLast >= -1 ? quotLast << 6 : quotM1Last << 6;
      quotP.set_slc(3, ui3(qLast + 1));
      quotM1P = qLast >= 0 ? quotLast << 6 : quotM1Last << 6;
      quotM1P.set_slc(3, ui3(qLast));
      quotM1P.set_slc(0, ui3(7));
    }
    else {
      quotP = quot << 3;
      quotP.set_slc(0, ui3(q + 4));
      quotM1P = q == -4 ? quotM1 << 3 : quot << 3;
      quotM1P.set_slc(0, ui3(q + 3));
    }
  }
  else {
    quotP = q >= -2 ? quot << 3 : quotM1 << 3;
    quotP.set_slc(0, ui3(q + 2));
    quotM1P = q >= -1 ? quot << 3 : quotM1 << 3;
    quotM1P.set_slc(0, ui3(q + 1));
  }
  return tuple<ui65, ui65>(quotP, quotM1P);
}

// First step in computation of 10-bit approximation of remainder for second iteration
// of cycle, performed during first iteration of cycle:

ui11 computeRS11(ui71 RP, ui71 RN, int q, ui71 divSigned, ui71 div3Signed) {

  ui13 RP13 = RP.slc<13>(49);
  ui13 RN13 = RN.slc<13>(49);
  ui13 divMult;
  switch (q) {
  case 4: case -4:
    divMult = divSigned.slc<13>(50);
    break;
  case 3: case -3:
    divMult = div3Signed.slc<13>(52);
    break;
  case 2: case -2:
    divMult = divSigned.slc<13>(51);
    break;
  case 1: case -1:
    divMult = divSigned.slc<13>(52);
  }

  ui12 sum = RP13.slc<12>(1) ^ RN13.slc<12>(1) ^ divMult.slc<12>(1);
  ui12 carry = (RP13.slc<12>(0) & ~RN13.slc<12>(0)) | (RP13.slc<12>(0) | ~RN13.slc<12>(0)) & divMult.slc<12>(0);

  ui12 sum12;
  if (q == 0) {
    sum12 =  RP13.slc<12>(1) + ~RN13.slc<12>(1) + 1;
  }
  else {
    sum12 = carry + ~sum + 1;
  }
  return sum12.slc<11>(1);
}

// Second step in computation of 10-bit approximation of remainder for second iteration
// of cycle, performed during second iteration of cycle:

ui10 computeRS10(ui71 divSigned, ui71 div3Signed, int q, ui11 RS11) {
  ui11 divMult;
  switch (q) {
  case 4: case -4:
    divMult = divSigned.slc<11>(55);
    break;
  case 3: case -3:
    divMult = div3Signed.slc<11>(57);
    break;
  case 2: case -2:
    divMult = divSigned.slc<11>(56);
    break;
  case 1: case -1:
    divMult = divSigned.slc<11>(57);
    break;
  case 0:
    divMult = 0;
  }
  ui11 sum11 = RS11 + divMult + 1;
  return sum11.slc<10>(1);
}

// Top-level function:

tuple<ui64, ui8> fdiv8(ui64 opa, ui64 opb, ui2 fmt, bool fz, bool dn, ui2 rmode) {

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

    // Multiples of divisor:
    ui71 div = ui71(sigb) << 14;  // d
    ui71 div2 = div << 1;         // 2*d
    ui71 div3 = div + div2;       // 3*d

    // Comparison constants:
    array<ui10, 8> cmpConst = computeCmpConst(div.slc<6>(60));

    ui71 RP, RN;  // redundant remainder
    int q;  // quotient digit
    int qLast;  // quotient digit before penultimate iteration
    ui65 quot = 0, quotM1 = 0; // quotient and decremented quotient
    ui65 quotLast, quotM1Last; // quotient and decremented quotient upon entering final cycle
    ui65 quotP, quotM1P;  // final quotient and decremented quotient plus rounding increment

    ui10 RS10;  // 10-bit approximation of remainder, used to derive next q
    ui11 RS11;  // 11-bit value computed during first iteration, as a first
                // step in computation of RS10 for second iteration

    // Compare siga and sigb:
    ui53 sigaBar = ~siga;
    ui54 sigCmp = sigb + sigaBar;
    bool sigaLTsigb = sigCmp[53];  // siga < sigb

    // Compute RP_1 = 8 * R_0 = X and exponent of unrounded quotient:
    si13 expQ;  // exponent of unrounded quotient
    if (sigaLTsigb) {
      RP = ui71(siga) << 15;
      expQ = expDiff - 1;
    }
    else {
      RP = ui71(siga) << 14;
      expQ = expDiff;
    }

    // Approximation of 8*R_0 to be used to derive q_1:
    RS10 = RP.slc<10>(61);

    // RN_1 = q_1 * d, where q_1 is either 1 or 2:
    // (Note that q_1 is used only in analysis.)
    ui11 geP2 = RS10 + cmpConst[5];
    if (geP2[10]) {
      q = 2;
      quot = 2;
      quotM1 = 1;
      RN = div2;
    }
    else {
      q = 1;
      quot = 1;
      quotM1 = 0;
      RN = div;
    }
  
    // Approximation of 8*R_1 to be used to derive q_2 in next cycle:
    RS10 = RP.slc<10>(58) + ~RN.slc<10>(58) + 1;

    ui53 Qtrunc, Qinc; // quotient and incremented quotient
    bool stk;          // sticky bit

#ifdef SLEC
    ui65 qmask = 0, quotLo = 0, quotM1Lo = 0;
    ac::probe_map("div", div);
    ac::probe_map("RP", RP);
    ac::probe_map("RN", RN); 
    ac::probe_map("quot", quotLo);
    ac::probe_map("quotM1", quotM1Lo);
#endif
    
    if (divPow2) {
      Qtrunc = ui53(mana) << 1;
      stk = 0;
    }

    else {
      ui5 C; // number of cycles in the iterative phase
      switch (fmt) {
      case DP: C = 9; break;
      case SP: C = 4; break;
      case HP: C = 2;
      }
      bool lsbIs2 = fmt != SP; // lsb of final quotient is bit 2 rather than bit 1

      for (uint i=1; i<=C; i++) { // ith cycle, consisting of 2 iterations

        for (uint j=1; j<=2; j++) {

          q = nextDigit(RS10, cmpConst);
    	  if (j == 1) {
	    // Save these values during the first iteration of the final cycle,
	    // to be used during the final iteration to compute quotP and quotM1P:
	    qLast = q;
	    quotLast = quot;
	    quotM1Last = quotM1;
          }    
          ui71 divSigned, div3Signed;
          if (RS10[9]) {
  	    divSigned = div;
	    div3Signed = div3;
          }
          else {
	    divSigned = ~div;
	    div3Signed = ~div3;
          }
          if (j == 1) {
  	    // On first iteration of cycle,  perform first step in computation
	    // of RS10 for second iteration:
            RS11 = computeRS11(RP, RN, q, divSigned, div3Signed);
          }
         tie (RP, RN) = nextRem(RP, RN, RS10[9], q, divSigned, div3Signed, fmt);
         if (j == 1) {
            // On first iteration of cycle, derive RS10 from RP and RN:
            RS10 = RP.slc<10>(58) + ~RN.slc<10>(58) + 1;
          }
          else {
	    // On second iteration of cycle, complete computation of RS10:
	    RS10 = computeRS10(divSigned, div3Signed, q, RS11);
          }
	  if (j == 2) {
            // Compute rounded quotient and decremented quotient on last iteration:
            tie(quotP, quotM1P) = incQuot(q, quot, quotM1, qLast, quotLast, quotM1Last, lsbIs2);
	  }
	  // update quotient and decremented quotient
          tie (quot, quotM1) = nextQuot(q, quot, quotM1);
        }

#ifdef SLEC
	qmask = (qmask << 6) + 0x3F;
        quotLo = quot & qmask;
        quotM1Lo = quotM1 & qmask;
        ac::probe_map("RP", RP);
        ac::probe_map("RN", RN);
        ac::probe_map("quot", quotLo);
        ac::probe_map("quotM1", quotM1Lo);
#endif
	
      }

      // Select inputs to rounder:
      tie(Qtrunc, Qinc, stk) = computeQ(quot, quotM1, quotP, quotM1P, RP, RN, lsbIs2);
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

SC_MODULE(fdiv8_wrapper) {

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
    tie(data, excps) = fdiv8_wrapper(opa, opb, fmt, fz, dn, rmode);

    // Contract excps to 6 bits to match RTL:
    ui6 excps6 = excps;
    excps6[5] = excps[7];

    D.write(data);
    flags.write(excps6);

  }

  SC_CTOR(fdiv8) {
    SC_METHOD(doit);  
    sensitive_pos << clk;
  }

};

#else

int main() {

ui64 opa = 0x6049608e;
ui64 opb = 0x6920ba64;
ui2 rmode = 0;
bool dn = 0, fz = 0;
ui2 fmt = SP;

ui64 D;
ui8 flags;
tie(D, flags) = fdiv8(opa, opb, fmt, fz, dn, rmode);

printf("opa = %s\n", opa.to_string(AC_HEX, false).c_str());
printf("opb = %s\n", opb.to_string(AC_HEX, false).c_str());
printf("D = %s\n", D.to_string(AC_HEX, false).c_str());
printf("flags = %s\n", flags.to_string(AC_HEX, false).c_str());

 return 0;
}	 

#endif

