#include <stdio.h>
#include <math.h>
#include <string>

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
typedef ac_int<5, false> ui5;
typedef ac_int<6, false> ui6;
typedef ac_int<7, false> ui7;
typedef ac_int<8, false> ui8;
typedef ac_int<10, false> ui10;
typedef ac_int<11, false> ui11;
typedef ac_int<13, false> ui13;
typedef ac_int<23, false> ui23;
typedef ac_int<28, false> ui28;
typedef ac_int<30, false> ui30;
typedef ac_int<31, false> ui31;
typedef ac_int<42, false> ui42;
typedef ac_int<43, false> ui43;
typedef ac_int<44, false> ui44;
typedef ac_int<52, false> ui52;
typedef ac_int<53, false> ui53;
typedef ac_int<54, false> ui54;
typedef ac_int<55, false> ui55;
typedef ac_int<56, false> ui56;
typedef ac_int<57, false> ui57;
typedef ac_int<64, false> ui64;
typedef ac_int<3, true> si3;
typedef ac_int<4, true> si4;
typedef ac_int<13, true> si13;
typedef ac_int<57, true> si57;

//*********************************************
// fdiv2: Multi-Precision Radix-2 SRT Division
//*********************************************

// Formats:

enum Format {HP = 1, SP, DP};

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

// NaN, infinity, or zero operand:

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
  si13 expQ = expaShft - expbShft + bias;
  return tuple<ui53, ui53, si13>(siga, sigb, expQ);
}

// Derive quotient digit from remainder approximation:

int nextDigit (si3 RS3, si3 RC3) {
  si4 R4 = RS3 + RC3;
  if (R4 < -1) {
    return -1;
  }
  else if (R4 == -1) {
    return 0;
  }
  else {
    return 1;
  }
}

// Update remainder.
// The remainder is restricted to the upper w bits; lower 57-w bits are 0.
//  scalar => w = 57
//  SP vector => w = 27
//  HP vector => w = 14

tuple<ui57, ui57> nextRem(ui57 sum0, ui57 car0, ui57 d57, int q, ui2 fmt) {
  ui57 sumIn = sum0 << 1, carIn = car0 << 1, dIn = 0, sumOut = 0, carOut = 0;
  if (q == 0) {
    sumOut = sumIn ^ carIn;
    carOut.set_slc(1, ui56(sumIn.slc<56>(0) & carIn.slc<56>(0)));
  }
  else {
    if (q == 1) {
      dIn = ~d57;
      switch (fmt) {
      case SP: dIn.set_slc(0, ui30(0)); break;
      case HP: dIn.set_slc(0, ui43(0));
      }
    }
    else {
      dIn = d57;
    }
    sumOut = sumIn ^ carIn ^ dIn;
    carOut.set_slc(1, ui56(sumIn.slc<56>(0) & carIn.slc<56>(0) | sumIn.slc<56>(0) & dIn.slc<56>(0) | carIn.slc<56>(0) & dIn.slc<56>(0)));
    if (q == 1) {
      switch (fmt) {
      case DP: carOut[0] = 1; break;
      case SP: carOut[30] = 1; break;
      case HP: carOut[43] = 1;
      }
    }
  }
  if (sumOut[56] != carOut[56]) {
    sumOut[56] = 0;
    carOut[56] = 1;
  }
  else if (q == 1) {
    sumOut[56] = 0;
    carOut[56] = 0;
  }
  else if (q == -1) {
    sumOut[56] = 1;
    carOut[56] = 1;
  }
  return tuple<ui57, ui57>(sumOut, carOut);
}

// Update quotient and decremented quotient with next digit:

tuple<ui55, ui55> nextQuot(ui55 quot, ui55 quotM1, int q, uint i) {
  ui55 nextQuot = q == -1 ? quotM1 : quot;
  nextQuot[55-i] = q != 0;
  ui55 nextQuotM1 = q == 1 ? quot : quotM1;
  nextQuotM1[55-i] = q == 0;
  return tuple<ui55, ui55> (nextQuot, nextQuotM1);
}

// Final result:

tuple<ui64, ui8> final(ui53 Qrnd, bool inx, bool sign, si13 expQ, ui2 rmode, bool fz, ui2 fmt, ui8 flags) {

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
        ui11 exp = Qrnd[52];
        D.set_slc(52, exp);
        D.set_slc(0, Qrnd.slc<52>(0));
        flags[IXC] = flags[IXC] || inx;
        flags[UFC] = flags[UFC] || inx;
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
        ui8 exp = Qrnd[23];
        D.set_slc(23, exp);
        D.set_slc(0, Qrnd.slc<23>(0));
        flags[IXC] = flags[IXC] || inx;
        flags[UFC] = flags[UFC] || inx;
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
        ui5 exp = Qrnd[10];
        D.set_slc(10, exp);
        D.set_slc(0, Qrnd.slc<10>(0));
        flags[IXC] = flags[IXC] || inx;
        flags[UFC] = flags[UFC] || inx;
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

// The RTL uses a 55-bit vector for the partial quotient and a pair of 72-bit vectors for
// the partial remainder, which is represented in carry save form.  For a scalar operation,
// the full quotient vector and the top 57 bits of each remainder vector are used, although
// these width are required only in the DP case.  For a vector SP op, a 27-bit segment of
// each of the three vectors is allocated for each lane.  For a vector HP op, each lane
// uses a 13-bit segment of the quotient vector and a 14-bit segment of each remainder vector.

// This model executes the lanes of a vector op sequentially.  The function fdivLane executes
// a single lane, using a 55-bit vector for the quotient and 2 57-bit vectors for the remainder.
// For a vector op, only the appropriate number of top bits of each vector are used.  This
// allows the eqyivalence checker to establish intermediate maps to reduce complexity.
// Note also that the data parameters are of width 64, but only the bottom 32 or 16 bits are
// used for a SP or HP op.

tuple<ui64, ui8> fdivLane(ui64 opa, ui64 opb, ui2 fmt, bool vec, bool fz, bool dn, ui2 rmode) {

  // Analyze operands and process special cases:
  bool signa, signb;    // operand signs
  ui11 expa, expb;      // operand exponents
  ui52 mana, manb;      // operand mantissas
  Class classa, classb; // operand classes
  ui8 flags = 0;        // exception flags
  tie(signa, expa, mana, classa, flags) = analyze(opa, fmt, fz, flags);
  tie(signb, expb, manb, classb, flags) = analyze(opb, fmt, fz, flags);

  // sign of quotient:
  bool sign = signa ^ signb;

  // Detect early exit:
  if (classa == ZERO || classa == INF || classa == SNAN || classa == QNAN ||
      classb == ZERO || classb == INF || classb == SNAN || classb == QNAN) {
    return specialCase(sign, opa, opb, classa, classb, fmt, dn, flags);
  }

  else {

    // Normalize denormals and compute exponent difference:
    ui53 x, d; // significands of dividend and divisor (1 implicit integer bit)
    si13 expQ;   // exponent difference
    tie(x, d, expQ) = normalize(expa, expb, mana, manb, fmt);
    ui57 x57 = 0, d57 = 0; // x and d represented as 57-bit vectors (2 implicit integer bits)
    x57.set_slc(3, x);
    d57.set_slc(3, d);

    ui55 Qtrunc; // truncated quotient (1 implicit integer bit)
    bool stk;    // sticky bit

    // Detect division by a power of 2:
    if (manb == 0) {
      Qtrunc = ui55(x) << 2;
      stk = 0;
    }

    else {

      // Partial remainder is represented in carry-save form, with 2 implicit integer bits
      ui57 RS = 0, RC = 0;
      ui2 fmtRem = vec ? fmt : DP; // fmt used in computation of remainder

      // 1st SRT iteration is executed in the initial cycle.
      // 1st digit is q = 1; 1st remainder is x - q * d = x - d.  Thus,
      // RS = x, RC = ~d, with 2's complement completed by setting lsb - 1 of each vector:
      RS = x57;
      RC = d57;
      RC = ~RC;
      switch (fmtRem) {
      case DP: RC.set_slc(0, ui2(0)); RS[2] = 1; break;
      case SP: RC.set_slc(0, ui31(0)); RS[31] = 1; break;
      case HP: RC.set_slc(0, ui44(0)); RS[44] = 1;
      }

      // Partial quotient and decremented quotient, with 1 implicit integer bit:
      ui55 quot = 0, quotM1 = 0;

      // Initial partial quotient is 1:
      quot[54] = 1;

      // Quotient digit:
      int q;

      #ifdef SLEC
        ac::probe_map("RS", RS);
        ac::probe_map("RC", RC);
        ac::probe_map("quot", quot);
        ac::probe_map("quotM1", quotM1);
      #endif

      // Each of the subsequent iterative cycles executes 3 iterations. The total number
      // of iterations (each of which extends the partial quotient by 1 bit) must exceed
      // the precision of the op by at least 2, in order (1) to include a guard bit and
      // (2) to allow for a possible leading zero, i.e., a quotient less than 1.  This
      // determines the number C of iterative  cycles:
      uint C;
      switch (fmt) {
      case DP: C = 18; break;
      case SP: C = 9; break;
      case HP: C = 4; break;
      }
      uint N = 3 * C + 1;  // number of iterations

      // Remaining N - 1 iterations:
      for (uint i = 2; i<=N && i<=55; i++) { // absolute bound makes SLEC happy
        q = nextDigit(RS.slc<3>(54), RC.slc<3>(54));      // compute digit
        tie(RS, RC) = nextRem(RS, RC, d57, q, fmtRem);    // update remainder:
        tie(quot, quotM1) = nextQuot(quot, quotM1, q, i); // Update quotient:

        #ifdef SLEC
          ac::probe_map("RS", RS);
          ac::probe_map("RC", RC);
          ac::probe_map("quot", quot);
          ac::probe_map("quotM1", quotM1);
        #endif
      }

      // Select truncated quotient according to sign of remainder:
      si57 RFinal = RS + RC;
      bool RSign = RFinal < 0, RNonzero = RFinal != 0;
      Qtrunc = RSign ? quotM1 : quot;

      // Check for RFinal = -d:
      ui57 RplusDS = RS ^ RC ^ d57;
      ui57 RplusDC = (RS & RC | RS & d57 | RC & d57) << 1;
      ui57 RplusDxor = RplusDS ^ RplusDC;
      ui57 RplusDor = (RplusDS | RplusDC) << 1;
      bool RplusDis0 = RplusDxor == RplusDor;
      assert(RplusDis0 == (RFinal + d57 == 0));

      // Sticky bit:
      stk = RNonzero && !RplusDis0;
    }

    // Division by power of 2 merges with iterative case here.

    // Right shift:
    if (expQ <= 0) {
      ui13 shft = 1 - expQ;
      stk |= shft >= 55 || (Qtrunc & ((ui55(1) << shft) - 1)) != 0;
      Qtrunc >>= shft;
    }

    // Normalize:
    else if (!Qtrunc[54]) {
      expQ--;
      if (expQ > 0) {
        Qtrunc <<= 1;
      }
    }

    // Move to low-order bits:
    switch (fmt) {
    case SP:
      stk |= Qtrunc.slc<29>(0) != 0;
      Qtrunc >>= 29;
      break;
    case HP:
      stk |= Qtrunc.slc<42>(0) != 0;
      Qtrunc >>= 42;
    }

    // Round:
    bool lsb = Qtrunc[2], grd = Qtrunc[1];
    stk |= Qtrunc[0];
    bool inx = grd || stk; // Inexact result:
    ui53 Qrnd;
    if ((rmode == RNE) && grd && (lsb || stk) ||
        (rmode == RUP) && !sign && (grd || stk) ||
        (rmode == RDN) && sign && (grd || stk)) {
      // Subnormal quotient can round up to a power of 2, but a normal quotient cannot;
      // thus, the msb is always retained here:
      Qrnd = Qtrunc.slc<53>(2) + 1;
    }
    else {
      Qrnd = Qtrunc.slc<53>(2);
    }

    // Compute exceptions and assemble final result:
    return final(Qrnd, inx, sign, expQ, rmode, fz, fmt, flags);
  }
}

// The top-level function simply calls fdivLane (once for a scalar operation, twice for
// SP vector, 4 times for HP vector) and combines the results:

tuple<ui64, ui8> fdiv2(ui64 opa, ui64 opb, ui2 fmt, bool vec, bool fz, bool dn, ui2 rmode) {
  ui64 D = 0, DLane;
  ui8 flags = 0, flagsLane;
  uint numLanes = fmt == DP || !vec ? 1 : fmt == SP ? 2 : 4;
  uint width = fmt == SP ? 32 : 16;
  for (uint k=0; k<numLanes && k<4; k++) {
    tie(DLane, flagsLane) = fdivLane(opa, opb, fmt, vec, fz, dn, rmode);
    D |= DLane << (k * width);
   flags |= flagsLane;
    opa >>= width;
    opb >>= width;
  }
  return tuple<ui64, ui8>(D, flags);
}

// RAC end

#ifdef SLEC

SC_MODULE(my_wrapper) {

  sc_in_clk    clk;
  sc_in<bool>  reset;
  sc_in<bool>  vec;
  sc_in<bool>  fz;
  sc_in<bool>  dn;
  sc_in<ui2>   rmode;
  sc_in<ui2>   fmt;
  sc_in<ui64>  opa;
  sc_in<ui64>  opb;

  sc_out<ui64> D;
  sc_out<ui8>  flags;

  void doit() {

    if (reset.read()) {
      return;
    }

    fz.read();
    dn.read();
    rmode.read();
    vec.read();
    fmt.read();
    opa.read();
    opb.read();

    ui64 data;
    ui8 excps;
    tie(data, excps) = fdiv2(opa, opb, fmt, vec, fz, dn, rmode);
    D.write(data);
    flags.write(excps);

  }

  SC_CTOR(my_wrapper) {
    SC_METHOD(doit);
    sensitive_pos << clk;
  }

};

#else

int main() {
  /*
ui64 opa = 0x0000000008000018;
ui64 opb = 0x000ffbffffffffaf;
ui2 rmode = 3;
bool dn = 0, fz = 1;
ui2 fmt = DP;
bool vec = 0;
*/

ui64 opa = 0xf3f6;
ui64 opb = 0xa9c3;
ui2 rmode = 3;
bool dn = 1, fz = 0;
ui2 fmt = HP;
bool vec = 0;

ui64 D;
ui8 flags;
tie(D, flags) = fdiv2(opa, opb, fmt, vec, fz, dn, rmode);
printf("opa = %s\n", opa.to_string(AC_HEX, false).c_str());
printf("opb = %s\n", opb.to_string(AC_HEX, false).c_str());
printf("D = %s\n", D.to_string(AC_HEX, false).c_str());
printf("flags = %s\n", flags.to_string(AC_HEX, false).c_str());

 return 0;
}

#endif

