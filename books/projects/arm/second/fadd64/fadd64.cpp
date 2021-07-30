#define SLEC

#include <stdio.h>
#include <math.h>
#include <rac.h>
#include <string>
#include <vector>

#include "ac_fixed.h"
#include "ac_int.h"

using namespace std;

// RAC begin

typedef ac_int<2, false> ui2;
typedef ac_int<6, false> ui6;
typedef ac_int<7, false> ui7;
typedef ac_int<8, false> ui8;
typedef ac_int<11, false> ui11;
typedef ac_int<12, false> ui12;
typedef ac_int<32, false> ui32;
typedef ac_int<52, false> ui52;
typedef ac_int<53, false> ui53;
typedef ac_int<54, false> ui54;
typedef ac_int<55, false> ui55;
typedef ac_int<56, false> ui56;
typedef ac_int<64, false> ui64;
typedef ac_int<105, false> ui105;
typedef ac_int<108, false> ui108;
typedef ac_int<109, false> ui109;
typedef ac_int<117, false> ui117;
typedef ac_int<128, false> ui128;

//******************************************************
// fadd64: Double-Precision Addition and FMA
//******************************************************

// Rounding modes:

enum Rmode {RNE, RUP, RDN, RTZ};

// Rounding direction:

enum RndDir {rndNear, rndZero, rndInf};

RndDir computeRndDir(ui2 rmode, bool sign) {
  if (rmode == RNE) {
    return rndNear;
  }
  else if (rmode == RTZ || rmode == RUP && sign || rmode == RDN && !sign) {
    return rndZero;
  }
  else { // (rmode == RDN && sign || rmode == RUP && !sign)
    return rndInf;
  }
}

// Flags:

enum Flags {IOC, DZC, OFC, UFC, IXC, IDC=7};

// Default NaN:

const ui64 DefNan = 0x7FF8000000000000;

// Convert an SNaN to a QNaN:

ui64 gag(ui64 x) {
  return x | 0x0008000000000000;
}

// Components of 117-bit operand:

bool sign(ui117 op) {
  return op[116];
}

ui11 expnt(ui117 op) {
  return op.slc<11>(105);
}

ui105 frac(ui117 op) {
  return op.slc<105>(0);
}

// Apply FZ to denormal operands:

tuple<ui117, ui8> checkDenorm(ui117 op, ui8 flags, bool fz) {
  if (fz && expnt(op) == 0 && frac(op) != 0) {
    op.set_slc(0, ui105(0));
    flags[IDC] = 1;
  }
  return tuple<ui117, ui8>(op, flags);
}
	       
// Identify special case (NaN or infinity operand, invalid op, or zero sum) and
// if detected, return data result and updated FPSCR:

tuple<bool, ui64, ui8>
checkSpecial(ui117 opa, ui117 opb, bool fz, bool dn, ui2 rmode, bool opbLong, bool mulOvfl, bool piz, bool mulStk, ui8 flags) {

  bool signa = sign(opa), signb = sign(opb);
  ui11 expa = expnt(opa), expb = expnt(opb);
  ui105 fraca = frac(opa), fracb = frac(opb);
  
  bool opaZero = (expa == 0) && (fraca == 0);
  bool opaInf = (expa == 0x7FF) && (fraca == 0);
  bool opaNan = (expa == 0x7FF) && (fraca != 0);
  bool opaQnan = opaNan && fraca[104];
  bool opaSnan = opaNan && !fraca[104];
  bool opbZero = (expb == 0) && (fracb == 0) && !mulOvfl && !mulStk;
  bool opbInf = (expb == 0x7FF) && (fracb == 0) && !opbLong;
  bool opbNan = (expb == 0x7FF) && (fracb != 0) && !opbLong;
  bool opbQnan = opbNan && fracb[104];
  bool opbSnan = opbNan && !fracb[104];

  bool isSpecial = false, ioc = false;
  ui64 D = 0;

  if (opaSnan) {
    isSpecial = true;
    D = dn ? DefNan : gag(opa.slc<64>(53));
    flags[IOC] = 1; // invalid operand
  }
 else if (piz) { // Note that this has precedence over opaQnan
    isSpecial = true;
    D = DefNan;
    // IOC is already set in mulExcps, so needn't be set here
  }
  else if (opbSnan) {
    isSpecial = true;
    D = dn ? DefNan : gag(opb.slc<64>(53));
    flags[IOC] = 1; // invalid operand
  }
  else if (opaQnan) {
    isSpecial = true;
    D = dn ? DefNan : opa.slc<64>(53);
  }
  else if (opbQnan) {
    isSpecial = true;
    D = dn ? DefNan : opb.slc<64>(53);
  }
  else if (opaInf) {
    isSpecial = true;
    if (opbInf && signa != signb) {
      D = DefNan;
      flags[IOC] = 1; // invalid operand
    }
    else {
      D = opa.slc<64>(53);
    }
  }
  else if (opbInf) {
    isSpecial = true;
    D = opb.slc<64>(53);
  }
  else if (opaZero && opbZero && signa == signb) {
    isSpecial = true;
    D[63] = signa;
  }
  else if (expa == expb && fraca == fracb && !mulOvfl && !mulStk && signa != signb) {
    isSpecial = true;
    if (rmode == RDN) {
      D[63] = 1;
    }
  }
  return tuple<bool, ui64, ui8>(isSpecial, D, flags);
}

// Determine near or far path.  RTL has a nice trick for detecting the cases 
// expb = expa + 1 and expa = expb + 1, but the latter includes expa = 0 and expb = FFF, 
// which therefore uses the near path, although all of this is ignored later and 
// infinity is returned.  In order to model RTL's choice of path, the comparisons
// are done as follows:

bool isFar(ui11 expa, ui11 expb, bool usa) {
  ui12 expaP1 = expa + 1;
  ui12 expbP1 = expb + 1;
  bool isNear = usa && (expa == expb || expa == expbP1 || expb == expaP1);
  return !isNear;
}

// Compute sum and return absolute value, sticky bit, and sign:

tuple<ui108, bool, bool> add(ui117 opa, ui117 opb, bool far, bool usa, bool mulStk) {

  bool signa = sign(opa), signb = sign(opb);
  ui11 expa = expnt(opa), expb = expnt(opb);
  ui105 fraca = frac(opa), fracb = frac(opb), fracl, fracs;
  bool opbGEopa = expb > expa || expb == expa && fracb >= fraca;

  // Construct significands, padding with a zero at the top to allow for a 1-bit 
  // left shift in the case usa && far, and a zero at the bottom to allow for a 
  // 1-bit right shift on the near path:
  ui108 siga = 0;
  siga[106] = expa != 0;
  siga.set_slc(1, fraca);

  ui108 sigb = 0;
  sigb[106] = expb != 0;
  sigb.set_slc(1, fracb);

  // In the case far && !usa, the leading 1 of the sum or difference is at bit 107 or 106.
  // The LZA is designed so that the same is true of the shifted sum in the near case. In 
  // order to for this hold in the case far && usa, we perform a 1-bit left shift:
  ui108 sigaPrime = siga, sigbPrime = sigb;
  if (far && usa) {
    sigaPrime <<= 1;
    sigbPrime <<= 1;
  }

 // Compare the operands and determine the exponent difference for the right shift
 // of the smaller one.  For this purpose, the exponent of a subnormal operand is
 // taken to be 1 rather than 0:
  bool signl; // sign of the result
  ui108 sigl, sigs; // significands of larger and smaller operands
  ui12 expDiff;
  if (opbGEopa) {
    signl = signb;
    sigl = sigbPrime;
    sigs = sigaPrime;
    if (expa == 0 && expb != 0) {
      expDiff = expb - expa - 1;
    }
    else {
      expDiff = expb - expa;
    }
  }
  else {
    signl = signa;
    sigl = sigaPrime;
    sigs = sigbPrime;
    if (expb == 0 && expa != 0) {
      expDiff = expa - expb - 1;
    }
    else {
      expDiff = expa - expb;
    }
  }

  // If the right shift exceeds the significand width, its value is uninteresting.
  // Therefore, we can collapse the 8 bits expDiff[11:4] to 3 bits as follows:
  ui7 rshift = expDiff.slc<7>(0);
  if (expDiff.slc<5>(7) != 0) {
    rshift |= 0x70;
  }

  ui108 sigShft = sigs >> rshift;
  bool shiftOut = (sigShft << rshift) != sigs;

  // Compute the sum or difference and the sticky bit.  In the case of subtraction, 
  // if either (a) sigs = sigb and mulStk = 1 or (b) a non-zero value has been shifted 
  // out, then the computed difference is an overestimate rather then an underestimate.  
  // In this event, we decrement the difference by eliminating the carry-in:
  bool cin = usa && !(mulStk && !opbGEopa || far && shiftOut);
  ui108 ops = usa ? ui108(~sigShft) : sigShft;
  ui108 sum = sigl + ops + cin;
  bool stk = mulStk || far && shiftOut;

  return tuple<ui108, bool, bool>(sum, stk, signl);
}

// Count leading zeroes of a nonzero 128-bit vector.
// After k iterations of the loop, where 0 <= k <= 7, the value of n 
// is 2^(7-k) and the low n entries of z and c are as follows:
// Consider the partition of x into n bit slices of width 2^k.
// For 0 <= i < n, the i^th slice is x[2^k*(i+1)-1:2^k*i].
// Let L(i) be the number of leading zeroes of this slice.  Then
//   z[i] = 1 <=> L(i) = 2^k;
//   L(i) < 2^k => c[i] = L(i).

ui7 CLZ128(ui128 x) {
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

// Count leading zeroes of a + b, where a and b are 128-bit vectors,
// under these assumptions: 
//   (1) the 128-bit sum is not 0; 
//   (2) the addition produces a carry-out
// The result may be an overestimate by 1:

ui7 LZA128(ui128 a, ui128 b) {

  // Let n be index of the lsb of the maximal prefix of the form P*GK* 
  // (where P is propagate, G is generate, K is kill).  Then n > 0 and
  // the index of the leading 1 of the sum is either n or n-1.

  // Construct a vector w that has its leading 1 at index n: 

  ui128 p = a ^ b;
  ui128 k = ~a & ~b;

  // w[i] = ~z[i], where
  //   z[i] = (p[i] & p[i-1]) | (p[i] & g[i-1]) | (g[i] & k[i-1]) | (k[i] & k[i-1])
  //        = (p[i] & (p[i-1] | g[i-1])) | ((g[i] | k[i]) & k[i-1])
  //        = (p[i] & ~k[i-1]) | (~p[i] & k[i-1])
  //        = p[i] ^ k[i-1]
  ui128 w = ~(p ^ (k << 1));

  // Now the number of leading zeroes of w is either equal to the number of
  // leading zeroes of the sum or 1 less, so we pad it with an extra leading zero:
  return CLZ128(w >> 1);
}

// Compute leading zero count of the difference in the near case:

ui7 computeLZA(ui117 opa, ui117 opb) {
  ui128 in1LZA = 0, in2LZA = 0;
  ui11 expa = expnt(opa), expb = expnt(opb);
  ui105 fraca = frac(opa), fracb = frac(opb), fracl, fracs;
  bool opbGEopa = expb > expa || expb == expa && fracb >= fraca;
  if (opbGEopa) {
    fracl = fracb;
    fracs = fraca;
  }
  else {
    fracl = fraca;
    fracs = fracb;
  }
  in1LZA[127] = 1;
  in1LZA.set_slc(22, fracl);
  if (expb[0] == expa[0]) {
    in2LZA = (ui128(1) << 22) - 1;
    in2LZA.set_slc(22, ui105(~fracs));
  }
  else {
    in2LZA = (ui128(1) << 21) - 1;
    in2LZA.set_slc(21, ui105(~fracs));
    in2LZA[127] = 1;
  }
  return LZA128(in1LZA, in2LZA);
}

// Compute left shift and adjusted exponent:

tuple<ui7, ui12> computeLshift(ui117 opa, ui117 opb, bool far, bool usa) {
  ui11 expa = expnt(opa), expb = expnt(opb);
  ui12 expl = expa >= expb ? expa : expb;
  ui7 lshift;   // left shift
  ui12 expShft; // adjusted exponent
  ui7 lza = computeLZA(opa, opb);
  if (far) {
    lshift = 0;
    expShft = usa ? ui12(expl - 1) : expl;
  }
  else if (lza < expl) {
    lshift = lza;
    expShft = expl - lza;
  }
  else {
    lshift = expl == 0 ? ui7(0) : ui7(expl - 1);
    expShft = 0;
  }
  return tuple<ui7, ui12>(lshift, expShft);
}

// The rounding increments and inexact bits for the overflow and non-overflow cases 
// are computed during the left shift.  This is done by applying lsb, guard, and sticky 
// masks to the unshifted sum.  Thus, the masks must be right-shifted by the left shift
// amount.  This may be done as soon as the shift amount is known: 

tuple<bool, bool, bool, bool> rndInfo(ui108 sum, bool stk, ui7 lshift, RndDir rndDir) {

  // lsb, guard, and sticky masks:
  ui56 lOvflMask = 0x80000000000000 >> lshift;
  ui55 gOvflMask = lOvflMask >> 1;	
  ui54 sOvflMask = 0x3FFFFFFFFFFFFF >> lshift;
  ui55 lNormMask = lOvflMask >> 1;
  ui54 gNormMask = lOvflMask >> 2;
  ui53 sNormMask = sOvflMask >> 1;

  // lsb, guard, and sticky bits:
  bool lOvfl = (sum & lOvflMask) != 0;
  bool gOvfl = (sum & gOvflMask) != 0;
  bool sOvfl = (sum & sOvflMask) != 0 || stk;
  bool lNorm = (sum & lNormMask) != 0;
  bool gNorm = (sum & gNormMask) != 0;
  bool sNorm = (sum & sNormMask) != 0 || stk;

  // rounding increments;
  bool incOvfl = (rndDir == rndNear) && gOvfl && (lOvfl || sOvfl) ||
                 (rndDir == rndInf) && (gOvfl || sOvfl);
  bool incNorm = (rndDir == rndNear) && gNorm && (lNorm || sNorm) ||
                 (rndDir == rndInf) && (gNorm || sNorm);

  // inexact bits:
  bool inxOvfl = gOvfl || sOvfl;
  bool inxNorm = gNorm || sNorm;

  return tuple<bool, bool, bool, bool>(incOvfl, incNorm, inxOvfl, inxNorm);

}
 
// Inputs of fadd64:
//   opa[63:0]: sign 63, exponent 62:52, mantissa 51:0
//   opb[116:0]: sign 116, exponent 115:105, mantissa 104:0
//   fz, dn, rmode: FPSCR components
//   fma: fused mul-add
//   inz: multiplier output is infinity, NaN, or zero
//   piz: multiplier computes inf * 0 and returns DefNan
//   expOvfl: bit 11 of opb exponent from multiplier
//   mulExcps[7:0]: exception flags from multiplier

// Outputs of fadd64:
//   D[63:0]: data result
//   flags[7:0]: exception flags

tuple<ui64, ui8> fadd64(ui64 opa, ui117 opb, bool fz, bool dn, ui2 rmode, bool fma, bool inz, bool piz, bool expOvfl, ui8 mulExcps) {

  ui64 D; // data result
  ui8 flags = 0; // initialize flags

  // An fma with a NaN, infinity, or zero from the multiplier is treated as an ordinary add:
  bool opbLong = fma && !inz;

  // expOvfl is qualified by opbLong:
  bool mulOvfl = opbLong && expOvfl;

  // piz is qualified by fma:
  piz = fma && piz;

  // In fma case, mulExcps[IXC] is sticky bit from multiplier:
  bool mulStk = mulExcps[IXC] && opbLong;

  // In fma case, copy flags from multiplier, ignoring mulExcps[IXC] when it is sticky bit:
  if (fma) {
    flags = mulExcps;
    flags[IXC] = flags[IXC] && !opbLong;
  }

  // opa extended to 117 bits:  
  ui117 opax = 0;
  opax.set_slc(53, opa);

  // Apply FZ to denormal operands:
  ui117 opaz, opbz;
  tie(opaz, flags) = checkDenorm(opax, flags, fz);
  if (!fma) {
    tie(opbz, flags) = checkDenorm(opb, flags, fz);
  }
  else {
    opbz = opb;
  }

  // NaN or infinity operand, invalid op, or zero sum:
  bool isSpecial;
  tie(isSpecial, D, flags) = checkSpecial(opaz, opbz, fz, dn, rmode, opbLong, mulOvfl, piz, mulStk, flags);
  if (isSpecial) {
    return tuple<ui64, ui8>(D, flags);
  }

  // Nonzero sum:
  else {

    // Unlike signs:
    bool usa = sign(opaz) != sign(opbz);

    // Far path (unlike signs and exponents within 1):
    bool far = isFar(expnt(opaz), expnt(opbz), usa);

    // Compute sum:
    ui108 sum;
    bool stk, signl;
    tie(sum, stk, signl) = add(opaz, opbz, far, usa, mulStk);

     // Compute left shift and adjusted exsponent:
    ui7 lshift;
    ui12 expShft;
    tie(lshift, expShft) = computeLshift(opaz, opbz, far, usa);

    // Perform the left shift:
    ui108 sumShft = sum << lshift;

    // Sign of result:
    bool signOut = mulOvfl ? sign(opb) : signl;

    // Rounding direction:
    RndDir rndDir = computeRndDir(rmode, signOut);

    // Compute rounding increments and inexact bits while shifting is performed:
    bool incOvfl, incNorm, inxOvfl, inxNorm;
    tie(incOvfl, incNorm, inxOvfl, inxNorm) = rndInfo(sum, stk, lshift, rndDir);

    // Rounding may be done as soon as the shifted sum is available:
    ui54 sumUnrnd = sumShft.slc<54>(54); // unrounded sum, with 2 integer bits
    ui54 sumNorm = sumUnrnd + incNorm; // rounded sum, assuming no overflow
    ui54 sumOvfl = sumUnrnd.slc<53>(1) + incOvfl; // rounded sum, assuming overflow
    
    // Case analysis:
    bool tiny =  !sumUnrnd[53] && !sumUnrnd[52]; // unrounded sum is subnormal
    bool ovfl = sumNorm[53]; // overflow
    bool ovfl2 = (sumUnrnd.slc<53>(1) == ((ui54(1) << 53) - 1)) && incOvfl; // double overflow
    bool infOrMax = expShft == 0x7FE && (ovfl || ovfl2) || expShft == 0x7FD && ovfl2 || 
                    expShft == 0x7FF && opbLong || mulOvfl; // rounded sum is supernormal

    // Computation of final result and exception flags:
    ui11 expOut;
    ui52 fracOut;
    if (infOrMax) { // supernormal rounded result
      if (rndDir == rndZero) { // return largest normal
        expOut = 0x7FE;
        fracOut = 0xFFFFFFFFFFFFF;
      }
      else { // return infinity
        expOut = 0x7FF;
        fracOut = 0;
      }
      flags[OFC] = 1; // overflow
      flags[IXC] = 1; // inexact
    }
    else if (tiny) { // subnormal unrounded result
      if (fz) { // flush to zero
        expOut = 0;
        fracOut = 0;
        flags[UFC] = 1; // underflow but not inexact
      }
      else if (sumNorm[52]) { // rounded up to normal
        expOut = 1;
        fracOut = 0;
        flags[UFC] = 1; // underflow
        flags[IXC] = 1; // inexact
      }
      else { // rounded result is subnormal
        expOut = expShft; // expOut = 0
        fracOut = sumNorm.slc<52>(0);
        if (inxNorm) {
          flags[UFC] = 1; // underflow
          flags[IXC] = 1; // inexact
        }
      }
    }
    else if (ovfl2) { // double overflow
      expOut = expShft + 2;
      fracOut = 0;
      flags[IXC] = flags[IXC] || inxOvfl; // inexact
    }
    else if (ovfl) { // overflow or double overflow of subnormal
      expOut = expShft == 0 ? ui11(2) : ui11(expShft + 1);
      fracOut = sumOvfl.slc<52>(0);
      flags[IXC] = flags[IXC] || inxOvfl; // inexact
    }
    else {
      expOut = expShft == 0 && sumNorm[52] ? ui11(1) : ui11(expShft); // overflow of subnormla
      fracOut = sumNorm.slc<52>(0);
      flags[IXC] = flags[IXC] || inxNorm; // inexact
    }
    D[63] = signOut;
    D.set_slc(52, expOut);
    D.set_slc(0, fracOut);

    return tuple<ui64, ui8>(D, flags);
  }
}

// RAC end
#ifdef TEST_MAIN

int main() {

ui64 opa = 0x8000000000000001;
ui117 opb = 0x0;
ui2 rmode = rmodeZero;
bool fz = 1;
bool dn = 0;
bool fma = 1;
bool piz = 0;
bool inz = 0;
bool expOvfl = 0;
ui6 mulExcps = 0x11;

ui64 sum;
ui6 excps;
tie(sum, excps) = fadd64(opa, opb, fz, dn, rmode, fma, piz, inz, expOvfl, mulExcps);

printf("opa = %s\n", opa.to_string(AC_HEX, false).c_str());
printf("opb = %s\n", opb.to_string(AC_HEX, false).c_str());
printf("sum = %s\n", sum.to_string(AC_HEX, false).c_str());
printf("excps = %s\n", excps.to_string(AC_HEX, false).c_str());


 return 0;
}	 

#endif

#ifdef SLEC

SC_MODULE(fadd) {

  sc_in_clk    clk;
  sc_in<bool>  reset;
  sc_in<bool>  fz;
  sc_in<bool>  dn;
  sc_in<ui2>   rmode;
  sc_in<bool>  fma;
  sc_in<bool>  inz;
  sc_in<bool>  piz;
  sc_in<bool>  expOvfl;
  sc_in<ui8>   mulExcps;
  sc_in<ui64>  opa;
  sc_in<ui117> opb;

  sc_out<ui64> D;
  sc_out<ui6> flags;

  void doit() {

    if (reset.read()) {
      return;
    }
  
    fz.read();
    dn.read();
    rmode.read();
    fma.read();
    inz.read();
    piz.read();
    expOvfl.read();
    mulExcps.read();
    opa.read();
    opb.read();

    ui64 sum;
    ui8 excps;
    tie(sum, excps) = fadd64(opa, opb, Rin, fma, inz, piz, expOvfl, mulExcps);

    // Contract excps to 6 bits to match RTL:
    ui6 excps6 = excps;
    excps6[5] = excps[7];

    D.write(sum);
    flags.write(excps6);

  }

  SC_CTOR(fadd) {
    SC_METHOD(doit);  
    sensitive_pos << clk;
  }

};

#endif
