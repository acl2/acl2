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
typedef ac_int<32, false> ui32;
typedef ac_int<40, false> ui40;
typedef ac_int<52, false> ui52;
typedef ac_int<53, false> ui53;
typedef ac_int<54, false> ui54;
typedef ac_int<59, false> ui59;
typedef ac_int<64, false> ui64;
typedef ac_int<65, false> ui65;
typedef ac_int<71, false> ui71;
typedef ac_int<128, false> ui128;
typedef ac_int<13, true> si13;
typedef ac_int<65, true> si65;
typedef ac_int<128, true> si128;

//********************************
// idiv8: 64-bit Integer Division
//********************************

// Count leading zeroes of a nonzero 64-bit vector.
// After k iterations of the loop, where 0 <= k <= 6, the value of n 
// is 2^(6-k) and the low n entries of z and c are as follows:
// Consider the partition of x into n bit slices of width 2^k.
// For 0 <= i < n, the i^th slice is x[2^k*(i+1)-1:2^k*i].
// Let L(i) be the number of leading zeroes of this slice.  Then
//   z[i] = 1 <=> L(i) = 2^k;
//   L(i) < 2^k => c[i] = L(i).

ui6 CLZ64(ui64 x) {
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

// This function operates on a 64-bit vector x.
// The boolean argument isNeg indicates that the operation is signed and the
// sign bit of x is set.  Thus, the value represented by x is x if isNeg = 0
// and x - 2^(64) if isNeg = 1.  We shall show that 2^(64) - x is a power of 2
// iff 2x ^ x is a power of 2.  Thus, we define z as
//
//   z = x       if isNeg = 0
//       2x ^ x  if isNeg = 1
//
// and our objective is to determine whether z is a power of 2.

// The program maintains a width w, a vector v, and an array of vectors A.
// Initially, w = 64 and v = x. After i iterations, where 0 <= i <= 6,
// z is conceptually partitioned to 2^i segments of width w = 2^(6-i).
// The first i entries of A are valid, as are the least significant w bits of
// each of the vectors v, A[0], ..., and A[i-1].  For 0 <= b < w, let C(z, b, i) 
// be the number of indices k, 0 <= k < 64, such that k mod w = b and z[k] = 1.  
// The following invariant holds:
//
//   (a) C(z, b, i) > 0 <=> v[b] = 1;
//
//   (b) C(z, b, i) = 0 => A[0][b] = ... = A[i-1][b] = 0.
//
//   (c) C(z, b, i) = 1 <=> A[0][b] = ... = A[i-1][b] = 1.
//
// In particular, after 6 iterations, since w = 1 and k mod 1 = 0 for all k,
// C(z, 0, 6) is the the number of indices k, 0 <= k < 64, such that z[k] = 1.
// Thus, z is a power of 2 <=> C(z, 0, 6) = 1, and therefore, according to (c),
//
//   z is a power of 2 <=> A[0][0] = ... = A[5][0] = 1.

bool isPow2(ui64 x, bool isNeg) {
  ui64 z;
  if (isNeg) {
    z = (x << 1) ^ x;
  }
  else {
    z = x;
  }
  uint w = 64;
  ui64 v = z; 
  ui64 A[6];
  for (uint i=0; i<6; i++) {
    w = w/2;
    for (uint j=0; j<i; j++) {
      A[j] |= A[j] >> w;
    }
    A[i] = v ^ (v >> w);
    v |= v >> w;
  }
  bool result = true;
  for (uint i=0; i<6; i++) {
    result = result && A[i][0];
  }
  return result;
}

// Division by a power of 2.
// arg is either opa or -opa, with the sign of the quotient, sgnQ.
// shft is the exponent of opb.

ui64 divPow2(ui64 arg, bool sgnQ, ui6 shft) {
  if (sgnQ) {
    si128 padA = ui128(arg) << 64;
    si128 shftA = padA >> shft;
    if (shftA.slc<64>(0) == 0) {
      return shftA.slc<64>(64);
    }
    else {
      return shftA.slc<64>(64) + 1;
    }
  }
  else {
    return arg >> shft;
  }
}

// This function returns a boolean indication of |opb| > |opa|.
// The difference |mskA| - |mskB| is computed according to the following table:

//     sgnA  sgnB |  |mskA| - |mskB|
//    -------------------------------
//       +     +  |  mskA + ~mskB + 1  
//       +     -  |  mskA +  mskB + 0
//       -     +  | ~mskA + ~mskB + 2
//       -     -  | ~mskA +  mskB + 1

// Note that there is a carry-in in all cases except sgnA = 0 and sgnB = 1,
// and in the case sgnA = 1 and sgnB = 0, we must add an extra 1.  This is
// done by means of a half-adder.

bool compareOps(ui64 opa, ui64 opb, bool sgnA, bool sgnB, bool int32) {

  bool cin = sgnA || !sgnB;  // carry-in

  ui64 sum = ~opa ^ ~opb;    // half-adder with second carry-in 
  ui64 car = (~opa & ~opb) << 1;
  if (int32) {
    car[32] = 1;
  }
  else {
    car[0] = 1;
  }

  ui64 argA = sgnA && !sgnB ? ui64(sum) : sgnA ? ui64(~opa) : ui64(opa);
  ui64 argB = sgnA && !sgnB ? ui64(car) : sgnB ? ui64(opb) : ui64(~opb);
  if (int32) {
    argA.set_slc(0, ui32(0));
    argB.set_slc(0, ui32(0xFFFFFFFF));
  }
  ui65 diff = argA + argB + cin;
  return !diff[64];
}
  
// Derive an array of 8 comparison constants based on the leading 6 bits of the divisor:

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

tuple<ui71, ui71> nextRem(ui71 RP, ui71 RN, bool remSign, int q, ui71 divSigned, ui71 div3Signed, bool int32) {

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
  if (int32) {
    RP.set_slc(33, carry.slc<38>(32));
    RP[32] = !remSign;
    RN.set_slc(32, sum.slc<39>(32));
  }
  else {
    RP.set_slc(1, carry.slc<70>(0));
    RP[0] = !remSign;
    RN = sum;
 }

 if (q == 0) {
   return tuple<ui71, ui71>(RP8, RN8);
 }
 else {
   return tuple<ui71, ui71>(RP, RN);
 }
}

// Update signed quotient and decremented quotient with next digit:

tuple<ui65, ui65> nextQuot(bool sgnQ, int q, ui65 quot, ui65 quotM) {
  if (sgnQ) {
    q = -q;
  }
  ui65 quotNew, quotMNew;
  quotNew = q >= 0 ? quot << 3 : quotM << 3;
  quotNew.set_slc(0, ui3(q));
  quotMNew = q > 0 ? quot << 3 : quotM << 3;
  quotMNew.set_slc(0, ui3(q - 1));
  return tuple<ui65, ui65>(quotNew, quotMNew);
}

// Add rounding increment to quotient (used only in case of a negative quotient):

ui65 incQuot(bool sgnQ, int q, ui65 quot, ui65 quotM, int qLast, ui65 quotLast, ui65 quotMLast, uint K) {
  if (sgnQ) {
    q = -q;
    qLast = -qLast;
  }
  ui65 quotP;
  if (K == 2) {
    if (q == 4) {
      // This is the case in which the final q together with the increment produces a carry
      // into the penultimate quotient bit, requiring backtracking.
      quotP = qLast >= -1 ? quotLast << 6 : quotMLast << 6;
      quotP.set_slc(3, ui3(qLast + 1));
    }
    else {
      quotP = quot << 3;
      quotP.set_slc(0, ui3(q + 4));
    }
  }
  else if (K == 1) {
    quotP = q >= -2 ? quot << 3 : quotM << 3;
    quotP.set_slc(0, ui3((q + 2)));
  }
  else { // K == 0) {
    quotP = q >= -1 ? quot << 3 : quotM << 3;
    quotP.set_slc(0, ui3((q + 1)));
  }
  return quotP;
}

// First step in computation of the 10-bit approximation of remainder for the
// second iteration of a cycle, performed during first iteration of the cycle:

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

// Second step in computation of 10-bit approximation of the remainder for the
// second iteration of cycle, performed during the second iteration of cycle:

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

// The top-level function:

ui64 idiv8(ui64 opa, ui64 opb, bool int32, bool sgnd) {

  bool sgnA = sgnd && opa[63];  // A < 0
  bool sgnB = sgnd && opb[63];  // B < 0
  bool sgnQ = sgnA ^ sgnB;      // A/B < 0

  bool BgtA = compareOps(opa, opb, sgnA, sgnB, int32);  // |B| > |A|

  ui64 mskA = opa, mskB = opb;
  if (int32) {  // 0 out low half in case int32
    mskA.set_slc(0, ui32(0));
    mskB.set_slc(0, ui32(0));
  }

  ui64 negA = ~mskA + 1; // -A, valid only if sgnd == 1
  ui64 negB = ~mskB + 1; // -B, valid only if sgnd == 1
  ui64 absA = sgnA ? negA : mskA;  // |A|
  ui64 absB = sgnB ? negB : mskB;  // |B|

  ui6 clzA = CLZ64(absA);  // Leading 0s of |A|
  ui6 clzB = CLZ64(absB);  // Leading 0s of |B|

  if (mskB == 0 || BgtA) {  // B = 0 or |A| < |B|
    return 0;
  }
  
  else if (isPow2(mskB, sgnB)) {  // |B| is a power of 2
    return divPow2(sgnB ? negA : mskA, sgnQ, ~clzB);
  }

  else if (clzA == clzB) {  // |A/B| = 1
    return sgnQ ? ui64(0xFFFFFFFFFFFFFFFF) : ui64(1);
  }

  else {

    ui71 div = ui71(absB) << (clzB + 3);  // d
    ui71 div2 = div << 1;                 // 2*d
    ui71 div3 = div + div2;               // 3*d
    ui71 RP, RN;  // redundant remainder
    int q;  // quotient digit
    int qLast;  // q upon entering final cycle
    ui65 quot = 0, quotM = 0, quotP = 0; // quotient, decremented quotient, incremented quotient
    ui65 quotLast, quotMLast; // quotient and decremented quotient upon entering final cycle

    ui10 RS10;  // 10-bit approximation of remainder, used to derive next q
    ui11 RS11;  // 11-bit value computed during first iteration, as a first
                // step in computation of RS10 for second iteration

    array<ui10, 8> cmpConst = computeCmpConst(div.slc<6>(60));  // Comparison constants

    // Compute RP_1 = 8 * R_0 = X
    RP = ui71(absA) << (clzA + 3);

    // Approximation of 8*R_0 to be used to derive q_1:
    RS10 = RP.slc<10>(61);

    // RN_1 = q_1 * d, where q_1 is either 1 or 2:
    ui11 geP2 = RS10 + cmpConst[5];
    if (geP2[10]) {
      q = 2;
      RN = div2;
    }
    else {
      q = 1;
      RN = div;
    }

    // Initialize quotient and decremented quotient:
    if (sgnQ) {
      quot = -q;
      quotM = -q - 1;
    }
    else {
      quot = q;
      quotM = q - 1;
    }
  
    // Approximation of 8*R_1 to be used to derive q_2 in next cycle:
    RS10 = RP.slc<10>(58) + ~RN.slc<10>(58) + 1;

 #ifdef SLEC
    ac::probe_map("div", div);
    ac::probe_map("RP", RP);
    ac::probe_map("RN", RN); 
    ac::probe_map("quot", quot);
    ac::probe_map("quotM", quotM);
#endif

    // Iterative phase:
    uint delta = clzB - clzA;   // number of bits of quotient
    uint bitsMod6 = delta % 6;  // number of bits generated on final cycle
    uint C = bitsMod6 == 0 ? delta/6 : 1 + delta/6;  // number of iterative cycles
    bool only1Iter = delta <= 3;  // only 1 iteration
    bool skipIter = !only1Iter && 0 < bitsMod6 && bitsMod6 <= 3;  // skip second iteration of penultimate cycle
    uint K;  // number of bits discarded from final quotient
    switch (delta % 3) {
    case 0: K = 0; break;
    case 1: K = 2; break;
    case 2: K = 1;
    }

    for (uint i=1; i<=C && i<=11; i++) { // ith cycle, consisting of 2 iterations
                                         // i<=11 is provable and required to make SLEC happy
      for (uint j=1; j<=2; j++) {

        if (j == 2 && (only1Iter || skipIter && i == C - 1)) {
	  // skip second iteration of cycle in these cases
	}
	else {
          q = nextDigit(RS10, cmpConst);
          if (j == 1) {
            // Save these values during the first iteration of the final cycle,
            // to be used during the final iteration to compute quotP:
	    qLast = q;
	    quotLast = quot;
	    quotMLast = quotM;
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
          tie (RP, RN) = nextRem(RP, RN, RS10[9], q, divSigned, div3Signed, int32);
          if (j == 1) {
            // On first iteration of cycle, derive RS10 from RP and RN:
            RS10 = RP.slc<10>(58) + ~RN.slc<10>(58) + 1;
          }
          else {
            // On second iteration of cycle, complete computation of RS10:
            RS10 = computeRS10(divSigned, div3Signed, q, RS11);
            // Compute incremented quotient on last iteration:
            quotP = incQuot(sgnQ, q, quot, quotM, qLast, quotLast, quotMLast, K);
          }
          // update quotient and decremented quotient
          tie (quot, quotM) = nextQuot(sgnQ, q, quot, quotM);
	  // Compute incremented quotient in case of only 1 iteration:
	  if (j == 1) {
	    quotP = quot + (1 << K);
	  }
        }
      }

#ifdef SLEC
        ac::probe_map("RP", RP);
        ac::probe_map("RN", RN);
        ac::probe_map("quot", quot);
        ac::probe_map("quotM", quotM);
#endif	

    }

    // Convert quot, quotM, and quotP to signed integers before shifting:
    si65 quotSigned = quot, quotMSigned = quotM, quotPSigned = quotP;
    
    // Determine whether any bits of quot will be shifted out:
    bool isLost = (quotSigned & ((1 << K) - 1)) != 0;

    ui64 quot0 = quotSigned >> K, quotM0 = quotMSigned >> K, quotP0 = quotPSigned >> K;

    ui71 rem = RP + ~RN + 1;  // Sign of final remainder is rem[70]

    if (sgnQ && (isLost || rem[70])) {
      return quotP0;
    }
    else if (!sgnQ && !isLost && rem[70]) {
      return quotM0;
    }
    else {
      return quot0;
    }
      
  }
}

// RAC end

#ifdef SLEC

SC_MODULE(idiv8_wrapper) {

  sc_in_clk    clk;
  sc_in<bool>  reset;
  sc_in<bool>  int32;
  sc_in<bool>  sgnd;
  sc_in<ui64>  opa;
  sc_in<ui64>  opb;

  sc_out<ui64> D;

  void doit() {

    if (reset.read()) {
      return;
    }
  
    int32.read();
    sgnd.read();
    opa.read();
    opb.read();

    ui64 data = idiv8(opa, opb, int32, sgnd);
    D.write(data);

  }

  SC_CTOR(idiv8_wrapper) {
    SC_METHOD(doit);  
    sensitive_pos << clk;
  }

};

#else

int main() {

  ui64 opa = 0xe150a049f26c2ac6;
  ui64 opb = 0x15c18ef7968639f8;

  ui64 D = idiv8(opa, opb, 1, 1);

  printf("opa = %s\n", opa.to_string(AC_HEX, false).c_str());
  printf("opb = %s\n", opb.to_string(AC_HEX, false).c_str());
  printf("D = %s\n", D.to_string(AC_HEX, false).c_str());

  return 0;
}	 

#endif

