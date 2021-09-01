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
typedef ac_int<9, false> ui9;
typedef ac_int<10, false> ui10;
typedef ac_int<11, false> ui11;
typedef ac_int<12, false> ui12;
typedef ac_int<16, false> ui16;
typedef ac_int<23, false> ui23;
typedef ac_int<29, false> ui29;
typedef ac_int<32, false> ui32;
typedef ac_int<52, false> ui52;
typedef ac_int<53, false> ui53;
typedef ac_int<54, false> ui54;
typedef ac_int<55, false> ui55;
typedef ac_int<57, false> ui57;
typedef ac_int<59, false> ui59;
typedef ac_int<61, false> ui61;
typedef ac_int<63, false> ui63;
typedef ac_int<64, false> ui64;
typedef ac_int<71, false> ui71;
typedef ac_int<72, false> ui72;
typedef ac_int<73, false> ui73;
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

// Formats:

enum Format {HP, SP, DP};

//const uint HP = 0;
//const uint SP = 1;
//const uint DP = 2;

// Rounding modes:

const ui2 rmodeNear = 0;
const ui2 rmodeUP = 1;
const ui2 rmodeDN = 2;
const ui2 rmodeZero = 3;

// Data classes:

enum Class {ZERO, INF, SNAN, QNAN, NORM, DENORM};

// Flags:

const uint IDC = 7; // denormal exxception
const uint IXC = 4; // inexact exception
const uint UFC = 3; // underflow
const uint OFC = 2; // overflow
const uint DZC = 1; // divide-by-zero exception
const uint IOC = 0; // invalid operand exception

// Extract operand components, apply FZ, identify data class, and record denormal exception:

tuple<bool, ui11, ui52, Class, ui8> analyze(ui64 op, Format fmt, bool fz, ui8 flags) {

  // Extract fields:

  bool sign;
  ui11 exp;
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

// Handle the special case of a zero, infinity, or NaN operand:

tuple<ui117, ui8, bool, bool, bool> specialCase
(ui64 opa, ui64 opb, Class classa, Class classb, bool dn, bool fused, ui8 flags) {

  ui117 D = 0;
  ui64 zero = 0;
  zero[63] = opa[63] ^ opb[63];
  ui64 infinity = 0x7FF0000000000000 | zero;
  ui64 manMSB = 0x8000000000000;
  ui64 defNaN = 0x7FF8000000000000;
  bool prodInfZero = false;

  if (classa == SNAN) {
    D = dn ? defNaN : fused ? opa : opa | manMSB;
    flags[IOC] = 1; // invalid operand
  }
  else if (classb == SNAN) {
    D = dn ? defNaN : fused ? opb : opb | manMSB;
    flags[IOC] = 1; // invalid operand
  }
  else if (classa == QNAN) {
    D = dn ? defNaN : opa;
  }
  else if (classb == QNAN) {
    D = dn ? defNaN : opb;
  }
  else if (classa == INF && classb == ZERO || classb == INF && classa == ZERO) {
    D = defNaN;
    prodInfZero = true;
    flags[IOC] = 1; // invalid operand
  }
  else if (classa == INF || classb == INF) {
    D = infinity;
  }
  else if (classa == ZERO || classb == ZERO) {
    D = zero;
  }

  if (fused) {
    D <<= 53;
  }
  bool infNanZero = true, expGTinf = false;

  return tuple<ui117, ui8, bool, bool, bool>(D, flags, prodInfZero, infNanZero, expGTinf);
}

// Count leading zeroes of a nonzero 53-bit vector.
// After k iterations of the loop, where 0 <= k <= 6, the value of n
// is 2^(6-k) and the low n entries of z and c are as follows:
// Consider the partition of x into n bit slices of width 2^k.
// For 0 <= i < n, the i^th slice is x[2^k*(i+1)-1:2^k*i].
// Let L(i) be the number of leading zeroes of this slice.  Then
//   z[i] = 1 <=> L(i) = 2^k;
//   L(i) < 2^k => c[i] = L(i).

ui6 CLZ53(ui53 m) {
  ui64 x = 0;
  x.set_slc(11, m);
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

// Compress the sum of 29 products to 2-vector redundant form, using 27 3-2 compressors.

// Since the final sum is a 106-bit vector, the RTL (quite naturally) limits every intermediate result
// to 106 bits.  The C model, however, in order to simplify the proof, doers not.  This discrepancy
// should not affect the equivalence proof.

// The following comment is taken from the RTL:

// For full adders receiving three inputs at the same time, t, the sum output emerges after 2 XOR delays
// (i.e. t+2) and the carry output after the equivalent of 1 XOR delay from a cgen cell (i.e. t+1)
// For full adders receiving two inputs at time t, and the third input at time t+1 (i.e. 1 XOR delay later),
// the sum and carry outputs both emerge at time t+2
// Can exploit these timings to good effect in order to build reduction trees with minimum-depth logic

tuple<ui106, ui106> compress(array<ui57, 27> pp, ui52 ia, ui53 ib) {

  // Time 0:

  ui59 t0fa0ina, t0fa0inb, t0fa0inc, t2pp0s, t1pp0c;
  t0fa0ina = pp[0];
  t0fa0inb = pp[1];
  t0fa0inc = ui59(pp[2]) << 2;
  t2pp0s = t0fa0ina ^ t0fa0inb ^ t0fa0inc;
  t1pp0c = t0fa0ina & t0fa0inb | t0fa0ina & t0fa0inc | t0fa0inb & t0fa0inc;

  ui61 t0fa1ina, t0fa1inb, t0fa1inc, t2pp1s, t1pp1c;
  t0fa1ina = pp[3];
  t0fa1inb = ui61(pp[4]) << 2;
  t0fa1inc = ui61(pp[5]) << 4;
  t2pp1s = t0fa1ina ^ t0fa1inb ^ t0fa1inc;
  t1pp1c = t0fa1ina & t0fa1inb | t0fa1ina & t0fa1inc | t0fa1inb & t0fa1inc;

  ui61 t0fa2ina, t0fa2inb, t0fa2inc, t2pp2s, t1pp2c;
  t0fa2ina = pp[6];
  t0fa2inb = ui61(pp[7]) << 2;
  t0fa2inc = ui61(pp[8]) << 4;
  t2pp2s = t0fa2ina ^ t0fa2inb ^ t0fa2inc;
  t1pp2c = t0fa2ina & t0fa2inb | t0fa2ina & t0fa2inc | t0fa2inb & t0fa2inc;

  ui61 t0fa3ina, t0fa3inb, t0fa3inc, t2pp3s, t1pp3c;
  t0fa3ina = pp[9];
  t0fa3inb = ui61(pp[10]) << 2;
  t0fa3inc = ui61(pp[11]) << 4;
  t2pp3s = t0fa3ina ^ t0fa3inb ^ t0fa3inc;
  t1pp3c = t0fa3ina & t0fa3inb | t0fa3ina & t0fa3inc | t0fa3inb & t0fa3inc;

  ui61 t0fa4ina, t0fa4inb, t0fa4inc, t2pp4s, t1pp4c;
  t0fa4ina = pp[12];
  t0fa4inb = ui61(pp[13]) << 2;
  t0fa4inc = ui61(pp[14]) << 4;
  t2pp4s = t0fa4ina ^ t0fa4inb ^ t0fa4inc;
  t1pp4c = t0fa4ina & t0fa4inb | t0fa4ina & t0fa4inc | t0fa4inb & t0fa4inc;

  ui61 t0fa5ina, t0fa5inb, t0fa5inc, t2pp5s, t1pp5c;
  t0fa5ina = pp[15];
  t0fa5inb = ui61(pp[16]) << 2;
  t0fa5inc = ui61(pp[17]) << 4;
  t2pp5s = t0fa5ina ^ t0fa5inb ^ t0fa5inc;
  t1pp5c = t0fa5ina & t0fa5inb | t0fa5ina & t0fa5inc | t0fa5inb & t0fa5inc;

  ui61 t0fa6ina, t0fa6inb, t0fa6inc, t2pp6s, t1pp6c;
  t0fa6ina = pp[18];
  t0fa6inb = ui61(pp[19]) << 2;
  t0fa6inc = ui61(pp[20]) << 4;
  t2pp6s = t0fa6ina ^ t0fa6inb ^ t0fa6inc;
  t1pp6c = t0fa6ina & t0fa6inb | t0fa6ina & t0fa6inc | t0fa6inb & t0fa6inc;

  ui61 t0fa7ina, t0fa7inb, t0fa7inc, t2pp7s, t1pp7c;
  t0fa7ina = pp[21];
  t0fa7inb = ui61(pp[22]) << 2;
  t0fa7inc = ui61(pp[23]) << 4;
  t2pp7s = t0fa7ina ^ t0fa7inb ^ t0fa7inc;
  t1pp7c = t0fa7ina & t0fa7inb | t0fa7ina & t0fa7inc | t0fa7inb & t0fa7inc;

  ui61 t0fa8ina, t0fa8inb, t0fa8inc, t2pp8s, t1pp8c;
  t0fa8ina = pp[24];
  t0fa8inb = ui61(pp[25]) << 2;
  t0fa8inc = ui61(pp[26]) << 4;
  t2pp8s = t0fa8ina ^ t0fa8inb ^ t0fa8inc;
  t1pp8c = t0fa8ina & t0fa8inb | t0fa8ina & t0fa8inc | t0fa8inb & t0fa8inc;

  // Time 1:

  ui71 t1fa0ina, t1fa0inb, t1fa0inc, t3pp0s, t2pp0c;
  t1fa0ina = t1pp0c;
  t1fa0inb = ui71(t1pp1c) << 4;
  t1fa0inc = ui71(t1pp2c) << 10;
  t3pp0s = t1fa0ina ^ t1fa0inb ^ t1fa0inc;
  t2pp0c = t1fa0ina & t1fa0inb | t1fa0ina & t1fa0inc | t1fa0inb & t1fa0inc;

  ui73 t1fa1ina, t1fa1inb, t1fa1inc, t3pp1s, t2pp1c;
  t1fa1ina = t1pp3c;
  t1fa1inb = ui73(t1pp4c) << 6;
  t1fa1inc = ui73(t1pp5c) << 12;
  t3pp1s = t1fa1ina ^ t1fa1inb ^ t1fa1inc;
  t2pp1c = t1fa1ina & t1fa1inb | t1fa1ina & t1fa1inc | t1fa1inb & t1fa1inc;

  ui73 t1fa2ina, t1fa2inb, t1fa2inc, t3pp2s, t2pp2c;
  t1fa2ina = t1pp6c;
  t1fa2inb = ui73(t1pp7c) << 6;
  t1fa2inc = ui73(t1pp8c) << 12;
  t3pp2s = t1fa2ina ^ t1fa2inb ^ t1fa2inc;
  t2pp2c = t1fa2ina & t1fa2inb | t1fa2ina & t1fa2inc | t1fa2inb & t1fa2inc;

  // Time 2:

  ui71 t2fa0ina, t2fa0inb, t2fa0inc, t4pp0s, t3pp0c;
  t2fa0ina = t2pp0s;
  t2fa0inb = ui71(t2pp1s) << 4;
  t2fa0inc = ui71(t2pp2s) << 10;
  t4pp0s = t2fa0ina ^ t2fa0inb ^ t2fa0inc;
  t3pp0c = t2fa0ina & t2fa0inb | t2fa0ina & t2fa0inc | t2fa0inb & t2fa0inc;

  ui73 t2fa1ina, t2fa1inb, t2fa1inc, t4pp1s, t3pp1c;
  t2fa1ina = t2pp3s;
  t2fa1inb = ui73(t2pp4s) << 6;
  t2fa1inc = ui73(t2pp5s) << 12;
  t4pp1s = t2fa1ina ^ t2fa1inb ^ t2fa1inc;
  t3pp1c = t2fa1ina & t2fa1inb | t2fa1ina & t2fa1inc | t2fa1inb & t2fa1inc;

  ui73 t2fa2ina, t2fa2inb, t2fa2inc, t4pp2s, t3pp2c;
  t2fa2ina = t2pp6s;
  t2fa2inb = ui73(t2pp7s) << 6;
  t2fa2inc = ui73(t2pp8s) << 12;
  t4pp2s = t2fa2ina ^ t2fa2inb ^ t2fa2inc;
  t3pp2c = t2fa2ina & t2fa2inb | t2fa2ina & t2fa2inc | t2fa2inb & t2fa2inc;

  ui107 t2fa3ina, t2fa3inb, t2fa3inc, t4pp3s, t3pp3c;
  t2fa3ina = t2pp0c;
  t2fa3inb = ui107(t2pp1c) << 16;
  t2fa3inc = ui107(t2pp2c) << 34;
  t4pp3s = t2fa3ina ^ t2fa3inb ^ t2fa3inc;
  t3pp3c = t2fa3ina & t2fa3inb | t2fa3ina & t2fa3inc | t2fa3inb & t2fa3inc;

  // Time 3:

  ui107 t3fa0ina, t3fa0inb, t3fa0inc, t5pp0s, t4pp0c;
  t3fa0ina = t3pp0s;
  t3fa0inb = ui107(t3pp1s) << 16;
  t3fa0inc = ui107(t3pp2s) << 34;
  t5pp0s = t3fa0ina ^ t3fa0inb ^ t3fa0inc;
  t4pp0c = t3fa0ina & t3fa0inb | t3fa0ina & t3fa0inc | t3fa0inb & t3fa0inc;

  ui107 t3fa1ina, t3fa1inb, t3fa1inc, t5pp1s, t4pp1c;
  t3fa1ina = t3pp0c;
  t3fa1inb = ui107(t3pp1c) << 16;
  t3fa1inc = ui107(t3pp2c) << 34;
  t5pp1s = t3fa1ina ^ t3fa1inb ^ t3fa1inc;
  t4pp1c = t3fa1ina & t3fa1inb | t3fa1ina & t3fa1inc | t3fa1inb & t3fa1inc;

  ui107 t3fa2ina, t3fa2inb, t3fa2inc, t4pp4s, t4pp2c;
  t3fa2ina = ui103(ia) << 49;
  t3fa2inb = ui103(ib) << 49;
  t3fa2inc = t3pp3c;
  t4pp4s = t3fa2ina ^ t3fa2inb ^ t3fa2inc;
  t4pp2c = t3fa2ina & t3fa2inb | t3fa2ina & t3fa2inc | t3fa2inb & t3fa2inc;

  // Time 4:

  ui109 t4fa0ina, t4fa0inb, t4fa0inc, t6pp0s, t5pp0c;
  t4fa0ina = ui109(t4pp2c) << 2;
  t4fa0inb = t4pp1c;
  t4fa0inc = t4pp0c;
  t6pp0s = t4fa0ina ^ t4fa0inb ^ t4fa0inc;
  t5pp0c = t4fa0ina & t4fa0inb | t4fa0ina & t4fa0inc | t4fa0inb & t4fa0inc;

  ui110 t4fa1ina, t4fa1inb, t4fa1inc, t6pp1s, t5pp1c;
  t4fa1ina = ui106(t4pp4s) << 3;
  t4fa1inb = t4pp0s;
  t4fa1inc = ui110(t4pp1s) << 16;
  t6pp1s = t4fa1ina ^ t4fa1inb ^ t4fa1inc;
  t5pp1c = t4fa1ina & t4fa1inb | t4fa1ina & t4fa1inc | t4fa1inb & t4fa1inc;

  // Time 5:

  ui111 t5fa0ina, t5fa0inb, t5fa0inc, t7pp0s, t6pp0c;
  t5fa0ina = t5pp0s;
  t5fa0inb = t5pp1s;
  t5fa0inc = ui111(t5pp0c) << 2;
  t7pp0s = t5fa0ina ^ t5fa0inb ^ t5fa0inc;
  t6pp0c = t5fa0ina & t5fa0inb | t5fa0ina & t5fa0inc | t5fa0inb & t5fa0inc;

  ui110 t5fa1ina, t5fa1inb, t5fa1inc, t6pp2s, t6pp1c;
  t5fa1ina = ui110(t4pp2s) << 33;
  t5fa1inb = ui110(t4pp3s) << 1;
  t5fa1inc = t5pp1c;
  t6pp2s = t5fa1ina ^ t5fa1inb ^ t5fa1inc;
  t6pp1c = t5fa1ina & t5fa1inb | t5fa1ina & t5fa1inc | t5fa1inb & t5fa1inc;

  // Time 6:

  ui111 t6fa0ina, t6fa0inb, t6fa0inc, t8pp0s, t7pp0c;
  t6fa0ina = ui111(t6pp0s) << 2;
  t6fa0inb = t6pp1s;
  t6fa0inc = ui111(t6pp2s) << 1;
  t8pp0s = t6fa0ina ^ t6fa0inb ^ t6fa0inc;
  t7pp0c = t6fa0ina & t6fa0inb | t6fa0ina & t6fa0inc | t6fa0inb & t6fa0inc;

  // Time 7:

  ui112 t7fa0ina, t7fa0inb, t7fa0inc, t9pp0s, t7pp1c;
  t7fa0ina = t7pp0s;
  t7fa0inb = t7pp0c;
  t7fa0inc = ui112(t6pp0c) << 1;
  t9pp0s = t7fa0ina ^ t7fa0inb ^ t7fa0inc;
  t7pp1c = t7fa0ina & t7fa0inb | t7fa0ina & t7fa0inc | t7fa0inb & t7fa0inc;

// Time 8:

  ui114 t8fa1ina, t8fa1inb, t8fa1inc, t9pp1s, t9pp0c;
  t8fa1ina = ui114(t7pp1c) << 2;
  t8fa1inb = ui114(t6pp1c) << 2;
  t8fa1inc = t8pp0s;
  t9pp1s = t8fa1ina ^ t8fa1inb ^ t8fa1inc;
  t9pp0c = t8fa1ina & t8fa1inb | t8fa1ina & t8fa1inc | t8fa1inb & t8fa1inc;

// Time 9:

  ui115 t9fa1ina, t9fa1inb, t9fa1inc, t11pp0s, t10pp0c;
  t9fa1ina = ui115(t9pp0s) << 1;
  t9fa1inb = t9pp1s;
  t9fa1inc = ui115(t9pp0c) << 1;
  t11pp0s = t9fa1ina ^ t9fa1inb ^ t9fa1inc;
  t10pp0c = t9fa1ina & t9fa1inb | t9fa1ina & t9fa1inc | t9fa1inb & t9fa1inc;

//  ac::probe_map("t11pp0s", t11pp0s);
//  ac::probe_map("t10pp0c", t10pp0c);

  ui115 ppa = t11pp0s;
  ui116 ppb = ui106(t10pp0c) << 1;

//  ac::probe_map("ppa", ppa);
//  ac::probe_map("ppb", ppb);

  return tuple<ui106, ui106> (ppa, ppb);
}

// Booth multiplier:

ui106 computeProduct(ui52 mana, ui52 manb, bool expaZero, bool expbZero) {

  array<ui57, 27> pp; // partial product array
  ui55 multiplier = manb;
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

  ui106 ppa, ppb;
  tie(ppa, ppb) = compress(pp, ia, ib);

  return ppa + ppb;
}

// The design uses an internal exponent format: 12-bit signed integer with bias -1.
 // This function computes the internal representation of a biased 11-bit exponent, with 0 replaced by 1:

 ui12 expInt(ui11 expBiased) {
   ui12 expInt;
   expInt[11] = !expBiased[10];
   expInt[10] = !expBiased[10];
   expInt.set_slc(1, expBiased.slc<9>(1));
   expInt[0] = expBiased[0] || expBiased == 0;
   return expInt;
 }

// Perform right shift if biased sum of exponents is 0 or negative:

tuple<ui12, bool, ui105, bool, bool, bool, bool> rightShft(ui11 expa, ui11 expb, ui106 prod) {

  // Difference between 1 and biased sum of exponents:

  ui10 expDeficit = ~expa + ~expb + 1 + (expa != 0 && expb != 0);

  // If expDeficit >= 64, its value is uninteresting and may be replaced by 63 or 62:

  ui6 shift = expDeficit;
  if (expDeficit.slc<4>(6) != 0) {
    shift.set_slc(1, ui5(31));
  }

  // Shifted product and fraction:

  ui107 prod0 = 0;
  prod0.set_slc(1, prod);
  ui106 prodShft = prod0 >> shift;
  ui105 frac105 = prodShft.slc<105>(0);

  ui12 expShftInt = 0xC00;
  bool expInc = prod[105] && (shift == 1);

  // Rounding bits:

  ui63 stkMaskFMA = 0;
  for (uint i=0; i<shift; i++) {
    stkMaskFMA[i] = 1;
  }
  bool stkFMA = (prod & (stkMaskFMA >> 1)) != 0;

  ui107 stkMask = 0xFFFFFFFFFFFFF;
  stkMask.set_slc(52, stkMaskFMA.slc<55>(0));
  bool stk = (prod & stkMask.slc<106>(1)) != 0;

  ui55 grdMask = ~stkMask.slc<55>(52) & stkMask.slc<55>(51);
  bool grd = (grdMask & prod.slc<55>(51)) != 0;

  ui54 lsbMask = grdMask.slc<54>(0);
  bool lsb = (lsbMask & prod.slc<54>(52)) != 0;

  return tuple<ui12, bool, ui105, bool, bool, bool, bool>(expShftInt, expInc, frac105, stkFMA, lsb, grd, stk);
}

// Perform left shift if leading zero count is positive and exceeded by biased sum of exponents:

tuple<ui12, bool, ui105, bool, bool, bool, bool> leftShft(ui11 expa, ui11 expb, ui106 prod, ui6 clz) {

  // Internal representations of operand exponents:

  ui12 expaInt = expInt(expa), expbInt = expInt(expb);

  // expProdInt - clz:

  ui12 expDiffInt = expaInt + expbInt - clz + 1;

  // expProdInt - 1:

  ui12 expProdM1Int = expaInt + expbInt;

  // Sign of biased sum of exponents:

  bool expDiffBiasedZero = expDiffInt == 0xC00; // expDiffInt == -1024
  bool expDiffBiasedNeg = expDiffInt.slc<2>(10) == 2; // expDiffInt < -1024
  bool expDiffBiasedPos = !expDiffBiasedZero && !expDiffBiasedNeg; // expDiffInt > -1024

  // Shift amount:

  ui6 shift = expDiffBiasedZero ? ui6(clz - 1) : expDiffBiasedPos ? clz : ui6(expProdM1Int);

  // Shifted product and adjusted exponent:

  ui106 prodShft = prod << shift;
  ui12 expShftInt = expDiffBiasedPos ? expDiffInt : ui12(0xC00);

  // Check for multiplication overflow:

  ui64 ovfMask = 0x8000000000000000 >> shift; // ovfMask[63-shift] = 1
  bool mulOvf = (ovfMask & prod.slc<64>(42)) != 0; // prod[105-shift]
  bool sub2Norm = ((ovfMask >> 1) & prod.slc<63>(42)) != 0; // prod[104-shift]

  ui105 frac105 = prodShft.slc<105>(0);
  if (!mulOvf) {
    frac105 <<= 1;
  }

  // Condition for incrementing exponent:

  bool expInc = mulOvf || expDiffBiasedZero && sub2Norm;

  // Rounding bits:

  ui52 stkMask = 0xFFFFFFFFFFFFF >> shift;
  bool stk = mulOvf ? (stkMask & prod) != 0 : ((stkMask >> 1) & prod) != 0;

  ui53 grdMask = ovfMask.slc<53>(11);
  bool grd = mulOvf ? (grdMask & prod) != 0 : ((grdMask >> 1) & prod) != 0;

  ui54 lsbMask = ovfMask.slc<54>(10);
  bool lsb = mulOvf ? (lsbMask & prod) != 0 : ((lsbMask >> 1) & prod) != 0;

  return tuple<ui12, bool, ui105, bool, bool, bool, bool>(expShftInt, expInc, frac105, 0, lsb, grd, stk);
}

// Inputs of fmul64:
//   opa[63:0], opb[63:0]: sign 63, exponent 62:52, mantissa 51:0
//   fz: force denormals to 0
//   dn: replace NaN operand with default
//   mode[1:0]: encoding of rounding mode
//   fused: boolean indication of FMA rather than FMUL

// Outputs of fmul64:
//   D[116:0]: For FMUL, data result is D[63:0]; for FMA, sign 116, exponent 115:105, mantissa 104:0
//   flags[7:0]: exception flags
//   prodInfZero: product of infinity and zero (valid for FMA only)
//   infNanZero: result is infinity, NaN, or zero (valid for FMA only)
//   expOvfl: implicit exponent bit 11 (valid for FMA when infNanZero = 0)

tuple<ui117, ui8, bool, bool, bool> fmul64(ui64 opa, ui64 opb, bool fz, bool dn, ui2 rmode, bool fused) {

  // Analyze operands and process special cases:

  bool signa, signb;    // operand signs
  ui11 expa, expb;      // operand exponents
  ui52 mana, manb;      // operand mantissas
  Class classa, classb; // operand classes
  ui8 flags = 0;        // exception flags
  tie(signa, expa, mana, classa, flags) = analyze(opa, DP, fz, flags);
  tie(signb, expb, manb, classb, flags) = analyze(opb, DP, fz, flags);

  // Detect early exit:

  if (classa == ZERO || classa == INF || classa == SNAN || classa == QNAN ||
      classb == ZERO || classb == INF || classb == SNAN || classb == QNAN) {
    return specialCase(opa, opb, classa, classb, dn, fused, flags);
  }

  else {

    // Leading zero count:

    ui6 clz = 0;
    if (expa == 0) {
      clz |= CLZ53(mana);
    }
    if (expb == 0) {
      clz |= CLZ53(manb);
    }

    // Product of significands:

    ui106 prod = computeProduct(mana, manb, expa == 0, expb == 0);

    // Internal representation of sum of operand exponents:

    ui12 expProdInt = expInt(expa) + expInt(expb) + 1;

    // Biased sum of exponents is 0, negative:

    bool expBiasedZero = expProdInt == 0xC00; // signed value of expProdInt == -1024;
    bool expBiasedNeg = expProdInt.slc<2>(10) == 2; // signed value of expProdInt < -1024;

    // If biased sum is 0 or negative, a right  shift is required.
    // Otherwise, a left shift (possibly 0) is performed.
    // Iin both cases, we compute the following quantities:

    ui12 expShftInt;     // expShftInt + expInc is internal representation of exponent of shifted product
    bool expInc;
    ui105 frac105;       // fraction to be returned for FMA
    bool stkFMA;         // sticky bit for FMA
    bool lsb, grd, stk;  // lsb, guard, and sticky bits for FMUL

    if (expBiasedZero || expBiasedNeg) {
      tie(expShftInt, expInc, frac105, stkFMA, lsb, grd, stk) = rightShft(expa, expb, prod);
    }
    else {
      tie(expShftInt, expInc, frac105, stkFMA, lsb, grd, stk) = leftShft(expa, expb, prod, clz);
    }

    // Important values of (pre-increment) exponent:

    bool expZero = expShftInt.slc<12>(0) == 0xC00;
    bool expMax = expShftInt.slc<12>(0) == 0x3FE;
    bool expInf = expShftInt.slc<12>(0) == 0x3FF;
    bool expGTinf = expShftInt.slc<2>(10) == 1;

    // Convert exponent to biased form:

    ui11 exp11 = expShftInt;
    exp11[10] = !exp11[10];

    // Sign of product:

    bool sign = signa ^ signb;

    if (fused) { // FMA case

      ui117 D;
      D[116] = sign;
      if (expInc && !expInf) {
        D.set_slc(105, ui11(exp11+1));
      }
      else {
        D.set_slc(105, exp11);
      }
      D.set_slc(0, frac105);
      flags[IXC] = stkFMA;
      bool prodInfZero = false, infNanZero = false;
      bool expOvfl = expGTinf || expInf && expInc;
      return tuple<ui117, ui8, bool, bool, bool>(D, flags, prodInfZero, infNanZero, expOvfl);
    }

    else { // FMUL case

      ui64 D = 0;
      D[63] = sign;

      bool rndUp = rmode == rmodeNear && grd && (lsb || stk) ||
                   rmode == rmodeUP && !sign && (grd || stk) ||
                   rmode == rmodeDN && sign && (grd || stk);

      ui52 fracUnrnd = frac105.slc<52>(53);
      ui53 fracP1 = fracUnrnd + 1;
      ui52 fracRnd = rndUp ? fracP1.slc<52>(0) : fracUnrnd;

      bool expRndInc = rndUp && fracP1[52];
      ui11 expRnd = expInc || expRndInc ? ui11(exp11 + 1) : exp11;

      bool underflow = expZero && !expInc;
      bool overflow = expGTinf || expInf || expMax && (expInc || expRndInc);

      if (overflow) {
        flags[IXC] = 1;
        flags[OFC] = 1;
        if (rmode == rmodeUP && sign || rmode == rmodeDN && !sign || rmode == rmodeZero) {
          D.set_slc(0, ui63(0x7FEFFFFFFFFFFFFF));
        }
        else {
          D.set_slc(0, ui63(0x7FF0000000000000));
        }
      }
      else if (underflow) {
        if (fz) {
          flags[UFC] = 1;
        }
        else {
          if (grd || stk) {
            flags[UFC] = 1;
            flags[IXC] = 1;
          }
          D.set_slc(0, fracRnd);
          D.set_slc(52, expRnd);
        }
      }
      else {
        if (grd || stk) {
          flags[IXC] = 1;
        }
        D.set_slc(0, fracRnd);
        D.set_slc(52, expRnd);
     }
      return tuple<ui117, ui8, bool, bool, bool>(D, flags, false, false, false);
    }
  }
}

// RAC end

#ifdef SLEC

SC_MODULE(fmul64) {

  sc_in_clk    clk;
  sc_in<bool>  reset;
  sc_in<bool>  fused;
  sc_in<bool>  fz;
  sc_in<bool>  dn;
  sc_in<ui2>   rmode;
  sc_in<ui64>  opa;
  sc_in<ui64>  opb;

  sc_out<ui64> D;
  sc_out<ui5>  flags;
  sc_out<ui117> DFMA;
  sc_out<ui5>  flagsFMA;
  sc_out<bool> prodInfZero;
  sc_out<bool> infNanZero;
  sc_out<bool> expOvfl;

  void doit() {

    if (reset.read()) {
      return;
    }

    fused.read();
    fz.read();
    dn.read();
    rmode.read();
    opa.read();
    opb.read();

    ui117 data;
    ui8 excps;
    bool piz, inz, egti;
    tie(data, excps, piz, inz, egti) = fmul64(opa, opb, fz, dn, rmode, fused);

    // Contract excps to 5 bits to match RTL:
    ui5 excps5;
    excps5[0] = excps[0];
    excps5[1] = excps[2];
    excps5[2] = excps[3];
    excps5[3] = excps[4];
    excps5[4] = excps[7];

    // Extract low 64 bits of data:
    ui64 data64 = data;

    D.write(data64);
    flags.write(excps5);

    DFMA.write(data);
    flagsFMA.write(excps5);
    prodInfZero.write(piz);
    infNanZero.write(inz);
    expOvfl.write(egti);

  }

  SC_CTOR(fmul64) {
    SC_METHOD(doit);
    sensitive_pos << clk;
  }

};

#else

int main() {

ui64 opa = 0x000800000000000;
ui64 opb = 0x0010000000000000;
ui2 rmode = 0;
bool dn = 1, fz = 0, fused = 0;

ui117 D;
ui8 flags;
bool prodInfZero, infNanZero, expOvfl;
tie(D, flags, prodInfZero, infNanZero, expOvfl) = fmul64(opa, opb, fz, dn, rmode, fused);

printf("opa = %s\n", opa.to_string(AC_HEX, false).c_str());
printf("opb = %s\n", opb.to_string(AC_HEX, false).c_str());
printf("D = %s\n", D.to_string(AC_HEX, false).c_str());
printf("flags = %s\n", flags.to_string(AC_HEX, false).c_str());

 return 0;
}

#endif

