// Simple RAC example: integer multiplication

//#define DEBUG

#include <stdio.h>
#include <iostream>
#include <ac_int.h>
#include <rac.h>
using namespace std;

// RAC begin

// This RAC code describes a 32x32 -> 64 unsigned integer multiplier.
// Adapted from significand_multiplier_r4_param in Warren Ferguson's
// library of Verilog reference models.

typedef ac_int<32,false> ui32;
typedef ac_int<64,false> ui64;
typedef ac_int<35,false> ui35;
typedef ac_int<3,false>  ui3; 
typedef ac_int<33,false> ui33;
typedef ac_int<67,false> ui67;

// Step 1: construct an array of radix-4 digits for a source multiplier.

// For each 3-bit slice x[2*k+1:2*k-1] of the multiplier, we compute a
// 3-bit sign-magnitude encoding of x[2*k-1] + x[2*k] - 2 * x[2*k+1]:

ui3 Encode(ui3 slice) {
  ui3 enc;
  switch (slice) {
  case 4:
    enc = 6; // -2 -> 110
    break;
  case 5: case 6:
    enc = 5; // -1 -> 101
    break;
  case 7: case 0:
    enc = 0; //  0 -> 000
    break;
  case 1: case 2:
    enc = 1; // +1 -> 001
    break;
  case 3:
    enc = 2; // +2 -> 010
    break;
  default: 
    assert(false);
  }
  return enc;
}

array<ui3, 17> Booth (ui35 x) {

  // Pad the multiplier with 2 leading zeroes and 1 trailing zero:
  ui35 x35 = x << 1;

  // Compute the booth encodings:
  array<ui3, 17> a;
  for (int k=0; k<17; k++) {
    a[k] = Encode(x35.slc<3>(2*k));
  }
  return a;
}

// Step 2: Form the partial products.

array<ui33, 17> PartialProducts (array<ui3, 17> m21, ui33 y) {
  array<ui33, 17> pp;

  for (int k=0; k<17; k++) {
    ui33 row;
    switch (m21[k].slc<2>(0)) {
    case 2:
      row = y << 1;
      break;
    case 1:
      row = y;
      break;
    default:
      row = 0;
    }
    pp[k] = m21[k][2] ? (ui33)~row : row;
  }

  return pp;
}

// Step 3: Construct the table of aligned partial products.

array<ui64, 17> Align(array<ui3, 17> bds, array<ui33, 17> pps) {

  // Extract the sign bits from the booth encodings:
  array<bool, 17> sb;
  array<bool, 18> psb;
  for (int k=0; k<17; k++) {
    sb[k] = bds[k][2];
    psb[k+1] = bds[k][2];
  }

  // Build the table:
  array<ui64, 17> tble;
  for (int k=0; k<17; k++) {
    ui67 tmp = 0;
    tmp.set_slc(2*k, pps[k]);
    if (k == 0) {
      tmp[33] =  sb[k];
      tmp[34] =  sb[k];
      tmp[35] =  !sb[k];
    }
    else {
      tmp[2*k-2] = psb[k];
      tmp[2*k+33] = !sb[k];
      tmp[2*k+34] = 1;
    }

    tble[k] = tmp;
  }

  return tble;
}

// Step 4: Sum the rows of the table of aligned partial products

// The compression tree is constucted from two basic modules:

tuple<ui64, ui64> Compress32(ui64 in0, ui64 in1, ui64 in2) {
  ui64 out0 = in0 ^ in1 ^ in2;
  ui64 out1 = in0 & in1 | in0 &in2 | in1 & in2;
  out1 <<= 1;
  return tuple<ui64, ui64>(out0, out1);
}

tuple<ui64, ui64> Compress42(ui64 in0, ui64 in1, ui64 in2, ui64 in3) {
  ui64 temp = (in1 & in2 | in1 & in3 | in2 & in3) << 1;
  ui64 out0 = in0 ^ in1 ^ in2 ^ in3 ^ temp;
  ui64 out1 = (in0 & ~(in0 ^ in1 ^ in2 ^ in3)) | (temp & (in0 ^ in1 ^ in2 ^ in3));
  out1 <<= 1;
  return tuple<ui64, ui64>(out0, out1);
}

ui64 Sum(array<ui64, 17> in) {

  // level 1 consists of 4 4:2 compressors
  array<ui64, 8> A1;
  for (uint i=0; i<4; i++) {
    tie(A1[2*i+0], A1[2*i+1]) = Compress42(in[4*i], in[4*i+1], in[4*i+2], in[4*i+3]);
  }

  // level 2 consists of 2 4:2 compressors
  array<ui64, 4> A2;
  for (uint i=0; i<2; i++) {
    tie(A2[2*i+0], A2[2*i+1]) = Compress42(A1[4*i], A1[4*i+1], A1[4*i+2], A1[4*i+3]);
  }

  // level 3 consists of 1 4:2 compressor
  array<ui64, 2> A3;
  tie(A3[0], A3[1]) = Compress42(A2[0], A2[1], A2[2], A2[3]);

  // level 4 consists of 1 3:2 compressor
  array<ui64, 2> A4;
  tie(A4[0], A4[1]) = Compress32(A3[0], A3[1], in[16]);

  // The final sum:
  return A4[0] + A4[1];
}
  
// Stitch it together

ui64 Imul(ui32 s1, ui32 s2) {

#ifdef DEBUG
   cout << "Operands: " << endl;
   printf("%s\n", s1.to_string(AC_HEX, false).c_str());
   printf("%s\n", s2.to_string(AC_HEX, false).c_str());
#endif

  array<ui3, 17> bd = Booth(s1);

#ifdef DEBUG
   cout << "Booth digits: " << endl;
   for (int i=0; i<17; i++) {
     printf("%d: %s\n", i, bd[i].to_string(AC_HEX, false).c_str());
   }
#endif

  array<ui33, 17> pp = PartialProducts(bd, s2);

#ifdef DEBUG
   cout << "Partial products:" << endl;
   for (int i=0; i<17; i++) {
     printf("%d: %s\n", i, pp[i].to_string(AC_HEX, false).c_str());
   }
#endif

  array<ui64, 17> tble = Align (bd, pp);

#ifdef HECTOR
  Hector::cutpoint("tble", tble);
#endif

#ifdef DEBUG
   cout << "Aligned partial products:" << endl;
   for (int i=0; i<17; i++) {
     printf("%d: %s\n", i, tble[i].to_string(AC_HEX, false).c_str());
   }
#endif

  ui64 prod = Sum(tble);

#ifdef DEBUG
   printf("Product: %s\n\n", prod.to_string(AC_HEX, false).c_str());
#endif

  return prod;

}

tuple<bool, ui64, ui64>ImulTest(ui32 s1, ui32 s2) {
  ui64 spec_result = s1 * s2;
  ui64 imul_result = Imul(s1, s2);
  return tuple<bool, ui64, ui64>(spec_result == imul_result, spec_result, imul_result);
}  

// RAC end

#ifdef HECTOR

void hectorWrapper() {

  ui32 x, y;
  ui64 prod;

  Hector::registerInput("x", x);
  Hector::registerInput("y", y);
  Hector::registerOutput("prod", prod);

  Hector::beginCapture();

  prod = Imul(x, y); 

  Hector::endCapture();

}

#else
#ifdef SLEC

SC_MODULE(imul) {

  sc_in<ui32> x;
  sc_in<ui32>y;

  sc_out<ui64> prod;

  void doit() {

    x.read();
    y.read();
    
    ui32 xval = x, yval = y;
    ui64 prodval = Imul(xval, yval);

    prod.write(prodval);
  }

  SC_CTOR(imul) {
    SC_METHOD(doit);  
  }

};

#else

int main (int argc, char *argv[]) {

  ui32 src1, src2;
  ui64 spec_result, imul_result;
  bool passed;
  uint in1, in2;

  while (! cin.eof()) {

    // On each iteration of this loop, two 32-bit integers are read in and passed to Imul. 

    cin >> hex >> in1;
    cin >> hex >> in2;
    src1 = in1;
    src2 = in2;

    tie(passed, spec_result, imul_result) = ImulTest(src1, src2);

    printf("Spec: %s\n", spec_result.to_string(AC_HEX, false).c_str());
    printf("Imul: %s\n", imul_result.to_string(AC_HEX, false).c_str());

    if (passed) {
      cout << "passed" << endl;
    }
    else {
      cout << "failed" << endl;
    }
  }

}

#endif
#endif
