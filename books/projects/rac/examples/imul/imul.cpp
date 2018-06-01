// Simple Rac example: integer multiplication

#include <systemc.h>
#include <rac.h>

using namespace std;

// Rac begin

// This Rac code describes a 32x32 -> 64 unsigned integer multiplier
// Adapted from significand_multiplier_r4_param in Warren Ferguson's
// library of Verilog reference models.

typedef sc_uint<32> ui32;
typedef sc_uint<64> ui64;
typedef sc_uint<35> ui35;
typedef sc_uint<3>  ui3; 
typedef sc_biguint<33> ui33;
typedef sc_biguint<67> ui67;

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

array<ui3, 17> Booth (ui32 x) {

  // Pad the multiplier with 2 leading zeroes and 1 trailing zero:
  ui35 x35 = x << 1;

  // Compute the booth encodings:
  array<ui3, 17> a;
  for (int k=0; k<17; k++) {
    a[k] = Encode(x35.range(2*k+2, 2*k));
  }
  return a;
}

// Step 2: Form the partial products.

array<ui33, 17> PartialProducts (array<ui3, 17> m21, ui32 y) {
  array<ui33, 17> pp;

  for (int k=0; k<17; k++) {
    ui33 row;
    switch (m21[k].range(1,0).to_uint()) {
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
    tmp.range(2*k+32, 2*k) = pps[k];
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

    tble[k] = tmp.range(63, 0);
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

//   cout << "Operands: << endl;
//   cout << hex << s1 << endl;
//   cout << hex << s1 << endl;

  array<ui3, 17> bd = Booth(s1);

//   cout << "Booth digits:" << endl;
//   for (int i=0; i<17; i++) {
//     cout << i << ": " << bds[i][2] << bds[i][1] << bds[i][0] << endl;
//   }

  array<ui33, 17> pp = PartialProducts(bd, s2);

//   cout << "Partial products:" << endl;
//   for (int i=0; i<17; i++) {
//     cout << i << ": " << hex << pps[i] << endl;
//   }

  array<ui64, 17> tble = Align (bd, pp);

#ifdef HECTOR
  Hector::cutpoint("tble", tble);
#endif

//   cout << "Aligned partial products:" << endl;
//   for (int i=0; i<17; i++) {
//     cout << i << ": " << hex << tble[i] << endl;
//   }

  ui64 prod = Sum(tble);

//   cout << "Product: << endl;
//   cout << hex << prod << endl;

  return prod;

}

tuple<bool, ui64, ui64>ImulTest(ui32 s1, ui32 s2) {
  ui64 spec_result = s1 * s2;
  ui64 imul_result = Imul(s1, s2);
  return tuple<bool, ui64, ui64>(spec_result == imul_result, spec_result, imul_result);
}  

// Rac end

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

int sc_main (int argc, char *argv[]) {

  ui32 src1;
  ui32 src2;
  ui64 spec_result;
  ui64 imul_result;
  bool passed;

  while (! cin.eof()) {

    cin >> src1;
    cin >> src2;

    tie(passed, spec_result, imul_result) = ImulTest(src1, src2);

    cout << src1.to_uint() << " " << src2.to_uint() << " " << imul_result.to_uint() << " ";
    if (passed) {
      cout << "passed";
    } else {
      cout << "failed (spec: " << spec_result.to_uint() << "; imul: " << imul_result.to_uint() << ")";
    }
    cout << endl;
  }

}

#endif
