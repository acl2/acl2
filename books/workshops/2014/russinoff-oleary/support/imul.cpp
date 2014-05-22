// Simple Masc example: integer multiplication
// John O'Leary, 28 May 2013

#include <systemc.h>
#include <masc.h>

// Masc begin

// This Masc code describes a 32x32 -> 64 unsigned integer multiplier
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

array<17, ui3> Booth (ui32 x) {

  // Pad the multiplier with 2 leading zeroes and 1 trailing zero:
  ui35 x35 = x << 1;

  // Compute the booth encodings:
  array<17, ui3> a;
  for (int k=0; k<17; k++) {
    a.elt[k] = Encode(x35.range(2*k+2, 2*k));
  }
  return a;
}

// Step 2: Form the partial products.

array<17, ui33> PartialProducts (array<17, ui3> m21, ui32 y) {
  array<17, ui33> pp;

  for (int k=0; k<17; k++) {
    ui33 row;
    switch (m21.elt[k].range(1,0).to_uint()) {
    case 2:
      row = y << 1;
      break;
    case 1:
      row = y;
      break;
    default:
      row = 0;
    }
    pp.elt[k] = m21.elt[k][2] ? ~row : row;
  }

  return pp;
}

// Step 3: Construct the table of aligned partial products.

array<17, ui64> Align(array<17, ui3> bds, array<17, ui33> pps) {

  // Extract the sign bits from the booth encodings:
  array<17, bool> sb;
  array<18, bool> psb;
  for (int k=0; k<17; k++) {
    sb.elt[k] = bds.elt[k][2];
    psb.elt[k+1] = bds.elt[k][2];
  }

  // Build the table:
  array<17, ui64> tble;
  for (int k=0; k<17; k++) {
    ui67 tmp = 0;
    tmp.range(2*k+32, 2*k) = pps.elt[k];
    if (k == 0) {
      tmp[33] =  sb.elt[k];
      tmp[34] =  sb.elt[k];
      tmp[35] =  !sb.elt[k];
    }
    else {
      tmp[2*k-2] = psb.elt[k];
      tmp[2*k+33] = !sb.elt[k];
      tmp[2*k+34] = 1;
    }

    tble.elt[k] = tmp.range(63, 0);
  }

  return tble;
}

// Step 4: Sum the rows of the table of aligned partial products

// The compression tree is constucted from two basic modules:

mv<ui64, ui64> Compress32(ui64 in0, ui64 in1, ui64 in2) {
  ui64 out0 = in0 ^ in1 ^ in2;
  ui64 out1 = in0 & in1 | in0 &in2 | in1 & in2;
  out1 <<= 1;
  return mv<ui64, ui64>(out0, out1);
}

mv<ui64, ui64> Compress42(ui64 in0, ui64 in1, ui64 in2, ui64 in3) {
  ui64 temp = (in1 & in2 | in1 & in3 | in2 & in3) << 1;
  ui64 out0 = in0 ^ in1 ^ in2 ^ in3 ^ temp;
  ui64 out1 = (in0 & ~(in0 ^ in1 ^ in2 ^ in3)) | (temp & (in0 ^ in1 ^ in2 ^ in3));
  out1 <<= 1;
  return mv<ui64, ui64>(out0, out1);
}

ui64 Sum(array<17, ui64> in) {

  // level 1 consists of 4 4:2 compressors
  array<8, ui64> A1;
  for (uint i=0; i<4; i++) {
    Compress42(in.elt[4*i], in.elt[4*i+1], in.elt[4*i+2], in.elt[4*i+3]).assign(A1.elt[2*i+0], A1.elt[2*i+1]);
  }

  // level 2 consists of 2 4:2 compressors
  array<4, ui64> A2;
  for (uint i=0; i<2; i++) {
    Compress42(A1.elt[4*i], A1.elt[4*i+1], A1.elt[4*i+2], A1.elt[4*i+3]).assign(A2.elt[2*i+0], A2.elt[2*i+1]);
  }

  // level 3 consists of 1 4:2 compressor
  array<2, ui64> A3;
  Compress42(A2.elt[0], A2.elt[1], A2.elt[2], A2.elt[3]).assign(A3.elt[0], A3.elt[1]);

  // level 4 consists of 1 3:2 compressor
  array<2, ui64> A4;
  Compress32(A3.elt[0], A3.elt[1], in.elt[16]).assign(A4.elt[0], A4.elt[1]);

  // The final sum:
  return A4.elt[0] + A4.elt[1];
}
  
// Stitch it together

ui64 Imul(ui32 s1, ui32 s2) {

//   cout << "Operands: << endl;
//   cout << hex << s1 << endl;
//   cout << hex << s1 << endl;

  array<17, ui3> bd = Booth(s1);

//   cout << "Booth digits:" << endl;
//   for (int i=0; i<17; i++) {
//     cout << i << ": " << bds.elt[i][2] << bds.elt[i][1] << bds.elt[i][0] << endl;
//   }

  array<17, ui33> pp = PartialProducts(bd, s2);

//   cout << "Partial products:" << endl;
//   for (int i=0; i<17; i++) {
//     cout << i << ": " << hex << pps.elt[i] << endl;
//   }

  array<17, ui64> tble = Align (bd, pp);

//   cout << "Aligned partial products:" << endl;
//   for (int i=0; i<17; i++) {
//     cout << i << ": " << hex << tble.elt[i] << endl;
//   }

  ui64 prod = Sum(tble);

//   cout << "Product: << endl;
//   cout << hex << prod << endl;

  return prod;

}

mv<bool, ui64, ui64>ImulTest(ui32 s1, ui32 s2) {
  ui64 spec_result = s1 * s2;
  ui64 imul_result = Imul(s1, s2);
  return mv<bool, ui64, ui64>(spec_result == imul_result, spec_result, imul_result);
}  

// Masc end

int sc_main (int argc, char *argv[]) {

  ui32 src1;
  ui32 src2;
  ui64 spec_result;
  ui64 imul_result;
  bool passed;

  while (! cin.eof()) {

    cin >> src1;
    cin >> src2;

    ImulTest(src1, src2).assign(passed, spec_result, imul_result);

    cout << src1 << " " << src2 << " " << imul_result << " ";
    if (passed) {
      cout << "passed";
    } else {
      cout << "failed (spec: " << spec_result << "; imul: " << imul_result << ")";
    }
    cout << endl;
  }

}

