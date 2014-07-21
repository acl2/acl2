


ui3 Encode(ui3 slice) {
  ui3 enc;
  switch (slice) {
  case 4:
    enc = 6;
    break;
  case 5:
  case 6:
    enc = 5;
    break;
  case 7:
  case 0:
    enc = 0;
    break;
  case 1:
  case 2:
    enc = 1;
    break;
  case 3:
    enc = 2;
    break;
  default:
    assert(false);
  }
  return enc;
}

ui3[17] Booth(ui32 x) {
  ui35 x35 = x << 1;
  ui3 a[17];
  for (int k = 0; k < 17; k++) {
    a[k] = Encode(x35[2 * k + 2:2 * k]);
  }
  return a;
}

ui33[17] PartialProducts(ui3 m21[17], ui32 y) {
  ui33 pp[17];
  for (int k = 0; k < 17; k++) {
    ui33 row;
    switch (m21[k][1:0]) {
    case 2:
      row = y << 1;
      break;
    case 1:
      row = y;
      break;
    default:
      row = 0;
    }
    pp[k] = m21[k][2] ? ~row : row;
  }
  return pp;
}

ui64[17] Align(ui3 bds[17], ui33 pps[17]) {
  ui64 tble[17];
  bool sb[17];
  bool psb[18];
  ui67 tmp;
  for (int k = 0; k < 17; k++) {
    sb[k] = bds[k][2];
    psb[k + 1] = bds[k][2];
  }
  for (int k = 0; k < 17; k++) {
    tmp = 0;
    tmp[2 * k + 32:2 * k] = pps[k];
    if (k == 0) {
      tmp[33] = sb[k];
      tmp[34] = sb[k];
      tmp[35] = !sb[k];
    }
    else  {
      tmp[2 * k - 2] = psb[k];
      tmp[2 * k + 33] = !sb[k];
      tmp[2 * k + 34] = 1;
    }
    tble[k] = tmp[63:0];
  }
  return tble;
}

<ui64, ui64> Compress32(ui64 in0, ui64 in1, ui64 in2) {
  ui64 out0 = in0 ^ in1 ^ in2;
  ui64 out1 = in0 & in1 | in0 & in2 | in1 & in2;
  out1 <<= 1;
  return <out0, out1>;
}

<ui64, ui64> Compress42(ui64 in0, ui64 in1, ui64 in2, ui64 in3) {
  ui64 temp = (in1 & in2 | in1 & in3 | in2 & in3) << 1;
  ui64 out0 = in0 ^ in1 ^ in2 ^ in3 ^ temp;
  ui64 out1 = (in0 & ~(in0 ^ in1 ^ in2 ^ in3)) | (temp & (in0 ^ in1 ^ in2 ^ in3));
  out1 <<= 1;
  return <out0, out1>;
}

ui64 Sum(ui64 in[17]) {
  ui64 level1[8];
  for (uint i = 0; i < 4; i++) {
    <level1[2 * i + 0], level1[2 * i + 1]> = Compress42(in[4 * i], in[4 * i + 1], in[4 * i + 2], in[4 * i + 3]);
  }
  ui64 level2[4];
  for (uint i = 0; i < 2; i++) {
    <level2[2 * i + 0], level2[2 * i + 1]> = Compress42(level1[4 * i], level1[4 * i + 1], level1[4 * i + 2], level1[4 * i + 3]);
  }
  ui64 level3[2];
  <level3[0], level3[1]> = Compress42(level2[0], level2[1], level2[2], level2[3]);
  ui64 level4[2];
  <level4[0], level4[1]> = Compress32(level3[0], level3[1], in[16]);
  return level4[0] + level4[1];
}

ui64 Imul(ui32 s1, ui32 s2) {
  ui3 bd[17] = Booth(s1);
  ui33 pp[17] = PartialProducts(bd, s2);
  ui64 tble[17] = Align(bd, pp);
  ui64 prod = Sum(tble);
  return prod;
}

<bool, ui64, ui64> ImulTest(ui32 s1, ui32 s2) {
  ui64 spec_result = s1 * s2;
  ui64 imul_result = Imul(s1, s2);
  return <spec_result == imul_result, spec_result, imul_result>;
}

