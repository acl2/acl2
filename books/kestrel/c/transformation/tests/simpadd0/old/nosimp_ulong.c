unsigned long nosimp_ulong(unsigned long x) {
  unsigned long x1 = +x;
  unsigned long x2 = -x;
  unsigned long x3 = ~x;
  unsigned long x4 = !x;
  return x1 + x2 + x3 + x4;
}
