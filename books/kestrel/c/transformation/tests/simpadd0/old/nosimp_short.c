int nosimp_short(short x) {
  int x1 = +x;
  int x2 = -x;
  int x3 = ~x;
  int x4 = !x;
  return x1 + x2 + x3 + x4;
}
