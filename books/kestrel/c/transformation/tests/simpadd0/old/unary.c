int f(int x) {
  return !x;
}

int g(int x) {
  return ~(x = 3);
}

int h(int x) {
  return -(x + 0);
}

int unary_on_int(int x) {
  int x1 = +x;
  int x2 = -x;
  int x3 = ~x;
  int x4 = !x;
  return x1 + x2 + x3 + x4;
}

int unary_on_short(short x) {
  int x1 = +x;
  int x2 = -x;
  int x3 = ~x;
  int x4 = !x;
  return x1 + x2 + x3 + x4;
}

unsigned long unary_on_ulong(unsigned long x) {
  unsigned long x1 = +x;
  unsigned long x2 = -x;
  unsigned long x3 = ~x;
  unsigned long x4 = !x;
  return x1 + x2 + x3 + x4;
}
