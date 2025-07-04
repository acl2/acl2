int nosimp_int(int x) {
  int x1 = +x;
  int x2 = -x;
  int x3 = ~x;
  int x4 = !x;
  return x1 + x2 + x3 + x4;
}

int nosimp_short(short x) {
  int x1 = +x;
  int x2 = -x;
  int x3 = ~x;
  int x4 = !x;
  return x1 + x2 + x3 + x4;
}

unsigned long nosimp_ulong(unsigned long x) {
  unsigned long x1 = +x;
  unsigned long x2 = -x;
  unsigned long x3 = ~x;
  unsigned long x4 = !x;
  return x1 + x2 + x3 + x4;
}

int var(int x) {
  return x + 0;
}

int constant() {
  return 17 + 0;
}

int bin(int x, int y) {
  return (x + y) + 0;
}

int nonint_param(int a, unsigned long b) {
  return a + 0;
}

long nonint_return(long x) {
  return x;
}

int decl() {
  int x = 5;
  return x + 0;
}

int noninteger() {
  float y = 5.0f;
  return y + 0;
}

int gg(int y) {
  int z = (y + 0);
  return z;
}

int paren() {
  int w = 1;
  int u = ((w + 0));
  return 0;
}

void nonint_const() {
  long long ll = 34LL;
}

int ternary_int(int x, int y, int z) {
  return x ? y : z;
}

long cast_int_to_long(int x) {
  return (long) x;
}

int cast_long_to_int(long x) {
  return (int) x;
}

void return_void() {
  return;
}

void asg_int(int x, int y) {
  x = 5;
  x = y + 0;
}

int main() {
  return 0;
}
