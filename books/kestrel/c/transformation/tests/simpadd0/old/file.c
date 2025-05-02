int f(int x, int y) {
  return (x + y) + 0;
}

int g(int a, unsigned long b) {
  return a + 0;
}

int main() {
  int x = 5;
  return x + 0;
}

int ff(int x) {
  return x + 0;
}

int main1() {
  float y = 5.0f;
  return y + 0;
}

int fff() {
  int x = 5;
  return x + 0;
}

int gg(int y) {
  int z = (y + 0);
  return z;
}

int h() {
  int w = 1;
  int u = ((w + 0));
  return 0;
}

int i(int x) {
  int x1 = +x;
  int x2 = -x;
  int x3 = ~x;
  int x4 = !x;
  return x1 + x2 + x3 + x4;
}

int main2() {
  int a = f();
  int b = g(a);
  return a + b;
}
