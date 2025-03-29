int f() {
  int x = 5;
  return x + 0;
}

int g(int y) {
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

int main() {
  int a = f();
  int b = g(a);
  return a + b;
}
