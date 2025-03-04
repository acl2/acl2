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
}

int main() {
  int a = f();
  int b = g(a);
  return a + b;
}
