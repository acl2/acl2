extern double foo(int x, int y) {
  return 0;
}
static double wrapper_foo(int x, int y) {
  return foo(x, y);
}
int main(void) {
  int (*foo)(double, double) = 0;
  return foo(0.0, 1.0);
}
