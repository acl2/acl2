extern double foo(int x, int y);
static double wrapper_foo(int x, int y) {
  return foo(x, y);
}
int main(void) {
  wrapper_foo(0, 1);
}
