int w = 42;
int baz(int x, long y, long z) {
  y = bar(x);
  return x + y + z;
}
int foo(int x) {
  long y = 0, z = 5;
  return baz(x, y, z);
}
