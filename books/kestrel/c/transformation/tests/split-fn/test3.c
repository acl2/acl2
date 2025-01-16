int w = 42;

int foo(int x) {
  long y = 0, z = 5;
  y = bar(x);
  return x + y + z;
}
