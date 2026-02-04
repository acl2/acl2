int foo(int y, int z);

__attribute__((noinline))
int foo(int y, int z) {
  int x = 5;
  return x + y - z;
}
