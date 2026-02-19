typedef int my_fn_t(int y, int z);

my_fn_t foo, bar, baz;

int bar(int y, int z) {
  int x = 5;
  return x + y - z;
}
