#include <stdio.h>

void test_f() {
  int x = 7733;
  int y = -939;
  int r = f(x, y);
  printf("f(%d, %d) = %d\n", x, y, r);
}

void test_g() {
  int x = 737838;
  int y = -1;
  int z = -4400;
  int r = g(x, y, z);
  printf("f(%d, %d, %d) = %d\n", x, y, z, r);
}

int main(void) {
  test_f();
  test_g();
}
