#include <stdio.h>

void f_test(int x, int y) {
  int r = f(x, y);
  printf("f(%d, %d) = %d\n", x, y, r);
}

void g_test(int z) {
  int r = g(z);
  printf("f(%d) = %d\n", z, r);
}

void h_test(int a, int b) {
  int r = h(a, b);
  printf("h(%d, %d) = %d\n", a, b, r);
}

int main(void) {
  f_test(16,-373);
  f_test(0, 0);
  g_test(63);
  g_test(-1);
  h_test(2, 78);
  h_test(-3, 0);
  return 0;
}
