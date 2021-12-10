#include <stdio.h>

void f_test(int x, int y, int z) {
  int r = f(x, y, z);
  printf("f(%d, %d, %d) = %d\n", x, y, z, r);
}

void g_test(int e) {
  int r = g(e);
  printf("g(%d) = %d\n", e, r);
}

void h_test(int x, int y) {
  int r = h(x, y);
  printf("h(%d, %d) = %d\n", x, y, r);
}

void i_test(int x) {
  int r = i(x);
  printf("i(%d) = %d\n", x, r);
}

void j_test(int a, int b) {
  int r = j(a, b);
  printf("j(%d, %d) = %d\n", a, b, r);
}

int main(void) {
  f_test(11, 8888, -220);
  f_test(0, 888, -220);
  g_test(67);
  g_test(80000);
  h_test(1700, 3);
  h_test(1700, -99);
  i_test(20000);
  i_test(23);
  i_test(-667);
  j_test(2728, -1);
  j_test(0, 0);
  return 0;
}
