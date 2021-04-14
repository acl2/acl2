#include <stdio.h>

void f_test(int x, int y) {
  int r = f(x, y);
  printf("f(%d, %d) = %d\n", x, y, r);
}

void g_test(int x, int y) {
  int r = g(x, y);
  printf("g(%d, %d) = %d\n", x, y, r);
}

void h_test(int x, int y) {
  int r = h(x, y);
  printf("h(%d, %d) = %d\n", x, y, r);
}

int main(void) {
  f_test(3, -2);
  g_test(15, 33);
  h_test(1, 2);
}
