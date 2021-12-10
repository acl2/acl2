#include <stdio.h>

void f_test(unsigned char x, unsigned char y) {
  int r = f(x, y);
  printf("f(%d, %d) = %d\n", x, y, r);
}

void g_test(int i) {
  unsigned char r = g(i);
  printf("g(%d) = %d\n", i, r);
}

int main(void) {
  f_test(100, 99);
  g_test(10000);
  return 0;
}
