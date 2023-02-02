#include <stdio.h>

#include "pointers.h"

void f_test() {
  int x = -3;
  int r = f(&x);
  printf("f(%d) = %d\n", x, r);
}

void g_test() {
  unsigned int a = 18;
  unsigned int b = 2;
  int r = g(&a, &b);
  printf("g(%d, %d) = %d\n", a, b, r);
}

int main(void) {
  f_test();
  g_test();
  return 0;
}
