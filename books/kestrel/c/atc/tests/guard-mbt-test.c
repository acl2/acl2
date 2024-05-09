#include <stdio.h>

#include "guard-mbt.h"

void f_test(int x) {
  int r = f(x);
  printf("f(%d) = %d\n", x, r);
}

int main(void) {
  f_test(10);
  f_test(50);
  return 0;
}
