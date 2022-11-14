#include <stdio.h>

#include "assign.h"

void test_f() {
  int x = 7733;
  int y = -939;
  int r = f(x, y);
  printf("f(%d, %d) = %d\n", x, y, r);
}

void test_g() {
  int x = 737838;
  int y = -4400;
  int r = g(x, y);
  printf("g(%d, %d) = %d\n", x, y, r);
}

int main(void) {
  test_f();
  test_g();
  return 0;
}
