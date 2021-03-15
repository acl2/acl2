#include <stdio.h>

void test_f() {
  unsigned char a[10] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
  int i = 4;
  int r = f(a, i);
  printf("f(array, %d) = %d\n", i, r);
}

int main(void) {
  test_f();
}
