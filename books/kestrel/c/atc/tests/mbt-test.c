#include <stdio.h>

#include "mbt.h"

void mbt1_test(int x) {
  int r = mbt1(x);
  printf("mbt(%d) = %d\n", x, r);
}

void mbt2_test(int x) {
  int r = mbt2(x);
  printf("mbt(%d) = %d\n", x, r);
}

void mbt_dollar_test(int x) {
  int r = mbt_dollar(x);
  printf("mbt$(%d) = %d\n", x, r);
}

int main(void) {
  mbt1_test(10);
  mbt1_test(200);
  mbt2_test(-5);
  mbt2_test(5);
  mbt_dollar_test(10);
  mbt_dollar_test(200);
  return 0;
}
