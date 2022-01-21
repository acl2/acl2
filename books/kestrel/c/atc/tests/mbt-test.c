#include <stdio.h>

void mbt_test(int x) {
  int r = mbt(x);
  printf("mbt(%d) = %d\n", x, r);
}

void mbt_dollar_test(int x) {
  int r = mbt_dollar(x);
  printf("mbt(%d) = %d\n", x, r);
}

int main(void) {
  mbt_test(10);
  mbt_test(200);
  mbt_dollar_test(10);
  mbt_dollar_test(200);
  return 0;
}
