#include <stdio.h>

void cond1_test(int x, int y, int z) {
  int r = cond1(x, y, z);
  printf("cond1(%d, %d, %d) = %d\n", x, y, z, r);
}

void cond2_test(int x) {
  int r = cond2(x);
  printf("cond2(%d) = %d\n", x, r);
}

void cond3_test(int a, int b) {
  int r = cond3(a, b);
  printf("cond3(%d, %d) = %d\n", a, b, r);
}

int main(void) {
  cond1_test(11, 8888, -220);
  cond1_test(0, 888, -220);
  cond2_test(20000);
  cond2_test(23);
  cond3_test(1700, 3);
  cond3_test(1700, -99);
}
