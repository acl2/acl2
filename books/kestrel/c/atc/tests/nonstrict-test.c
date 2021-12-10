#include <stdio.h>

void and_test(int x, int y) {
  int r = and(x, y);
  printf("and(%d, %d) = %d\n", x, y, r);
}

void or_test(int x, int y) {
  int r = or(x, y);
  printf("and(%d, %d) = %d\n", x, y, r);
}

void ifand_test(int x, int y) {
  int r = ifand(x, y);
  printf("ifand(%d, %d) = %d\n", x, y, r);
}

void ifor_test(int x, int y) {
  int r = ifor(x, y);
  printf("ifor(%d, %d) = %d\n", x, y, r);
}

void condand_test(int x) {
  int r = condand(x);
  printf("condand(%d) = %d\n", x, r);
}

void condor_test(int x) {
  int r = condor(x);
  printf("condor(%d) = %d\n", x, r);
}

void notandor_test(int x) {
  int r = notandor(x);
  printf("notandor(%d) = %d\n", x, r);
}

int main(void) {
  and_test(0, 0);
  and_test(0, 2);
  and_test(2, 0);
  and_test(2, 2);
  or_test(0, 0);
  or_test(0, 2);
  or_test(2, 0);
  or_test(2, 2);
  ifand_test(3, 7);
  ifand_test(3, 170);
  ifor_test(3, 2);
  ifor_test(3, 17);
  condand_test(5);
  condand_test(500);
  condor_test(-60);
  condor_test(3);
  notandor_test(3);
  notandor_test(150);
  return 0;
}
