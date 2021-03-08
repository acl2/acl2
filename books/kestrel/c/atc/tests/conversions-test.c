#include <stdio.h>

int main(void) {
  unsigned char x = 100;
  unsigned char y = 99;
  int r = f(x, y);
  printf("f(%d, %d) = %d\n", x, y, r);
}
