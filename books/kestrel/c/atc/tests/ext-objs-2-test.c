#include <stdio.h>

int main(void) {
  int a = f(2);
  h(2);
  int b = f(2);
  printf("(a, b) = (%d, %d)\n", a, b);
  return 0;
}
