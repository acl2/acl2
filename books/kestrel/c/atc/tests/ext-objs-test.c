#include <stdio.h>

int main(void) {
  int a = f(2);
  g(2);
  int b = f(2);
  printf("(a, b) = (%d, %d)\n", a, b);
  return 0;
}
