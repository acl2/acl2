#include <stdio.h>

extern unsigned int arr2[8];

int main(void) {
  int a = f(2);
  h(2);
  int b = f(2);
  printf("(a, b) = (%d, %d)\n", a, b);
  i();
  printf("arr2[0] = %d\n", arr2[0]);
  return 0;
}
