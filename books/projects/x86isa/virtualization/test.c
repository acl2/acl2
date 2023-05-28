#include "main.h"
#include <stdio.h>

int main() {
  ccl_init();
  printf("%lx", ccl_step());
  return 0;
}
