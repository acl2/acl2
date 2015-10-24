#include "stdio.h"

void copyData (int* src, int* dst, int n) {

  int* dstEnd = dst + n;

  while (dst != dstEnd)
    *dst++ = *src++;

}
