// gcc -O1 -g -c core.c -o core.o
// gcc -o dataCopy.o dataCopy.c core.o

#include "stdio.h"
#include "core.h"

void printIntArray (int* x, int n) {

  printf("\n");

  for (int i = 0; i < n; i++)
    printf(" %d ", *(x+i));

  printf("\n");

}

int main () {

  int src[5], dst[5];

  src[0] = 1;
  src[1] = 2;
  src[2] = 3;
  src[3] = 4;
  src[4] = 5;

  printf("\nSource before data copy:\n");
  printIntArray (src, 5);

  copyData(src, dst, 5);

  printf("\nSource after data copy:\n");
  printIntArray (src, 5);
  printf("\nDestination after data copy:\n");
  printIntArray (dst, 5);

}
