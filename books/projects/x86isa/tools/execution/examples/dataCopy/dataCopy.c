// gcc -O1 -g -c core.c -o core.o
// gcc -o dataCopy.o dataCopy.c core.o

#include "stdio.h"
#include "stdint.h"
#include "core.h"

void printIntArray (int* x, int n) {

  int i;
  printf("\n");

  for (i = 0; i < n; i++)
    printf(" %d ", *(x+i));

  printf("\n");

}

int main () {

  int i;
  int src[1024], dst[1024], numElems;
  numElems = 1024;
  
  // Source initialization:
  for (i = 0; i < numElems; i++)
    src[i] = i;

  printf("\nStart address of the source: 0x%llx\n", (uint64_t)src);
  printf("\nEnd address of the source: 0x%llx\n", (uint64_t)(src+numElems-1));
  printf("\nValue at end address of the source: %llu\n", (uint64_t)*(src+numElems-1));

  printf("\nSome elements of source before data copy:\n");
  printIntArray (src, 5);

  printf("\nNumber of elements to copy: %d\n", numElems);
  copyData(src, dst, numElems);

  printf("\nStart address of the destination: 0x%llx\n", (uint64_t)dst);
  printf("\nEnd address of the destination: 0x%llx\n", (uint64_t)(dst+numElems-1));
  printf("\nValue at end address of the destination: %llu\n", (uint64_t)*(dst+numElems-1));

  printf("\nSome elements of source after data copy:\n");
  printIntArray (src, 5);
  printf("\nSome elements of destination after data copy:\n");
  printIntArray (dst, 5);

}
