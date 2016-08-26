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

  // static allows memory to be allocated on the heap instead of the
  // stack.  Of course, segfault may still occur on some systems.
  int i;
  static int src[268435456], dst[268435456], numElems; // 268435456 = 2^28
  numElems = 268435456; // 2^28 4-byte elements, i.e., 1GB

  // Source initialization:
  for (i = 0; i < numElems; i++)
    src[i] = i;

  printf("\nStart address of the source: 0x%llx\n", (uint64_t)src);
  printf("\nEnd address of the source: 0x%llx\n", (uint64_t)(src+numElems-1));
  printf("\nValue at end address of the source: %llu\n", (uint64_t)*(src+numElems-1));

  printf("\nSome elements of source before data copy:\n");
  printIntArray (src, 20);

  printf("\nNumber of elements to copy: %d\n", numElems);
  copyData(src, dst, numElems);

  printf("\nStart address of the destination: 0x%llx\n", (uint64_t)dst);
  printf("\nEnd address of the destination: 0x%llx\n", (uint64_t)(dst+numElems-1));
  printf("\nValue at end address of the destination: %llu\n", (uint64_t)*(dst+numElems-1));

  printf("\nSome elements of source after data copy:\n");
  printIntArray (src, 20);
  printf("\nSome elements of destination after data copy:\n");
  printIntArray (dst, 20);

}
