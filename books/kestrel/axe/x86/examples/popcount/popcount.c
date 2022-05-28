// Written by Shipli Goel (see acl2/books/projects/x86isa/proofs/popcount/popcount.lisp).
// based on https://graphics.stanford.edu/~seander/bithacks.html.

#include <stdio.h>
#include <stdlib.h>

int popcount_32 (unsigned int v)
{
  v = v - ((v >> 1) & 0x55555555);
  v = (v & 0x33333333) + ((v >> 2) & 0x33333333);
  v = ((v + (v >> 4) & 0xF0F0F0F) * 0x1010101) >> 24;
  return(v);
 }

int popcount_64 (long unsigned int v)
{
  long unsigned int v1, v2;
  // v1: lower 32 bits of v
  v1 = (v & 0xFFFFFFFF);
  // printf ("\n v1: %lu", v1);
  // v2: upper 32 bits of v
  v2 = (v >> 32);
  // printf ("\n v2: %lu", v2);
  return (popcount_32(v1) + popcount_32(v2));
}

int main (int argc, char *argv[], char *env[])
{
  long unsigned int v;
  printf ("\nEnter the value v: ");
  scanf  ("%lu", &v);
  printf ("\nPopcount of %lu is: %d\n", v, popcount_64(v));
  return 0;
}
