// Shilpi Goel

// rdrand.c as a shared library:

// On Linux systems:
// gcc -c -Wall -Werror -fpic rdrand.c
// gcc -shared -o librdrand.so rdrand.c

// On Darwin systems:
// gcc -m64 -dynamiclib -Wall -o librdrand.dylib rdrand.c

#include "stdio.h"

unsigned short _rdrand16(unsigned short *num) {

  unsigned short n;
  unsigned short cf_error_stat;

  asm("rdrand %%ax\n\t"
      "mov $1,%%dx\n\t"
      "cmovae %%ax,%%dx\n\t"
      "mov %%dx,%1\n\t"
      "mov %%ax,%0"
      :"=r"(n), "=r"(cf_error_stat)
      ::"%ax","%dx");

  // printf("\n%u\n", n);

  *num = n;
  return (cf_error_stat);
}

unsigned int _rdrand32(unsigned int *num) {

  unsigned int n;
  unsigned int cf_error_stat;

  asm("rdrand %%eax\n\t"
      "mov $1,%%edx\n\t"
      "cmovae %%eax,%%edx\n\t"
      "mov %%edx,%1\n\t"
      "mov %%eax,%0"
      :"=r"(n),"=r"(cf_error_stat)
      ::"%eax","%edx");

  // printf("\n%u\n", n);

  *num = n;
  return (cf_error_stat);

}

unsigned long long _rdrand64 (unsigned long long *num) {

  unsigned long long n, cf_error_stat;

  asm("rdrand %%rax\n\t"
      "mov $1,%%rdx\n\t"
      "cmovae %%rax,%%rdx\n\t"
      "mov %%rdx,%1\n\t"
      "mov %%rax,%0"
      :"=r"(n),"=r"(cf_error_stat)
      ::"%rax","%rdx");

  *num = n;
  // printf("\n%llu\n", n);

  return (cf_error_stat);

}

/*
int main () {

  printf("\n%llu\n", _rdrand64()); // returns cf
}
*/
