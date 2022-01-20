#include <stdio.h>

int main(void) {
  printf("signed int decimal = %d\n",
         signed_int_decimal());
  printf("signed int octal = %d\n",
         signed_int_octal());
  printf("signed int hexadecimal = %d\n",
         signed_int_hexadecimal());
  printf("unsigned int decimal = %u\n",
         unsigned_int_decimal());
  printf("unsigned int octal = %o\n",
         unsigned_int_octal());
  printf("unsigned int hexadecimal = %x\n",
         unsigned_int_hexadecimal());
  printf("signed long decimal = %ld\n",
         signed_long_decimal());
  printf("signed long octal = %ld\n",
         signed_long_octal());
  printf("signed long hexadecimal = %ld\n",
         signed_long_hexadecimal());
  printf("unsigned long decimal = %lu\n",
         unsigned_long_decimal());
  printf("unsigned long octal = %lo\n",
         unsigned_long_octal());
  printf("unsigned long hexadecimal = %lx\n",
         unsigned_long_hexadecimal());
  printf("signed long long decimal = %lld\n",
         signed_long_long_decimal());
  printf("signed long long octal = %lld\n",
         signed_long_long_octal());
  printf("signed long long hexadecimal = %lld\n",
         signed_long_long_hexadecimal());
  printf("unsigned long long decimal = %llu\n",
         unsigned_long_long_decimal());
  printf("unsigned long long octal = %llo\n",
         unsigned_long_long_octal());
  printf("unsigned long long hexadecimal = %llx\n",
         unsigned_long_long_hexadecimal());
  return 0;
}
