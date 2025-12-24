#include <limits.h>
#include <stdio.h>

int main(void) {
  #ifdef __STDC_VERSION__
    long stdc = __STDC_VERSION__;
  #else
    long stdc = 0;
  #endif

  // Note: clang also defines __GNUC__
  #if defined(__GNUC__) && !defined(__STRICT_ANSI__)
    _Bool gcc_extensions = 1;
  #else
    _Bool gcc_extensions = 0;
  #endif

  printf("%ld\n", stdc);                 // version -> c standard
  printf("%d\n", gcc_extensions);        // version -> gcc extensions
  printf("%d\n", sizeof(short));         // short-bytes
  printf("%d\n", sizeof(int));           // int-bytes
  printf("%d\n", sizeof(long));          // long-bytes
  printf("%d\n", sizeof(long long));     // llong-bytes
  // See [C17:5.2.4.2.1/2]
  printf("%d\n", CHAR_MIN != SCHAR_MIN); // plain-char-signedp

  return 0;
}
