// Soumava Ghosh

// syscall-utils.c as a shared library:

// On Linux systems:
// gcc -c -Wall -Werror -fpic syscall-utils.c
// gcc -shared -o libsyscallutils.so syscall-utils.o

// On Darwin systems:
// gcc -m64 -dynamiclib -Wall -o libsyscallutils.dylib syscall-utils.c

#include <stdio.h>
#include <sys/stat.h>

#define _STRUCT_STAT_ 1

int get_struct_size (unsigned int which) {
  switch (which) {
  case _STRUCT_STAT_ : 
    return sizeof(struct stat);
  }
  return -1;
}

/*
int main () {
  printf("\n%d\n", get_struct_size(_STRUCT_STAT_));
  return 0;
}
*/
