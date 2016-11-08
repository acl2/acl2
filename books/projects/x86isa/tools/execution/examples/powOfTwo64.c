// Source: https://graphics.stanford.edu/~seander/bithacks.html#DetermineIfPowerOf2

// gcc -O2 powOfTwo64.c -o powOfTwo64.o

#include "stdio.h"
#include "stdbool.h"

bool powerOfTwo (long unsigned int v) {
  bool f;
  f = v && !(v & (v - 1));
  return f;
}

int main () {

  long unsigned int v; // we want to see if v is a power of 2
  bool f;              // the result goes here

  printf("\nEnter a value: ");
  scanf("%lu", &v);

  f = powerOfTwo(v);

  printf ("\%lu is a power of 2: %d\n", v, f);
  return 0;

}

/*
0000000100000ec0 <_powerOfTwo>:
   100000ec0:	55                   	push   %rbp
   100000ec1:	48 89 e5             	mov    %rsp,%rbp
   100000ec4:	48 85 ff             	test   %rdi,%rdi
   100000ec7:	74 0c                	je     100000ed5 <_powerOfTwo+0x15>
   100000ec9:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
   100000ecd:	48 85 c7             	test   %rax,%rdi
   100000ed0:	0f 94 c0             	sete   %al
   100000ed3:	eb 02                	jmp    100000ed7 <_powerOfTwo+0x17>
   100000ed5:	31 c0                	xor    %eax,%eax
   100000ed7:	5d                   	pop    %rbp
   100000ed8:	c3                   	retq   
   100000ed9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
*/
