// Soumava Ghosh

// gcc -O2 -o wc-file.o wc-file.c

// This program takes in the name of a file as input and prints out
// the number of characters, words, and lines in it.

#include <stdio.h>
#include <stdint.h>

#define IN  0
#define OUT 1

// See pre-defined macros supported by your GCC using:
// gcc -dM -E - < /dev/null

#ifdef __linux__
static int sysread_num  = 0;
static int syswrite_num = 1;
static int sysopen_num  = 2;
#endif
#ifdef __MACH__  // Apple machines
static int sysread_num  = 0x2000003;
static int syswrite_num = 0x2000004;
static int sysopen_num  = 0x2000005;
#endif


int writeNumberToBuffer(char* buffer, int bufSize, int number) {
  int numSize = 0, div = 1;
  int i = 0, tempNum = number;

  do {
    numSize ++;
    div *= 10;
    tempNum = tempNum / 10;
  }
  while (tempNum != 0);

  if (bufSize < numSize) {
    return -1;
  }

  div = div/10;
  tempNum = number;

  while (i < numSize) {
    buffer[i++] = tempNum / div + 48;
    tempNum = tempNum % div;
    div = div / 10;
  }

  return numSize;
}

int syscall_read(int fd, void* buf, long int count) {
  uint64_t ret;
  uint64_t num = (uint64_t)sysread_num;
  __asm__ volatile                    // volatile indicates not to
    (                                 // be optimized by gcc
     "mov %1, %%rax\n\t"              // System call number in RAX
     "mov %2, %%rdi\n\t"              // First parameter in RDI --- FD is n32pp.
     "mov %3, %%rsi\n\t"              // Second parameter in RSI
     "mov %4, %%rdx\n\t"              // Third parameter in RDX
     "syscall"
     : "+a"(ret)                      // return value to be moved to 'ret'
				      // 'a' indicates RAX

     : "g"(num), "g"((uint64_t)fd),               // input arguments, 'g' indicates these
       "g"((uint64_t)buf), "g"((uint64_t)count)   // can be stored anywhere expect in registers
						  // that are not general-purpose registers

     : "%rdi",                        // Clobbered registers - the registers that
       "%rsi",                        // are used by the assembly code
       "%rdx",
       "cc", "memory",                // flags and memory will change, as side effects of this asm block
       "%rcx",                        // RCX and R11 are used by kernel
       "%r11"                         // and destroyed
     );
  return (int)ret;
}


int syscall_open(char* pathname, unsigned int flags, unsigned int mode) {
  uint64_t ret;
  uint64_t num = (uint64_t)sysopen_num;
  __asm__ volatile
    (
	"mov %1, %%rax\n\t"
	"mov %2, %%rdi\n\t"
	"mov %3, %%rsi\n\t"
	"mov %4, %%rdx\n\t"
	"syscall"
	: "+a"(ret)
	: "g"(num), "g"((uint64_t)pathname), "g"((uint64_t)flags), "g"((uint64_t)mode)
	: "%rdi", "%rsi", "%rdx", "%rcx", "%r11", "cc", "memory"
    );
  return (int)ret;
}

int syscall_write(int fd, void* buf, long int count) {
  uint64_t ret;
  uint64_t num = (uint64_t)syswrite_num;
  __asm__ volatile
    (
	"mov %1, %%rax\n\t"
	"mov %2, %%rdi\n\t"
	"mov %3, %%rsi\n\t"
	"mov %4, %%rdx\n\t"
	"syscall"
	: "+a"(ret)
	: "g"(num), "g"((uint64_t)fd), "g"((uint64_t)buf), "g"((uint64_t)count)
	: "%rdi", "%rsi", "%rdx", "%rcx", "%r11", "cc", "memory"
    );
  return (int)ret;
}


int main() {
    char filename[256], buffer[256];
    char output[256];
    int ret, nBytes, fd, i;
    long int filename_count = sizeof(filename);
    long int buffer_count = sizeof(buffer);
    long int output_size = 0;
    int nc, nw, nl, state;

    nc = nl = nw = 0;
    state = OUT;

    ret = syscall_read(0, filename, filename_count);
    if (ret == -1) {
	return 0;
    }

    nBytes = ret;
    filename[nBytes - 1] = '\0';

    ret = syscall_open(filename, 0, 0);
    if (ret == -1) {
	return 0;
    }

    fd = ret;
    do {
      ret = syscall_read(fd, buffer, buffer_count);
      if (ret == -1) {
	return 0;
      }

      nBytes = ret;
      if (nBytes == 0) {
	break;
      }

      for (i = 0; i < nBytes; i++) {
	++nc;
	if (buffer[i] == '\n') {
	  ++nl;
	}
	if (buffer[i] == ' ' || buffer[i] == '\n' || buffer[i] == '\t' ||
	    buffer[i] == ',' || buffer[i] == '.' || buffer[i] == ';') {
	  state = OUT;
	}
	else if (state == OUT) {
	  state = IN;
	  ++nw;
	}
      }
    }
    while (nBytes == buffer_count);

    output[output_size++] = 'n';
    output[output_size++] = 'c';
    output[output_size++] = ':';
    nBytes = writeNumberToBuffer(&output[output_size], 256 - output_size, nc);
    if (nBytes == -1) {
      return 0;
    }

    output_size += nBytes;
    output[output_size++] = ' ';
    output[output_size++] = 'n';
    output[output_size++] = 'w';
    output[output_size++] = ':';
    nBytes = writeNumberToBuffer(&output[output_size], 256 - output_size, nw);
    if (nBytes == -1) {
      return 0;
    }

    output_size += nBytes;
    output[output_size++] = ' ';
    output[output_size++] = 'n';
    output[output_size++] = 'l';
    output[output_size++] = ':';
    nBytes = writeNumberToBuffer(&output[output_size], 256 - output_size, nl);
    if (nBytes == -1) {
      return 0;
    }

    output_size += nBytes;
    output[output_size++] = '\n';
    output[output_size] = '\0';
    ret = syscall_write(1, output, output_size);
    if (ret == -1) {
      return 0;
    }
    return 0;
}

//
// Assembly code entry point is _start()
// Use this if no std libs are being included.
/*
void _start() {
  main();
  asm (
       "mov $0x2000001, %rax;"
       "xor %rdi, %rdi;"
       "syscall");
}
*/
