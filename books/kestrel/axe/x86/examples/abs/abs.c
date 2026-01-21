// Simple test case for abs() library function
// Compiled with: gcc -O0 -fno-builtin -o abs.elf64 abs.c
//
// This tests Axe's ability to recognize and summarize library calls.
// The abs() function is simple: no loops, no syscalls, just a conditional negate.

#include <stdlib.h>
#include <stdint.h>

int32_t test_abs(int32_t x) {
    return abs(x);
}

int main(int argc, char *argv[]) {
    // Use argc to get a symbolic input
    int32_t input = (int32_t)argc;
    int32_t result = test_abs(input);
    return result;
}
