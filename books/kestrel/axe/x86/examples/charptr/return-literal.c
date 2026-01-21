// Simple test returning a string literal pointer
#include <stdint.h>

const char* get_literal() {
    return "hello";  // Returns pointer to string literal in .rodata
}

// Return first char of a literal
int32_t get_literal_char() {
    const char* str = "test";
    return (int32_t)str[0];  // Should return 't' (116)
}

int main() {
    return 0;
}