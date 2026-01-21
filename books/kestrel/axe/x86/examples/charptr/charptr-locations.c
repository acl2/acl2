// Test case for lifting functions that take char* from different memory locations
// This tests how pointer location affects lifting

// TODO: Add test for actual string modification (writing bytes)
// TODO: Add test for pointer arithmetic without loops (e.g., read str[0] + str[1])
// TODO: Add test for returning a pointer to modified data

#include <stdint.h>
#include <stdlib.h>

// Global/static data segment (initialized)
char global_string[] = "global";
const char global_const_string[] = "const_global";

// BSS segment (uninitialized, zero-initialized at runtime)
char bss_string[100];

// Static local (also in data segment, but with internal linkage)
static char static_string[] = "static";

// String literal (typically in read-only .rodata section)
const char *literal_ptr = "literal";

// Function that reads with const - can't modify
int32_t read_only_byte(const char *str) {
    if (str == 0) {
        return -1;
    }
    return (int32_t)str[0];
}

// Function that can modify - no const
int32_t read_write_byte(char *str) {
    if (str == 0) {
        return -1;
    }
    int32_t result = (int32_t)str[0];
    // Could modify here if we wanted: str[0] = 'X';
    return result;
}

// Test function for string literal (read-only memory)
int32_t test_literal() {
    return read_only_byte("literal_string");  // In .rodata
}

// Test function for global data
int32_t test_global() {
    return read_write_byte(global_string);  // In .data
}

// Test function for const global data
int32_t test_const_global() {
    return read_only_byte(global_const_string);  // In .rodata
}

// Test function for BSS segment
int32_t test_bss() {
    bss_string[0] = 'B';  // Initialize first
    return read_write_byte(bss_string);  // In .bss
}

// Test function for stack-allocated string
int32_t test_stack() {
    char stack_string[] = "stack";  // On stack
    return read_write_byte(stack_string);
}

// Test function for heap-allocated string
int32_t test_heap() {
    char *heap_string = (char*)malloc(10);
    if (heap_string == 0) {
        return -1;
    }
    heap_string[0] = 'H';
    heap_string[1] = '\0';
    int32_t result = read_write_byte(heap_string);
    free(heap_string);
    return result;
}

// Test function for static local
int32_t test_static() {
    return read_write_byte(static_string);  // In .data with internal linkage
}

// Function that takes a pointer parameter (for lifting tests)
int32_t process_string(char *str) {
    // This is what we'll try to lift - takes external pointer
    if (str == 0) {
        return -1;
    }

    int32_t sum = 0;
    // Read first 4 bytes and sum them
    for (int i = 0; i < 4; i++) {
        sum += (int32_t)str[i];
        if (str[i] == 0) break;  // Stop at null terminator
    }
    return sum;
}

// Simple main
int main() {
    return 0;
}