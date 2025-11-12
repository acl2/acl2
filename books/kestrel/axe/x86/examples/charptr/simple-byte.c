// Very simple char* test - no null check, just read byte
#include <stdint.h>

int32_t get_byte(char *str) {
    return (int32_t)str[0];
}

int main() {
    return 0;
}
