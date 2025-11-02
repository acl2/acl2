// Simple switch statement example for Axe x86 lifting

#include <stdint.h>

int32_t classify_value(int32_t x) {
    switch (x) {
        case 0:
            return 100;
        case 1:
            return 200;
        case 2:
            return 300;
        case 3:
            return 400;
        default:
            return -1;
    }
}

int main() {
    return 0;
}
