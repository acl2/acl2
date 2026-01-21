// More complex switch statement to encourage jump table generation
// This example has more cases and more complex code in each case

#include <stdint.h>

// Global variable to prevent optimization
volatile int32_t global_counter = 0;

int32_t process_command(int32_t cmd) {
    int32_t result = 0;

    switch (cmd) {
        case 0:
            result = global_counter * 2;
            global_counter++;
            break;
        case 1:
            result = global_counter * 3;
            global_counter += 2;
            break;
        case 2:
            result = global_counter * 4;
            global_counter += 3;
            break;
        case 3:
            result = global_counter * 5;
            global_counter += 4;
            break;
        case 4:
            result = global_counter * 6;
            global_counter += 5;
            break;
        case 5:
            result = global_counter * 7;
            global_counter += 6;
            break;
        case 6:
            result = global_counter * 8;
            global_counter += 7;
            break;
        case 7:
            result = global_counter * 9;
            global_counter += 8;
            break;
        case 8:
            result = global_counter * 10;
            global_counter += 9;
            break;
        case 9:
            result = global_counter * 11;
            global_counter += 10;
            break;
        default:
            result = -1;
            global_counter = 0;
            break;
    }

    return result;
}

int main() {
    return process_command(5);
}