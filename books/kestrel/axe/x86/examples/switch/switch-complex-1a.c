// More complex switch statement to encourage jump table generation
// This example has more cases and more complex code in each case
// Version 1a: main() takes an argument to initialize global_counter
//             Uses argv[1][1] (second byte) instead of argv[1][0]

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

int main(int argc, char *argv[]) {
    int32_t cmd = 5;  // Default command

    // Set global_counter from command line argument,
    // to see if symbolic execution keeps it symbolic.
    if (argc > 1) {
        global_counter = (int32_t)argv[1][0];  // Use first byte of first arg
        cmd = (int32_t)argv[1][1];  // Use second byte for command
    }
    return process_command(cmd);
}
