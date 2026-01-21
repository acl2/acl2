#include <stdbool.h>
#include <stdint.h>



// Declare global pointer
uint32_t *y_addr;


unsigned char add_r32_m32_return_CF(uint32_t x, uint32_t y) {
    unsigned char ah;

    __asm__ volatile (
        "movl %1, %%eax;"        // eax = x
        "movl %2, %[mem];"       // *y_addr = y
        "addl %[mem], %%eax;"    // eax += *y_addr
        "lahf;"                  // load flags into AH
        "movb %%ah, %0;"         // move AH to output
        : "=r" (ah)              // output
        : "r" (x), "r" (y), [mem] "m" (*y_addr)  // inputs
        : "%eax", "%ah", "memory"
    );

    return ah;
}






//check property for CF
//CF is bit 0 in ah

bool test_add_r32_r32_CF (uint32_t  x, uint32_t  y) {
    uint32_t  sum = x + y;

    
    unsigned char flags = add_r32_m32_return_CF(x, y);

    

    if ((sum < x) && ((flags & 0x01)==0x01)) {
        return true;  
    }
    else if ((flags & 0x01)==0x00) {
      return true;  
    }

    return false;

    
}


// dummy main function, to allow us to link the executable
int main () { return 0;}
