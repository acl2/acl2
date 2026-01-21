#include <stdio.h>
#include <stdbool.h>

unsigned char sub_two_longs_return_ah(long x, long y) {
    unsigned char ah;

    asm volatile (
        "movq %1, %%rax;"  
        "subq %2, %%rax;"   
        "lahf;"             
        "movb %%ah, %0;"    
        : "=r" (ah)
        : "r" (x), "r" (y)
        : "rax", "cc"
    );

    return ah;
}

//Test function for Zero Flag after subtraction
bool test_long_sub_ZF(long x, long y) {
    long diff = x - y;
    unsigned char flags = sub_two_longs_return_ah(x, y);

    if (diff == 0) {
        return ((flags & 0x40) == 0x40); 
    } else {
        return ((flags & 0x40) == 0x00); 
    }
}

//Dummy main function
int main() {return 0;}
