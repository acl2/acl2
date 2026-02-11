#include <stdint.h>
#include <stdbool.h>

static inline unsigned char blsi_r32_r32_return_ah(uint32_t x, uint32_t y) {
    unsigned char ah;
    __asm__ volatile (
        "movl %1, %%eax;"        // eax = x 
        "movl %2, %%ebx;"        // ebx = y (source)
        "blsi %%ebx, %%eax;"     // eax = blsi(y)
        "lahf;"                  // AH = flags 
        "movb %%ah, %0;"
        : "=r"(ah)
        : "r"(x), "r"(y)
        : "eax", "ebx", "cc"
    );
    return ah;
}


// CF: 
bool test_blsi_r32_r32_CF(uint32_t x, uint32_t y) {
    (void)x;
    unsigned char flags = blsi_r32_r32_return_ah(x, y);
    unsigned char cf = flags & 0x01;
    unsigned char expected_cf = (y == 0) ? 0x01 : 0x00;  
    return cf == expected_cf;
}

// ZF: 
bool test_blsi_r32_r32_ZF(uint32_t x, uint32_t y) {
    (void)x;
    unsigned char flags = blsi_r32_r32_return_ah(x, y);
    unsigned char zf = flags & 0x40;
    uint32_t res = y & (uint32_t)(-(int32_t)y);
    unsigned char expected_zf = (res == 0) ? 0x40 : 0x00;
    return zf == expected_zf;
}

// SF: bit 31 of result
bool test_blsi_r32_r32_SF(uint32_t x, uint32_t y) {
    (void)x;
    unsigned char flags = blsi_r32_r32_return_ah(x, y);
    unsigned char sf = flags & 0x80;
    uint32_t res = y & (uint32_t)(-(int32_t)y);
    unsigned char expected_sf = (res & 0x80000000) ? 0x80 : 0x00;
    return sf == expected_sf;
}

static inline unsigned char blsi_r32_r32_return_OF(uint32_t x, uint32_t y) {
    unsigned char of;
    __asm__ volatile (
        "movl %1, %%eax;"
        "movl %2, %%ebx;"
        "blsi %%ebx, %%eax;"
        "seto %0;"
        : "=r"(of)
        : "r"(x), "r"(y)
        : "eax", "ebx", "cc"
    );
    return of;
}

// OF is always 0 for BLSI
bool test_blsi_r32_r32_OF(uint32_t x, uint32_t y) {
    unsigned char of = blsi_r32_r32_return_OF(x, y);
    return (of == 0);
}


// dummy main function, to allow us to link the executable

int main () { return 0;}