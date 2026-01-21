#include <stdbool.h>
#include <stdint.h>
#include <immintrin.h>


/**************************************************************************
 *  PAND xmm1, xmm2   8bit         (register source form)
 *************************************************************************/
__m128i pand_sse_register(__m128i x, __m128i y) {
    __asm__ volatile (
        "pand %1, %0"          // destination &= source_register
        : "+x"(x)              // destination: input/output XMM register
        : "x"(y)               // source_register: input XMM register
    );
    return x;
}

/* Test function for register source form */
bool test_pand_8bit(__m128i x, __m128i y) {
    uint8_t x_vals[16], y_vals[16], result_vals[16];

    __m128i result = pand_sse_register(x, y);

    _mm_storeu_si128((__m128i*)x_vals, x);
    _mm_storeu_si128((__m128i*)y_vals, y);
    _mm_storeu_si128((__m128i*)result_vals, result);

    for (int i = 0; i < 16; ++i) {
        if (result_vals[i] != (uint8_t)(x_vals[i] & y_vals[i])) {
            return false;
        }
    }
    return true;
}

/**************************************************************************
 *  PAND xmm1, m128 8bit            (memory source form)
 *************************************************************************/
__m128i pand_sse_memory(__m128i x, const __m128i* val) {
    __asm__ volatile (
        "pand %1, %0"          // destination &= source_memory
        : "+x"(x)              // destination: input/output XMM register
        : "m"(*val)            // source_memory: 128‑bit memory operand
    );
    return x;
}



/* Test function for memory source form */

bool test_pand_memory_8bit(__m128i x, __m128i y) {
    uint8_t x_vals[16], y_vals[16], result_vals[16];

     static __m128i y_aligned __attribute__((aligned(16)));
    y_aligned = y;                           

    __m128i result = pand_sse_memory(x, &y_aligned);
  
    _mm_storeu_si128((__m128i*)x_vals,      x);
    _mm_storeu_si128((__m128i*)y_vals,      y);
    _mm_storeu_si128((__m128i*)result_vals, result);

    for (int i = 0; i < 16; ++i) {
        if (result_vals[i] != (uint8_t)(x_vals[i] & y_vals[i])) {
            return false;
        }
    }
    return true;
}






// dummy main function, to allow us to link the executable
int main () { return 0;}
