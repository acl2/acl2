#include <stdbool.h>
#include <stdint.h>
#include <immintrin.h>

//************************************************************************** */
//  PADDB xmm1, xmm2 (register source)

__m128i paddb_sse_register(__m128i x, __m128i y) {
    __asm__ volatile (
        "paddb %1, %0"          // destination += source_register
        : "+x"(x)               // destination: input/output XMM register
        : "x"(y)                // source_register: input XMM register
    );
    return x;
}


// Test function for register source form
bool test_paddb_sse_register(__m128i x, __m128i y) {
    int8_t x_vals[16], y_vals[16], result_vals[16];

    __m128i result = paddb_sse_register(x, y);

    // Store XMM registers to memory arrays
    _mm_storeu_si128((__m128i*)x_vals, x);
    _mm_storeu_si128((__m128i*)y_vals, y);
    _mm_storeu_si128((__m128i*)result_vals, result);

    // Verify each byte (16 bytes for SSE2 vs 8 for MMX)
    for (int i = 0; i < 16; ++i) {
        if (result_vals[i] != (int8_t)(x_vals[i] + y_vals[i])) {
            return false;
        }
    }
    return true;
}
// ***************************************************************
// PADDB xmm1, m128 (memory source)

__m128i paddb_sse_memory(__m128i x, const __m128i* val) {
    __asm__ volatile (
        "paddb %1, %0"          // destination += source_memory
        : "+x"(x)               // destination: input/output XMM register
        : "m"(*val)             // source_memory: 128-bit memory operand
    );
    return x;
}

// Test function for memory source form  
bool test_paddb_sse_memory(__m128i x, __m128i y) {
    int8_t x_vals[16], y_vals[16], result_vals[16];

    // Store y in aligned memory to use as memory operand
    __m128i aligned_y __attribute__((aligned(16))) = y;
    
    __m128i result = paddb_sse_memory(x, &aligned_y);

    _mm_storeu_si128((__m128i*)x_vals, x);
    _mm_storeu_si128((__m128i*)y_vals, y);
    _mm_storeu_si128((__m128i*)result_vals, result);

    for (int i = 0; i < 16; ++i) {
        if (result_vals[i] != (int8_t)(x_vals[i] + y_vals[i])) {
            return false;
        }
    }
    return true;
}

//****************************************************************************** 
//PADDW xmm1, xmm2/m128

__m128i paddw_sse_register(__m128i x, __m128i y) {
    __asm__ volatile (
        "paddw %1, %0"          // xmm1 += xmm2
        : "+x"(x)               // XMM register input/output
        : "x"(y)                // XMM register input
    );
    return x;
}

// Test function for register source form
bool test_paddw_sse_register(__m128i x, __m128i y) {
    int16_t x_vals[8], y_vals[8], result_vals[8];

    __m128i result = paddw_sse_register(x, y);

    _mm_storeu_si128((__m128i*)x_vals, x);
    _mm_storeu_si128((__m128i*)y_vals, y);
    _mm_storeu_si128((__m128i*)result_vals, result);

    for (int i = 0; i < 8; ++i) {
        if (result_vals[i] != (int16_t)(x_vals[i] + y_vals[i])) {
            return false;
        }
    }
    return true;
}
//***************************************************************************
// PADDW xmm1, m128 

__m128i paddw_sse_memory(__m128i x, const __m128i *val) {
    __asm__ volatile (
        "paddw %1, %0"          // xmm1 += [m128]
        : "+x"(x)               // XMM register input/output
        : "m"(*val)             // 128-bit memory source
    );
    return x;
}

// Test function for memory source form
bool test_paddw_sse_memory(__m128i x, __m128i y) {
    int16_t x_vals[8], y_vals[8], result_vals[8];

    __m128i aligned_y __attribute__((aligned(16))) = y;

    __m128i result = paddw_sse_memory(x, &aligned_y);

    _mm_storeu_si128((__m128i*)x_vals, x);
    _mm_storeu_si128((__m128i*)y_vals, y);
    _mm_storeu_si128((__m128i*)result_vals, result);

    for (int i = 0; i < 8; ++i) {
        if (result_vals[i] != (int16_t)(x_vals[i] + y_vals[i])) {
            return false;
        }
    }
    return true;
}

//******************************************************************
//  PADDD xmm1, xmm2

__m128i paddd_sse_register(__m128i x, __m128i y) {
    __asm__ volatile (
        "paddd %1, %0"          // destination += source_register
        : "+x"(x)               // "+x" = XMM register input/output
        : "x"(y)                // "x" = XMM register input
    );
    return x;
}

// Test function for register source form
bool test_paddd_sse_register(__m128i x, __m128i y) {
    int32_t x_vals[4], y_vals[4], result_vals[4];

    __m128i result = paddd_sse_register(x, y);

    _mm_storeu_si128((__m128i*)x_vals, x);
    _mm_storeu_si128((__m128i*)y_vals, y);
    _mm_storeu_si128((__m128i*)result_vals, result);

    for (int i = 0; i < 4; ++i) {
        if (result_vals[i] != (int32_t)(x_vals[i] + y_vals[i])) {
            return false;
        }
    }
    return true;
}

//******************************************************************
// PADDD xmm1, m128 

__m128i paddd_sse_memory(__m128i x, const __m128i *val) {
    __asm__ volatile (
        "paddd %1, %0"          // destination += source_memory
        : "+x"(x)               // XMM register input/output
        : "m"(*val)             // 128-bit memory operand
    );
    return x;
}

// Test function for memory source form
bool test_paddd_sse_memory(__m128i x, __m128i y) {
    int32_t x_vals[4], y_vals[4], result_vals[4];

    // Store y in aligned memory to use as memory operand
    __m128i aligned_y __attribute__((aligned(16))) = y;

    __m128i result = paddd_sse_memory(x, &aligned_y);

    _mm_storeu_si128((__m128i*)x_vals, x);
    _mm_storeu_si128((__m128i*)y_vals, y);
    _mm_storeu_si128((__m128i*)result_vals, result);

    for (int i = 0; i < 4; ++i) {
        if (result_vals[i] != (int32_t)(x_vals[i] + y_vals[i])) {
            return false;
        }
    }
    return true;
}

//****************************************************************
//  xmm1, xmm2

__m128i paddq_sse_register(__m128i x, __m128i y) {
    __asm__ volatile (
        "paddq %1, %0"          // destination += source_register
        : "+x"(x)               // XMM register input/output
        : "x"(y)                // XMM register input
    );
    return x;
}

// Test function for register source form
bool test_paddq_sse_register(__m128i x, __m128i y) {
    int64_t x_vals[2], y_vals[2], result_vals[2];

    __m128i result = paddq_sse_register(x, y);

    _mm_storeu_si128((__m128i*)x_vals, x);
    _mm_storeu_si128((__m128i*)y_vals, y);
    _mm_storeu_si128((__m128i*)result_vals, result);

    for (int i = 0; i < 2; ++i) {
        if (result_vals[i] != (int64_t)(x_vals[i] + y_vals[i])) {
            return false;
        }
    }
    return true;
}
//*******************************************************************
// xmm1,m128 

__m128i paddq_sse_memory(__m128i x, const __m128i *val) {
    __asm__ volatile (
        "paddq %1, %0"          // destination += source_memory
        : "+x"(x)               // XMM register input/output
        : "m"(*val)             // 128-bit memory source
    );
    return x;
}

// Test function for memory source form
bool test_paddq_sse_memory(__m128i x, __m128i y) {
    int64_t x_vals[2], y_vals[2], result_vals[2];

    // Align y to 16 bytes for safe memory operand
    __m128i aligned_y __attribute__((aligned(16))) = y;

    __m128i result = paddq_sse_memory(x, &aligned_y);

    _mm_storeu_si128((__m128i*)x_vals, x);
    _mm_storeu_si128((__m128i*)y_vals, y);
    _mm_storeu_si128((__m128i*)result_vals, result);

    for (int i = 0; i < 2; ++i) {
        if (result_vals[i] != (int64_t)(x_vals[i] + y_vals[i])) {
            return false;
        }
    }
    return true;
}

// dummy main function, to allow us to link the executable
int main () { return 0;}


