#include <stdbool.h>
#include <stdint.h>
#include <immintrin.h>

//*****************************************************************
//  VPADDB xmm1, xmm2, xmm3

__m128i vpaddb_sse_register(__m128i a, __m128i b) {
    __m128i result;
    __asm__ volatile (
        "vpaddb %2, %1, %0"
        : "=x"(result)        // result in XMM register
        : "x"(a), "x"(b)      // a = xmm2, b = xmm3
    );
    return result;
}

// Test function for VPADDB register form
bool test_vpaddb_register(__m128i a, __m128i b) {
    int8_t a_vals[16], b_vals[16], result_vals[16];

    __m128i result = vpaddb_sse_register(a, b);

    _mm_storeu_si128((__m128i*)a_vals, a);
    _mm_storeu_si128((__m128i*)b_vals, b);
    _mm_storeu_si128((__m128i*)result_vals, result);

    for (int i = 0; i < 16; i++) {
        if (result_vals[i] != (int8_t)(a_vals[i] + b_vals[i])) {
            return false;
        }
    }
    return true;
}

//***********************************************************
//VPADDB xmm1, xmm2, m128
static __m128i global_b __attribute__((aligned(16)));

__m128i vpaddb_sse_memory_global(__m128i a) {
    __m128i result;
    __asm__ volatile (
        "vpaddb %2, %1, %0"
        : "=x"(result)        
        : "x"(a), "m"(global_b) 
    );
    return result;
}

bool test_vpaddb_memory_global(__m128i a) {
    int8_t a_vals[16], b_vals[16], result_vals[16];

    
    __m128i result = vpaddb_sse_memory_global(a);

    _mm_storeu_si128((__m128i*)a_vals, a);
    _mm_storeu_si128((__m128i*)b_vals, global_b);
    _mm_storeu_si128((__m128i*)result_vals, result);

    for (int i = 0; i < 16; i++) {
        if (result_vals[i] != (int8_t)(a_vals[i] + b_vals[i])) return false;
    }
    return true;
}

//****************************************************
//  VPADDw xmm1, xmm2, xmm3

__m128i vpaddw_sse_register(__m128i a, __m128i b) {
    __m128i result;
    __asm__ volatile (
        "vpaddw %2, %1, %0"
        : "=x"(result)        // %0 = xmm1 (output)
        : "x"(a), "x"(b)      // %1 = xmm2, %2 = xmm3
    );
    return result;
}

// Test function for VPADDW register form
bool test_vpaddw_register(__m128i a, __m128i b) {
    int16_t a_vals[8], b_vals[8], result_vals[8];

    __m128i result = vpaddw_sse_register(a, b);

    _mm_storeu_si128((__m128i*)a_vals, a);
    _mm_storeu_si128((__m128i*)b_vals, b);
    _mm_storeu_si128((__m128i*)result_vals, result);

    for (int i = 0; i < 8; i++) {
        if (result_vals[i] != (int16_t)(a_vals[i] + b_vals[i])) {
            return false;
        }
    }
    return true;
}
//****************************************************************
//  VPADDw xmm1, xmm2, m128
static __m128i global_b __attribute__((aligned(16)));

__m128i vpaddw_sse_memory(__m128i a) {
    __m128i result;
    __asm__ volatile (
        "vpaddw %2, %1, %0"
        : "=x"(result)            // %0 = result
        : "x"(a), "m"(global_b)   // %1 = a, %2 = memory (global_b)
    );
    return result;
}

// Test function for VPADDW memory form
bool test_vpaddw_memory(__m128i a, __m128i b) {
    int16_t a_vals[8], b_vals[8], result_vals[8];

    __m128i result = vpaddw_sse_memory(a);

    _mm_storeu_si128((__m128i*)a_vals, a);
    _mm_storeu_si128((__m128i*)b_vals, global_b);
    _mm_storeu_si128((__m128i*)result_vals, result);

    for (int i = 0; i < 8; i++) {
        if (result_vals[i] != (int16_t)(a_vals[i] + b_vals[i])) {
            return false;
        }
    }
    return true;
}

//*************************************************************
// VPADDD xmm1, xmm2, xmm3

__m128i vpaddd_sse_register(__m128i a, __m128i b) {
    __m128i result;
    __asm__ volatile (
        "vpaddd %2, %1, %0"
        : "=x"(result)        // %0 = xmm1 (output)
        : "x"(a), "x"(b)      // %1 = xmm2, %2 = xmm3
    );
    return result;
}

bool test_vpaddd_register(__m128i a, __m128i b) {
    int32_t a_vals[4], b_vals[4], result_vals[4];

    __m128i result = vpaddd_sse_register(a, b);

    _mm_storeu_si128((__m128i*)a_vals, a);
    _mm_storeu_si128((__m128i*)b_vals, b);
    _mm_storeu_si128((__m128i*)result_vals, result);

    for (int i = 0; i < 4; i++) {
        if (result_vals[i] != (int32_t)(a_vals[i] + b_vals[i])) {
            return false;
        }
    }
    return true;
}
//***************************************************************************
// VPADDD xmm1, xmm2, m128
static __m128i global_b __attribute__((aligned(16)));

__m128i vpaddd_sse_memory(__m128i a) {
    __m128i result;
    __asm__ volatile (
        "vpaddd %2, %1, %0"
        : "=x"(result)        // %0 = xmm1 (output)
        : "x"(a), "m"(global_b)   // %1 = xmm2, %2 = m128 (memory)
    );
    return result;
}

bool test_vpaddd_memory(__m128i a) {
    int32_t a_vals[4], b_vals[4], result_vals[4];
   
    __m128i result = vpaddd_sse_memory(a);

    _mm_storeu_si128((__m128i*)a_vals, a);
    _mm_storeu_si128((__m128i*)b_vals, global_b);
    _mm_storeu_si128((__m128i*)result_vals, result);

    for (int i = 0; i < 4; i++) {
        if (result_vals[i] != (int32_t)(a_vals[i] + b_vals[i])) {
            return false;
        }
    }
    return true;
}

//******************************************************
//  VPADDQ xmm1, xmm2, xmm3

__m128i vpaddq_sse_register(__m128i a, __m128i b) {
    __m128i result;
    __asm__ volatile (
        "vpaddq %2, %1, %0"
        : "=x"(result)        // %0 = xmm1 (output/result)
        : "x"(a), "v"(b)      // %1 = xmm2, %2 = xmm3
    );
    return result;
}

// Test function for VPADDQ register form
bool test_vpaddq_register(__m128i a, __m128i b) {
    int64_t a_vals[2], b_vals[2], result_vals[2];

    __m128i result = vpaddq_sse_register(a, b);

    _mm_storeu_si128((__m128i*)a_vals, a);
    _mm_storeu_si128((__m128i*)b_vals, b);
    _mm_storeu_si128((__m128i*)result_vals, result);

    for (int i = 0; i < 2; i++) {
        if (result_vals[i] != (int64_t)(a_vals[i] + b_vals[i])) {
            return false;
        }
    }
    return true;
}

//*****************************************************************************
//  
static __m128i global_b __attribute__((aligned(16)));

__m128i vpaddq_sse_memory(__m128i a) {
    __m128i result;
    __asm__ volatile (
        "vpaddq %2, %1, %0"
        : "=x"(result)        // %0 = xmm1 (output/result)
        : "x"(a), "m"(global_b)   // %1 = xmm2, %2 = m128 memory source
    );
    return result;
}

// Test function for VPADDQ memory form
bool test_vpaddq_memory(__m128i a) {
    int64_t a_vals[2], b_vals[2], result_vals[2];
    

    __m128i result = vpaddq_sse_memory(a);

    _mm_storeu_si128((__m128i*)a_vals, a);
    _mm_storeu_si128((__m128i*)b_vals, global_b);
    _mm_storeu_si128((__m128i*)result_vals, result);

    for (int i = 0; i < 2; i++) {
        if (result_vals[i] != (int64_t)(a_vals[i] + b_vals[i])) {
            return false;
        }
    }
    return true;
}

// dummy main function, to allow us to link the executable
int main () { return 0;}
