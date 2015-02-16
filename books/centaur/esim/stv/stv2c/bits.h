// ESIM Symbolic Hardware Simulator
// Copyright (C) 2008-2015 Centaur Technology
//
// Contact:
//   Centaur Technology Formal Verification Group
//   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
//   http://www.centtech.com/
//
// License: (An MIT/X11-style license)
//
//   Permission is hereby granted, free of charge, to any person obtaining a
//   copy of this software and associated documentation files (the "Software"),
//   to deal in the Software without restriction, including without limitation
//   the rights to use, copy, modify, merge, publish, distribute, sublicense,
//   and/or sell copies of the Software, and to permit persons to whom the
//   Software is furnished to do so, subject to the following conditions:
//
//   The above copyright notice and this permission notice shall be included in
//   all copies or substantial portions of the Software.
//
//   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
//   THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.
//
// bits.h -- Arbitrary (but fixed) bit<n> datatype
// Original author: Nikhil Patil <npatil@centtech.com>

// WARNING: much of this code hasn't been tested very well, yet.

#pragma once

#include <cstring>
#include <cstdlib>
#include <cctype>
#include <cstdio>
#include <climits>
#include <cinttypes>
#include <cerrno>

#include <initializer_list>

#if !defined(attest)
#include <cassert>
#define attest assert
#endif

#if !defined(STATIC_ASSERT)
#define STATIC_ASSERT(x) static_assert(x, #x)
#endif

namespace conf_ {
    static const bool debugBits = 0;
}

namespace bits {
    constexpr
    uint64_t ilog2(uint64_t n) {
        return n == 0 ? ULLONG_MAX : n == 1 ? 0 : ilog2(n >> 1) + 1;
    }
    constexpr
    uint64_t lg(uint64_t n) { // iceillog2
        return n == 1 ? 0 : ilog2(n - 1) + 1;
    }
}
using bits::lg;

static inline
unsigned popcount(uint32_t x)
{
    return (unsigned) __builtin_popcount(x);
}
static inline
unsigned popcount(uint64_t x)
{
    return (unsigned) __builtin_popcountll(x);
}

static inline
unsigned countLeadingZeroes(uint32_t x)
{
    return (unsigned) __builtin_clz(x);
}
static inline
unsigned countLeadingZeroes(uint64_t x)
{
    return (unsigned) __builtin_clzll(x);
}

static inline
unsigned countTrailingZeroes(uint32_t x)
{
    return (unsigned) __builtin_ctz(x);
}
static inline
unsigned countTrailingZeroes(uint64_t x)
{
    return (unsigned) __builtin_ctzll(x);
}

// Prim<N> chooses the primitive type big enough to fit N bits; but if N > 64, it picks uint64_t
template <bool g64, bool g32, bool g16, bool g8>
struct Prim_;

template <unsigned n>
using Prim = typename Prim_<(n > 64), (n > 32), (n > 16), (n > 8)>::type;

template <>
struct Prim_<0,0,0,0> {
    typedef uint8_t type;
};
template <>
struct Prim_<0,0,0,1> {
    typedef uint16_t type;
};
template <>
struct Prim_<0,0,1,1> {
    typedef uint32_t type;
};
template <bool g64>
struct Prim_<g64,1,1,1> {
    //// static_assert (!g64, "Prim<N> not defined for N > 64");
    typedef uint64_t type;
};

// bit<N> is an N-bit type
template <unsigned N, bool g64>
class BV;

template <unsigned N>
using bit = BV<N, (N>64)>;

// bit<0>
template <>
class BV<0,0>
{
  public:

    // constructor
    BV<0,0>() = default;
    BV<0,0>(const BV<0,0> &) = default;

    static bit<0> zero() {
        return bit<0>();
    }

    // parse
    void parseVBin(const char *s) {
        attest (*s == 0);
    }
    void parseHexBytes(const char *s) {
        attest (*s == 0);
    }
    void parseHexWords(const char *s) {
        attest (*s == 0);
    }
    size_t parseHexLong(const char *s) {
        attest (*s == 0);
        return 0;
    }

    // cast
    // raw pointer access
    uint8_t *raw() {
        return nullptr;
    }

    // normalization
    bit<0> &normalize() { return *this; }
    bool isNormal() { return true; }
    void assertNormal() const { }

    // comparison
    bool operator ==(const bit<0> &) { return true;  }
    bool operator !=(const bit<0> &) { return false; }
    bool operator < (const bit<0> &) { return false; }
    bool operator > (const bit<0> &) { return false; }
    bool operator <=(const bit<0> &) { return true;  }
    bool operator >=(const bit<0> &) { return true;  }

    // bitwise
    bit<0> operator ~()               const { return bit<0>(); }
    bit<0> operator &(const bit<0> &) const { return bit<0>(); }
    bit<0> operator |(const bit<0> &) const { return bit<0>(); }
    bit<0> operator ^(const bit<0> &) const { return bit<0>(); }

    // bitwise assignment
    bit<0> &operator &=(const bit<0> &) { return *this; }
    bit<0> &operator |=(const bit<0> &) { return *this; }
    bit<0> &operator ^=(const bit<0> &) { return *this; }

    // bit-select
    template <typename T> bool    operator [](T) const { return false; }
    template <typename T> bool    getBit     (T) const { return false; }
    template <typename T> bit<0> &setBit     (T)       { return *this; }
    template <typename T> bit<0> &clrBit     (T)       { return *this; }
    template <typename T> bit<0> &cpyBit     (T, bool) { return *this; }

    signed int lsbIndex() const { return -1; }
    unsigned   popcount() const { return  0; }
    unsigned   popcountGt(unsigned) const { return false; }

    // shift
    // arithmetic

    // extension
    bit<0> truncate() {
        return bit<0>();
    }
    template <unsigned M>
        bit<M> extend() const {
            return bit<M>::zero();
        }
};

// bit<N> where 1 <= N <= 64
template <unsigned N>
class BV<N,0>
{
    STATIC_ASSERT (N > 0 && N <= 64);

    // use a primitive type, with appropriate masking
    Prim<N> val;

    constexpr static Prim<N> mask = N == 64 ? ~uint64_t(0) : (uint64_t(1) << N) - 1;

  public:
    // constructor
    BV<N,0>() = default;
    BV<N,0>(const BV<N,0> &) = default;

    BV<N,0>(Prim<N> x) : val(x) { // convenient conversion from underlying primitive type
    }

    static bit<N> zero() {
        return 0;
    }

    // parse
    void parseVBin(const char *s) {
        val = 0;
        unsigned n = strlen(s);
        attest (n <= N);
        Prim<N> j = 1;
        while (n--) {
            attest (!!strchr("01xz", s[n]));
            if (s[n] == '1')
                val |= j;
            j <<= 1;
        }
        attestNormal();
    }

    void parseHexBytes(const char *s) {
        val = 0;
        const char *p = s;
        uint8_t *ptr = raw();
        for (unsigned i = 0; i < (N + 7) / 8; ++i) {
            char *endp;
            unsigned long c = strtoul(p, &endp, 16); // this eats white-space
            attest (c <= 255);
            p = endp;
            ptr[i] = uint8_t(c);
        }
        while (isspace(*p))
            ++p;
        attest (*p == '\0');
        attestNormal();
    }

    void parseHexWords(const char *s) {
        auto x = strtoull(s, nullptr, 16);
        assert (errno == 0 && "strtoull failed");
        val = Prim<N>(x);
        attestNormal();
    }

    size_t parseHexLong(const char *s) {
        char *endp;
        auto x = strtoull(s, &endp, 16);
        assert (errno == 0 && "strtoull failed");
        val = Prim<N>(x);
        attestNormal();
        return size_t(endp - s);
    }

    // cast
    // conversion to the underlying primitive type is allowed but must be explicit,
    // since it loses mask information
    explicit operator Prim<N>() const {
        return val;
    }

    // raw pointer access
    uint8_t *raw() {
        return reinterpret_cast<uint8_t *>(&val);
    }

    // normalization
    bit<N> &normalize() {
        val &= mask;
        return *this;
    }
    bool isNormal() const {
        return 0 == (val & ~mask);
    }
    void assertNormal() const {
        if (conf_::debugBits && !isNormal()) {
            printf("bit<%d> %16lx\n", N, uint64_t(val));
            assert (0 && "assertNormal");
        }
    }
    void attestNormal() const {
        if (!isNormal()) {
            printf("bit<%d> %16lx\n", N, uint64_t(val));
            attest (0 && "attestNormal");
        }
    }

    // comparison
    bool operator ==(const bit<N> &that) const { return val == that.val; }
    bool operator !=(const bit<N> &that) const { return val != that.val; }
    bool operator < (const bit<N> &that) const { return val <  that.val; }
    bool operator > (const bit<N> &that) const { return val >  that.val; }
    bool operator <=(const bit<N> &that) const { return val <= that.val; }
    bool operator >=(const bit<N> &that) const { return val >= that.val; }

    // bitwise
    bit<N> operator ~() const { return bit<N>(~val).normalize(); }
    bit<N> operator &(const bit<N> &that) const { return bit<N>(val & that.val); }
    bit<N> operator |(const bit<N> &that) const { return bit<N>(val | that.val); }
    bit<N> operator ^(const bit<N> &that) const { return bit<N>(val ^ that.val); }

    // bitwise assignment
    bit<N> &operator &=(const bit<N> &that) { val &= that.val; return *this; }
    bit<N> &operator |=(const bit<N> &that) { val |= that.val; return *this; }
    bit<N> &operator ^=(const bit<N> &that) { val ^= that.val; return *this; }

    // bit-select
    template <typename T>
        bool operator [](T idx) const { return getBit(idx); }

    bool getBit(uint8_t idx) const {
        assert (idx < N);
        return val >> idx & 1;
    }
    bool getBit(bit<lg(N)> idx) const { return getBit(uint8_t(idx)); }
    bool getBit(uint16_t idx)   const { return getBit(uint8_t(idx)); }
    bool getBit(uint32_t idx)   const { return getBit(uint8_t(idx)); }
    bool getBit( int32_t idx)   const { return getBit(uint8_t(idx)); }
    bool getBit(uint64_t idx)   const { return getBit(uint8_t(idx)); }

    bit<N> &setBit(uint8_t idx) {
        assert (idx < N);
        val |= Prim<N>(1) << idx;
        return *this;
    }
    bit<N> &setBit(bit<lg(N)> idx) { return setBit(uint8_t(idx)); }
    bit<N> &setBit(uint16_t idx)   { return setBit(uint8_t(idx)); }
    bit<N> &setBit(uint32_t idx)   { return setBit(uint8_t(idx)); }
    bit<N> &setBit( int32_t idx)   { return setBit(uint8_t(idx)); }
    bit<N> &setBit(uint64_t idx)   { return setBit(uint8_t(idx)); }

    bit<N> &clrBit(uint8_t idx) {
        assert (idx < N);
        val &= ~(Prim<N>(1) << idx);
        return *this;
    }
    bit<N> &clrBit(bit<lg(N)> idx) { return clrBit(uint8_t(idx)); }
    bit<N> &clrBit(uint16_t idx)   { return clrBit(uint8_t(idx)); }
    bit<N> &clrBit(uint32_t idx)   { return clrBit(uint8_t(idx)); }
    bit<N> &clrBit( int32_t idx)   { return clrBit(uint8_t(idx)); }
    bit<N> &clrBit(uint64_t idx)   { return clrBit(uint8_t(idx)); }

    bit<N> &cpyBit(uint32_t idx, bool p) {
        assert (idx < N);
        val &= ~(Prim<N>(1) << idx);
        val |=   Prim<N>(p) << idx;
        return *this;
    }
    bit<N> &cpyBit(bit<lg(N)> idx, bool p) { return cpyBit(uint32_t(idx), p); }
    bit<N> &cpyBit( uint8_t idx, bool p)   { return cpyBit(uint32_t(idx), p); }
    bit<N> &cpyBit(uint16_t idx, bool p)   { return cpyBit(uint32_t(idx), p); }
    bit<N> &cpyBit( int32_t idx, bool p)   { return cpyBit(uint32_t(idx), p); }
    bit<N> &cpyBit(uint64_t idx, bool p)   { return cpyBit(uint32_t(idx), p); }

    signed int lsbIndex() const {
        if (val == 0)
            return -1;
        return (signed) ::countTrailingZeroes(val);
    }

    unsigned popcount() const {
        return ::popcount(val);
    }
    unsigned popcountGt(unsigned n) const {
        return popcount() > n;
    }

    // logical shift
    bit<N> operator >>(uint8_t amt) const {
        assertNormal();
        return bit<N>(val >> amt);
    }
    bit<N> operator >>(bit<lg(N)> amt) const { return *this >> uint8_t(amt); }
    bit<N> operator >>(uint16_t amt)   const { return *this >> uint8_t(amt); }
    bit<N> operator >>(uint32_t amt)   const { return *this >> uint8_t(amt); }
    bit<N> operator >>(uint64_t amt)   const { return *this >> uint8_t(amt); }
    bit<N> operator >>(int amt)        const { assert (amt >= 0); return *this >> uint8_t(amt); }

    bit<N> operator <<(uint8_t amt) const { // loses most significant bits
        return bit<N>(val << amt).normalize();
    }

    bit<N> operator <<(bit<lg(N)> amt) const { return *this << uint8_t(amt); }
    bit<N> operator <<(uint16_t amt)   const { return *this << uint8_t(amt); }
    bit<N> operator <<(uint32_t amt)   const { return *this << uint8_t(amt); }
    bit<N> operator <<(uint64_t amt)   const { return *this << uint8_t(amt); }
    bit<N> operator <<(int amt)        const { assert (amt >= 0); return *this << uint8_t(amt); }

    // arithmetic
    bit<N> operator +(const bit<N> &that) const { return bit<N>(val + that.val).normalize(); }
    bit<N> operator -(const bit<N> &that) const { return bit<N>(val - that.val).normalize(); }
    bit<N> operator %(unsigned x)         const { return bit<N>(val % x); }

    // arithmetic assignment
    BV<N,false> &operator ++() { ++val; return normalize(); }

    // extension
    template <unsigned M>
        bit<M> truncate() const {
            STATIC_ASSERT (M <= N);
            return bit<M>(Prim<M>(val)).normalize();
        }

    template <unsigned M>
        bit<M> extend() const {
            STATIC_ASSERT (M >= N);
            return extend_<M,(M>64)>::call(*this);
        }

  private:
    template <unsigned M, bool g64>
        struct extend_ {
            bit<M> static call(const bit<N> &x);
        };

    template <unsigned M>
        struct extend_<M,0> {
            bit<M> static call(const bit<N> &x) {
                x.assertNormal();
                return bit<M>(x.val);
            }
        };

    template <unsigned M>
        struct extend_<M,1> {
            bit<M> static call(const bit<N> &x) {
                x.assertNormal();
                auto w = bit<M>::zero();
                w.arr[0] = x.val;
                return w;
            }
        };
}
__attribute__((packed));

// bit<N> where N > 64
template <unsigned N>
class BV<N,1>
{
    STATIC_ASSERT (N > 64);
    constexpr static uint64_t mask = N % 64 == 0 ? ~uint64_t(0) : (uint64_t(1) << (N % 64)) - 1;
  public:
    constexpr static unsigned K = (N + 63) / 64;
    STATIC_ASSERT (K >= 1);

    // arr[K-1] could be replaced by bit<N % 64>, but that would make words in
    // an array of bit<N> unaligned.
    uint64_t arr[K];

    // constructor
    BV<N,1>() = default;
    BV<N,1>(const BV<N,1> &) = default;

    explicit BV<N,1>(uint64_t x) : arr{x} { }
    template <typename... T>
    explicit BV<N,1>(uint64_t x, T... xs) : arr{x, xs...} { }

    // template <typename... T>
    //     BV<N,1>(T... xs) : arr{xs...} {
    //     }

    void mkzero() { // make *this zero
        for (unsigned i = 0; i < K; ++i)
            arr[i] = 0;
    }
    static bit<N> zero() {
        bit<N> w;
        w.mkzero();
        return w;
    }

    // parse
    void parseVBin(const char *s) {
        mkzero();
        unsigned n = strlen(s);
        attest (n <= N);

        unsigned k = 0;
        uint64_t j = 1;
        while (n--) {
            attest (!!strchr("01xz", s[n]));
            if (s[n] == '1')
                arr[k] |= j;
            j <<= 1;
            if (j == 0) {
                j = 1;
                k++;
            }
        }
        attestNormal();
    }

    // white-space separated hex bytes; Lo to Hi
    void parseHexBytes(const char *s) {
        normalize();
        const char *p = s;
        uint8_t *ptr = raw();
        for (unsigned i = 0; i < (N + 7) / 8; ++i) {
            char *endp;
            unsigned long c = strtoul(p, &endp, 16); // this eats white-space
            attest (c <= 255);
            p = endp;
            ptr[i] = uint8_t(c);
        }
        while (isspace(*p))
            ++p;
        attest (*p == '\0');
        attestNormal();
    }


    // white-space separated hex words; Lo to Hi
    void parseHexWords(const char *s) {
        const char *p = s;
        for (unsigned i = 0; i < K; ++i) {
            char *endp;
            arr[i] = strtoull(p, &endp, 16); // this eats white-space
            assert (errno == 0 && "strtoull failed");
            p = endp;
        }
        while (isspace(*p))
            ++p;
        attest (*p == '\0');
        attestNormal();
    }

    // single looong word, msb first lsb last
    size_t parseHexLong(const char *s) {
        mkzero();
        assert (!(s[0] == '0' && s[1] == 'x') && "parseHexLong cannot deal with 0x prefix");

        unsigned n = (unsigned) strspn(s, "0123456789abcdefABCDEF");
        attest (n <= (N + 3) / 4);

        unsigned k = 0;
        uint64_t j = 0;

        while (n) {
            n--;
            char c = s[n];
            uint64_t x = (c & 0xf) + (c > '9' ? 9 : 0);
            arr[k] |= x << j;
            j += 4;
            if (j == 64) {
                j = 0;
                k++;
            }
        }
        attestNormal();
        return n; // returns how many bytes were used
    }

    // cast

    // raw pointer access
    uint8_t *raw() {
        return reinterpret_cast<uint8_t *>(arr);
    }
    const uint8_t *raw() const {
        return reinterpret_cast<const uint8_t *>(arr);
    }
    // raw word access
    uint64_t &word(unsigned i) { return arr[i]; }
    uint64_t  word(unsigned i) const { return arr[i]; }

    // normalization
    bit<N> &normalize() {
        arr[K-1] &= mask;
        return *this;
    }
    bool isNormal() const {
        return 0 == (arr[K-1] & ~mask);
    }
    void assertNormal() const {
        if (conf_::debugBits && !isNormal()) {
            printf("bit<%d>", N);
            for (unsigned i = 0; i < K; ++i)
                printf(" %016lx", arr[i]);
            printf("\n");
            assert (0 && "assertNormal");
        }
    }
    void attestNormal() const {
        if (!isNormal()) {
            printf("bit<%d>", N);
            for (unsigned i = 0; i < K; ++i)
                printf(" %016lx", arr[i]);
            printf("\n");
            attest (0 && "attestNormal");
        }
    }

    // comparison
    bool operator ==(const bit<N> &that) const {
        assertNormal(); that.assertNormal();
        for (unsigned i = 0; i < K; ++i)
            if (arr[i] != that.arr[i])
                return false;
        return true;
    }
    bool operator !=(const bit<N> &that) const {
        return !(*this == that);
    }

    // bitwise
    bit<N> operator ~() const {
        bit<N> w;
        for (unsigned i = 0; i < K; ++i)
            w.arr[i] = ~arr[i];
        return w.normalize();
    }
    bit<N> operator &(const bit<N> &that) const {
        bit<N> w;
        for (unsigned i = 0; i < K; ++i)
            w.arr[i] = arr[i] & that.arr[i];
        return w;
    }
    bit<N> operator |(const bit<N> &that) const {
        bit<N> w;
        for (unsigned i = 0; i < K; ++i)
            w.arr[i] = arr[i] | that.arr[i];
        return w;
    }
    bit<N> operator ^(const bit<N> &that) const {
        bit<N> w;
        for (unsigned i = 0; i < K; ++i)
            w.arr[i] = arr[i] ^ that.arr[i];
        return w;
    }

    // bitwise assignment
    bit<N> &operator &=(const bit<N> &that) {
        for (unsigned i = 0; i < K; ++i)
            arr[i] &= that.arr[i];
        return *this;
    }
    bit<N> &operator |=(const bit<N> &that) {
        for (unsigned i = 0; i < K; ++i)
            arr[i] |= that.arr[i];
        return *this;
    }
    bit<N> &operator ^=(const bit<N> &that) {
        for (unsigned i = 0; i < K; ++i)
            arr[i] ^= that.arr[i];
        return *this;
    }

    // bit-select
    template <typename T>
        bool operator [](T idx) const { return getBit(idx); }

    bool getBit(uint32_t idx) const {
        assert (idx < N);
        auto q = idx / 64;
        auto r = idx % 64;
        return arr[q] >> r & 1;
    }
    bool getBit(bit<lg(N)> idx) const { return getBit(uint32_t(idx)); }
    bool getBit( uint8_t idx)   const { return getBit(uint32_t(idx)); }
    bool getBit(uint16_t idx)   const { return getBit(uint32_t(idx)); }
    bool getBit( int32_t idx)   const { return getBit(uint32_t(idx)); }
    bool getBit(uint64_t idx)   const { return getBit(uint32_t(idx)); }

    bit<N> &setBit(uint32_t idx) {
        assert (idx < N);
        auto q = idx / 64;
        auto r = idx % 64;
        arr[q] |= uint64_t(1) << r;
        return *this;
    }
    bit<N> &setBit(bit<lg(N)> idx) { return setBit(uint32_t(idx)); }
    bit<N> &setBit( uint8_t idx)   { return setBit(uint32_t(idx)); }
    bit<N> &setBit(uint16_t idx)   { return setBit(uint32_t(idx)); }
    bit<N> &setBit( int32_t idx)   { return setBit(uint32_t(idx)); }
    bit<N> &setBit(uint64_t idx)   { return setBit(uint32_t(idx)); }

    bit<N> &clrBit(uint32_t idx) {
        assert (idx < N);
        auto q = idx / 64;
        auto r = idx % 64;
        arr[q] &= ~(uint64_t(1) << r);
        return *this;
    }
    bit<N> &clrBit(bit<lg(N)> idx) { return clrBit(uint32_t(idx)); }
    bit<N> &clrBit( uint8_t idx)   { return clrBit(uint32_t(idx)); }
    bit<N> &clrBit(uint16_t idx)   { return clrBit(uint32_t(idx)); }
    bit<N> &clrBit( int32_t idx)   { return clrBit(uint32_t(idx)); }
    bit<N> &clrBit(uint64_t idx)   { return clrBit(uint32_t(idx)); }

    bit<N> &cpyBit(uint32_t idx, bool p) {
        assert (idx < N);
        auto q = idx / 64;
        auto r = idx % 64;
        arr[q] &= ~(uint64_t(1) << r);
        arr[q] |=   uint64_t(p) << r;
        return *this;
    }
    bit<N> &cpyBit(bit<lg(N)> idx, bool p) { return cpyBit(uint32_t(idx), p); }
    bit<N> &cpyBit( uint8_t idx, bool p)   { return cpyBit(uint32_t(idx), p); }
    bit<N> &cpyBit(uint16_t idx, bool p)   { return cpyBit(uint32_t(idx), p); }
    bit<N> &cpyBit( int32_t idx, bool p)   { return cpyBit(uint32_t(idx), p); }
    bit<N> &cpyBit(uint64_t idx, bool p)   { return cpyBit(uint32_t(idx), p); }

    signed int lsbIndex() {
        for (unsigned i = 0; i < K; ++i) {
            uint64_t x = arr[i];
            if (x)
                return (signed) (64 * i + ::countTrailingZeroes(x));
        }
        return -1;
    }

    unsigned popcount() const {
        unsigned x = 0;
        for (unsigned i = 0; i < K; ++i)
            x += ::popcount(arr[i]);
        return x;
    }
    unsigned popcountGt(unsigned n) const { // not sure if this is faster than: popcount() > n
        unsigned x = 0;
        for (unsigned i = 0; i < K; ++i) {
            x += ::popcount(arr[i]);
            if (x > n)
                return true;
        }
        return false;
    }

    // logical shift
    bit<N> operator >>(unsigned amt) const {
        assertNormal();

        auto q = amt / 64;
        auto r = amt % 64;
        bit<N> w;

        if (q >= K) {
            w.mkzero();
            return w;
        }

        for (unsigned i = 0; i+q+1 < K; ++i) {
            if (r == 0)
                w.arr[i] = arr[i+q];
            else
                w.arr[i] = arr[i+q] >> r | arr[i+q+1] << (64 - r);
        }

        w.arr[K-q-1] = arr[K-1] >> r;

        for (unsigned i = K - q; i < K; ++i)
            w.arr[i] = 0;

        w.assertNormal();
        return w;
    }

    bit<N> operator >>(bit<lg(N)> amt) const { return *this >> uint32_t(amt); }
    bit<N> operator >>(uint8_t  amt)   const { return *this >> uint32_t(amt); }
    bit<N> operator >>(uint16_t amt)   const { return *this >> uint32_t(amt); }
    bit<N> operator >>(uint64_t amt)   const { return *this >> uint32_t(amt); }
    bit<N> operator >>(int amt)        const { assert (amt >= 0); return *this >> uint32_t(amt); }

    bit<N> operator <<(unsigned amt) const {
        auto q = amt / 64;
        auto r = amt % 64;
        bit<N> w;

        if (q >= K) {
            w.mkzero();
            return w;
        }

        for (unsigned i = 0; i < q; ++i)
            w.arr[i] = 0;

        w.arr[q] = arr[0] << r;

        for (unsigned i = q + 1; i < K; ++i) {
            if (r == 0)
                w.arr[i] = arr[i-q];
            else
                w.arr[i] = arr[i-q] << r | arr[i-q-1] >> (64 - r);
        }

        return w.normalize();
    }

    bit<N> operator <<(bit<lg(N)> amt) const { return *this << uint32_t(amt); }
    bit<N> operator <<(uint8_t  amt)   const { return *this << uint32_t(amt); }
    bit<N> operator <<(uint16_t amt)   const { return *this << uint32_t(amt); }
    bit<N> operator <<(uint64_t amt)   const { return *this << uint32_t(amt); }
    bit<N> operator <<(int amt)        const { assert (amt >= 0); return *this << uint32_t(amt); }

    // extension
    template <unsigned M>
        bit<M> truncate() const {
            STATIC_ASSERT (M <= N);
            return truncate_<M,(M>64)>::call(*this);
        }

    template <unsigned M>
        bit<M> extend() const {
            STATIC_ASSERT (M >= N);
            assertNormal();
            bit<M> w;
            unsigned i;
            for (i = 0; i < K; ++i)
                w.arr[i] = arr[i];
            for (; i < bit<M>::K; ++i)
                w.arr[i] = 0;
            w.assertNormal();
            return w;
        }

  private:
    template <unsigned M, bool g64>
        struct truncate_ {
            bit<M> static call(const bit<N> &x);
        };

    template <unsigned M>
        struct truncate_<M,0> {
            bit<M> static call(const bit<N> &x) {
                return bit<M>(Prim<M>(x.arr[0])).normalize();
            }
        };

    template <unsigned M>
        struct truncate_<M,1> {
            bit<M> static call(const bit<N> &x) {
                bit<M> w;
                for (unsigned i = 0; i < bit<M>::K; ++i)
                    w.arr[i] = x.arr[i];
                return w.normalize();
            }
        };

}
__attribute__((packed));


namespace bits {
    template <typename T>
        struct BitSizeOf {
            static constexpr size_t value = sizeof (T) * 8;
        };

    template <>
        struct BitSizeOf<bool> {
            static constexpr size_t value = 1;
        };

    template <unsigned N>
        struct BitSizeOf<bit<N>> {
            static constexpr size_t value = N;
        };
}

template <typename T>
constexpr size_t bitSizeOf(const T &) {
    return bits::BitSizeOf<T>::value;
}
template <typename T>
constexpr size_t bitSizeOf() {
    return bits::BitSizeOf<T>::value;
}
