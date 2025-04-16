#ifndef UTILS_H
#define UTILS_H

#include <cassert>
#include <cstring>
#include <deque>
#include <limits>
#include <memory>
#include <ostream>
#include <sstream>
#include <tuple>
#include <vector>

#define UNREACHABLE() assert(!"Woopsie, some unreachable code was reach")

#define STRONGTYPEDEF(BASE, TYPE)                                              \
  struct TYPE {                                                                \
    TYPE() = default;                                                          \
    TYPE(BASE v) : value(v) {}                                                 \
    TYPE(const TYPE &v) = default;                                             \
    TYPE &operator=(const TYPE &rhs) = default;                                \
    TYPE &operator=(BASE &rhs) {                                               \
      value = rhs;                                                             \
      return *this;                                                            \
    }                                                                          \
    operator BASE &() { return value; }                                        \
    BASE value;                                                                \
    using BaseType = BASE;                                                     \
  }

template <class... Ts> struct overloaded : Ts... {
  using Ts::operator()...;
};
// explicit deduction guide (not needed as of C++20)
template <class... Ts> overloaded(Ts...) -> overloaded<Ts...>;

// Check if the pointer elm is of type T. T and U should be both a pointer
// type. If both are the type but one if const (or volatile) and not the other
// this will return false. Maybe this behavior should be modified ?
template <typename T, typename U> inline bool isa(U elm) {
  return dynamic_cast<T>(elm);
}

// Alaways cast elem from type U to T where U is a base of T.
template <typename T, typename U> inline T always_cast(U elm) {
  auto t = dynamic_cast<T>(elm);
  assert(t && "Invalid conversion");
  return t;
}

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wformat-security"

template <typename... Args>
std::string format(const std::string &format, Args... args) {

  // Compute size of string.
  int size = std::snprintf(nullptr, 0, format.c_str(), args...) + 1;

  assert(size >= 0 && "Error during formatting");

  std::unique_ptr<char[]> buf(new char[(size_t)size]);
  std::snprintf(buf.get(), size, format.c_str(), args...);
  return std::string(buf.get(),
                     buf.get() + size - 1); // We don't want the '\0' inside
}

#pragma GCC diagnostic pop

class BigInt {
public:
  BigInt(int val)
      : abs_val_(std::abs(static_cast<long>(val))), sign_(val < 0) {}
  BigInt(unsigned int val) : abs_val_(val), sign_(false) {}
  BigInt(long val) : abs_val_(std::abs(val)), sign_(val < 0) {}
  BigInt(unsigned long val) : abs_val_(val), sign_(false) {}

  BigInt(unsigned long abs_val, bool sign) : abs_val_(abs_val), sign_(sign) {}

  BigInt &operator=(long val) {
    abs_val_ = std::abs(val);
    sign_ = val < 0;
    return *this;
  }
  BigInt &operator=(unsigned long val) {
    abs_val_ = val;
    sign_ = false;
    return *this;
  }

  bool operator==(const BigInt &other) const { return cmp(other) == 0; }
  bool operator>=(const BigInt &other) const { return cmp(other) >= 0; }
  bool operator<=(const BigInt &other) const { return cmp(other) <= 0; }
  bool operator>(const BigInt &other) const { return cmp(other) > 0; }
  bool operator<(const BigInt &other) const { return cmp(other) < 0; }

  // TODO remove
  int eval() const {
    assert(abs_val_ < std::numeric_limits<int>::max());
    return (sign_ ? -1 : 1) * abs_val_;
  }

  template <typename T> bool can_fit_inside() const {
    return *this <= std::numeric_limits<T>::max() &&
           *this >= std::numeric_limits<T>::min();
  }

  bool can_fit_inside(bool sign, unsigned width) const {

    BigInt max_value((1ULL << (width - sign)) - 1, false);
    BigInt min_value(sign ? (1ULL << (width - 1)) : 0, sign);

    return *this <= max_value && *this >= min_value;
  }

  friend std::string to_string(const BigInt &n);

private:
  // returns
  //  1 if this > other
  //  0 if this == other
  // -1 if this < other
  int cmp(const BigInt &other) const {

    if (sign_ && !other.sign_) {
      return -1;
    }

    if (!sign_ && other.sign_) {
      return 1;
    }

    if (abs_val_ == other.abs_val_) {
      return 0;
    }

    if (sign_) {
      return abs_val_ > other.abs_val_ ? -1 : 1;
    } else {
      return abs_val_ > other.abs_val_ ? 1 : -1;
    }
  }

  unsigned long abs_val_;
  bool sign_;
};

inline std::string to_string(const BigInt &n) {
  std::stringstream ss;
  if (n.sign_) {
    ss << '-';
  }
  ss << n.abs_val_;
  return ss.str();
}

template <typename T, typename U> class Zip {

public:
  using T_it = decltype(std::declval<T>().begin());
  using U_it = decltype(std::declval<U>().begin());

  class Iterator {
  public:
    using reference =
        std::pair<typename T_it::reference, typename U_it::reference>;

    explicit Iterator(T_it itT, U_it itU) : curT_(itT), curU_(itU) {}

    Iterator &operator++() {
      curT_++;
      curU_++;
      return *this;
    }

    bool operator==(Iterator other) const {
      return curT_ == other.curT_ && curU_ == other.curU_;
    }
    bool operator!=(Iterator other) const { return !(*this == other); }

    reference operator*() const { return {*curT_, *curU_}; }

  private:
    T_it curT_;
    U_it curU_;
  };

  Zip(T &t, U &u) : begin_(t.begin(), u.begin()), end_(t.end(), u.end()) {}
  Iterator begin() { return begin_; }
  Iterator end() { return end_; }

private:
  Iterator begin_, end_;
};

// template <typename T, typename F>
// class LazyTransform {
// public:
//  using T_it = decltype(std::declval<T>().begin());
//
//  class Iterator {
//  public:
//    using value = typename T_it::value_type;
//    using reference = value &;
//
//    explicit Iterator(T_it itT, F f) : curT_(itT), f_(f) {}
//
//    Iterator &operator++() {
//      curT_++;
//      return *this;
//    }
//
//    bool operator==(Iterator other) const { return curT_ == other.curT_; }
//    bool operator!=(Iterator other) const { return !(*this == other); }
//
//    value operator*() const { return f_(*curT_); }
//
//  private:
//    T_it curT_;
//    F f_;
//  };
//
//  LazyTransform(T &t, F f) : begin_(t.begin(), f), end_(t.end(), f) {}
//  Iterator begin() { return begin_; }
//  Iterator end() { return end_; }
//
// private:
//  Iterator begin_, end_;
//};

#endif // UTILS_H
