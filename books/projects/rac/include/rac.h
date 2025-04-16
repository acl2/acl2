// ---------------------------------------------------------------------------
// Array and tuple classes (bare bones version).
//
// RAC uses the C++11 array and tuple classes. Not all commercial EDA tools
// support C++11, unfortunately. Synopsys Hector does not, nor does Cadence
// C2S, and I suspect most other high level synthesis tools don't either.
//
// The classes defined below are sufficient for RAC and also work with
// Hector and C2S. They are intended to be compatible with C++11.
// ---------------------------------------------------------------------------

#ifndef RAC_H
#define RAC_H

#include <cassert>
#include <ostream>

typedef unsigned int uint;

#ifdef __cpp_static_assert
static_assert(sizeof(int) == 4, "int is not exactly 32 bits.");
static_assert(sizeof(unsigned int) == 4, "uint is not exactly 32 bits.");
static_assert(sizeof(long) == 8, "int64 is not 64 exactly bits.");
static_assert(sizeof(unsigned long) == 8, "int64 is not 64 exactly bits.");
#endif

// Do we support C++11 ? If so don't redefine array and tuple.
#if __cplusplus > 199711L

#include <array>
#include <tuple>

#else

// ---------------------------------------------------------------------------
// Templates for passing and returning arrays
// ---------------------------------------------------------------------------

template <class T, uint m> class array {
  T elt[m];

public:
  T &operator[](int idx) {
    assert(idx >= 0 && idx < m && "Out of bounds access !");
    return elt[idx];
  }

  std::ostream &dump(std::ostream &os) {
    os << "{";
    for (int i = 0; i < m; i++) {
      if (0 < i)
        os << ", ";
      os << elt[i];
    }
    return os << "}";
  }
};

template <class T, uint m>
std::ostream &operator<<(std::ostream &os, array<T, m> src) {
  return src.dump(os);
}

// ---------------------------------------------------------------------------
// Templates for passing & returning tuples
// ---------------------------------------------------------------------------

// null type
struct null_type {};

std::ostream &operator<<(std::ostream &os, const null_type) {
  return os << "-";
}

// a global to absorb "writes" to unused tuple fields.
// would be good to get rid of this.
null_type dummy;

template <class T0 = null_type, class T1 = null_type, class T2 = null_type,
          class T3 = null_type, class T4 = null_type, class T5 = null_type,
          class T6 = null_type, class T7 = null_type>
class ltuple;

template <class T0 = null_type, class T1 = null_type, class T2 = null_type,
          class T3 = null_type, class T4 = null_type, class T5 = null_type,
          class T6 = null_type, class T7 = null_type>
class tuple {
  T0 el0;
  T1 el1;
  T2 el2;
  T3 el3;
  T4 el4;
  T5 el5;
  T6 el6;
  T7 el7;

public:
  typedef tuple<T0, T1, T2, T3, T4, T5, T6, T7> this_t;
  friend this_t ltuple<T0, T1, T2, T3, T4, T5, T6, T7>::operator=(this_t);

  std::ostream &dump(std::ostream &os) {
    return os << "(" << el0 << "," << el1 << "," << el2 << "," << el3 << ","
              << el4 << "," << el5 << "," << el6 << "," << el7,
           ")";
  }

  tuple(T0 t0, T1 t1 = dummy, T2 t2 = dummy, T3 t3 = dummy, T4 t4 = dummy,
        T5 t5 = dummy, T6 t6 = dummy, T7 t7 = dummy)
      : el0(t0), el1(t1), el2(t2), el3(t3), el4(t4), el5(t5), el6(t6), el7(t7) {
  }
};

template <class T0, class T1, class T2, class T3, class T4, class T5, class T6,
          class T7>
std::ostream &operator<<(std::ostream &os,
                         tuple<T0, T1, T2, T3, T4, T5, T6, T7> src) {
  return src.dump(os);
}

template <class T0, class T1, class T2, class T3, class T4, class T5, class T6,
          class T7>
class ltuple {
private:
  T0 &el0;
  T1 &el1;
  T2 &el2;
  T3 &el3;
  T4 &el4;
  T5 &el5;
  T6 &el6;
  T7 &el7;

public:
  ltuple(T0 &t0, T1 &t1 = dummy, T2 &t2 = dummy, T3 &t3 = dummy, T4 &t4 = dummy,
         T5 &t5 = dummy, T6 &t6 = dummy, T7 &t7 = dummy)
      : el0(t0), el1(t1), el2(t2), el3(t3), el4(t4), el5(t5), el6(t6), el7(t7) {
  }

  tuple<T0, T1, T2, T3, T4, T5, T6, T7>
  operator=(tuple<T0, T1, T2, T3, T4, T5, T6, T7> src) {
    el0 = src.el0;
    el1 = src.el1;
    el2 = src.el2;
    el3 = src.el3;
    el4 = src.el4;
    el5 = src.el5;
    el6 = src.el6;
    el7 = src.el7;
    return src;
  };
};

template <class T0> ltuple<T0> tie(T0 &t0) { return ltuple<T0>(t0); }

template <class T0, class T1> ltuple<T0, T1> tie(T0 &t0, T1 &t1) {
  return ltuple<T0, T1>(t0, t1);
}

template <class T0, class T1, class T2>
ltuple<T0, T1, T2> tie(T0 &t0, T1 &t1, T2 &t2) {
  return ltuple<T0, T1, T2>(t0, t1, t2);
}

template <class T0, class T1, class T2, class T3>
ltuple<T0, T1, T2, T3> tie(T0 &t0, T1 &t1, T2 &t2, T3 &t3) {
  return ltuple<T0, T1, T2, T3>(t0, t1, t2, t3);
}

template <class T0, class T1, class T2, class T3, class T4>
ltuple<T0, T1, T2, T3, T4> tie(T0 &t0, T1 &t1, T2 &t2, T3 &t3, T4 &t4) {
  return ltuple<T0, T1, T2, T3, T4>(t0, t1, t2, t3, t4);
}

template <class T0, class T1, class T2, class T3, class T4, class T5>
ltuple<T0, T1, T2, T3, T4, T5> tie(T0 &t0, T1 &t1, T2 &t2, T3 &t3, T4 &t4,
                                   T5 &t5) {
  return ltuple<T0, T1, T2, T3, T4, T5>(t0, t1, t2, t3, t4, t5);
}

template <class T0, class T1, class T2, class T3, class T4, class T5, class T6>
ltuple<T0, T1, T2, T3, T4, T5, T6> tie(T0 &t0, T1 &t1, T2 &t2, T3 &t3, T4 &t4,
                                       T5 &t5, T6 &t6) {
  return ltuple<T0, T1, T2, T3, T4, T5, T6>(t0, t1, t2, t3, t4, t5, t6);
}

template <class T0, class T1, class T2, class T3, class T4, class T5, class T6,
          class T7>
ltuple<T0, T1, T2, T3, T4, T5, T6, T7> tie(T0 &t0, T1 &t1, T2 &t2, T3 &t3,
                                           T4 &t4, T5 &t5, T6 &t6, T7 &t7) {
  return ltuple<T0, T1, T2, T3, T4, T5, T6, T7>(t0, t1, t2, t3, t4, t5, t6, t7);
}
#endif // __cplusplus > 199711L

#endif // RAC_H
