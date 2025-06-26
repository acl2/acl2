#include <stdbool.h>

// The function to test:
unsigned long unsigned_long_add (unsigned long x, unsigned long y) {
  return x+y;
}

// The formal unit test (the add function is commutative).  The Formal Unit Tester
// will prove that this function always returns 1.
bool test_unsigned_long_add_commutative (unsigned long x, unsigned long y) {
  return unsigned_long_add(x, y) == unsigned_long_add(y, x);
}
