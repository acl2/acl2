#include <array>

using namespace std;

template<class T, std::size_t N>
using fast_array =array<T, N>;

// RAC begin


int bar(const array<int, 3> a) {
  return a[0];
}

int foo() {
  const fast_array<int, 3> a_fast_local = { 1, 2, 3 };
  return bar(a_fast_local);
}
