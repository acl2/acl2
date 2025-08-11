#include <array>

using namespace std;

template<class T, std::size_t N>
using fast_array =array<T, N>;

// RAC begin

int foo() {
  fast_array<int, 3> a_fast_local = {{ 1, 2, 3 }};
  return a_fast_local[1];
}
