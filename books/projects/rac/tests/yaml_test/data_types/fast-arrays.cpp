#include <array>

using namespace std;

template<class T, std::size_t N>
using fast_array =array<T, N>;

// RAC begin

const array<int, 3> a_global = { 1, 2, 3 };
const fast_array<int, 3> a_fast_global = { 1, 2, 3 };

int global_use() {
  return a_global[1] + a_fast_global[1];
}

int local_use() {
  const array<int, 3> a_local = { 1, 2, 3 };
  const fast_array<int, 3> a_fast_local = { 1, 2, 3 };
  return a_local[1] + a_fast_local[1];
}
