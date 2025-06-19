#include <array>
using namespace std;

// RAC begin

int foo(const array<int, 3> a) {
  return a[2];
}

const array<int, 3> global_a = { 1, 2, 3 };
int bar() {
  const array<int, 3> local_a = { 1, 2, 3 };
  return foo(global_a) + foo(local_a);
}
