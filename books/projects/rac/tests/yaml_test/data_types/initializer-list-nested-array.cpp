#include <array>
using namespace std;

// RAC begin

int bar() {
  const array<int, 2> arr[2] = { 3 }, arr2[1] = { 0 }, arr3[1] = { 0 };
  return 0;
}
