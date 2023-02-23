#include <array>

// grrr
using namespace std;

// RAC begin

int foo(array<int, 5> a)
{
  return a[4];
}

array<int, 2> bar(int a, int b)
{
  array<int, 2> arr;
  arr[0] = a;
  arr[1] = b;
  return arr;
}

// RAC end
