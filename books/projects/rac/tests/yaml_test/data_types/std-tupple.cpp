#include <tuple>

// grrr
using namespace std;

// RAC begin

tuple<int, uint> foo(int a, uint b)
{
  return tuple<int, uint>(a, b);
}

// RAC end
