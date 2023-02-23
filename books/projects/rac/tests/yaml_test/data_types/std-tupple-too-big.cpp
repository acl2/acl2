#include <tuple>

// grrr
using namespace std;

// RAC begin

tuple<int, int, int, int, int, int, int, int, int> foo(int a)
{
  return tuple<int, int, int, int, int, int, int, int, int>(a, a, a, a, a, a, a, a, a);
}

// RAC end
