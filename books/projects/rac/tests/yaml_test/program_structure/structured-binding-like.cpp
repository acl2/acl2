#include <tuple>
#include <array>
using namespace std;

// RAC begin

tuple<int, int> foo()
{
  return tuple<int, int>(3, 2);
}

int bar()
{
  int a, b = foo();
  return 0;
}

// RAC end
