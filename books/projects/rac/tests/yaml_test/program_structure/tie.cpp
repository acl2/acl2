#include <tuple>
using namespace std;

// RAC begin

tuple<int, int> foo()
{
  return tuple<int, int>(1, 2);
}

int bar()
{
  int a, b;
  tie(a, b) = foo();
  return 0;
}

// RAC end
