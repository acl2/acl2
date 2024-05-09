#include <tuple>
using namespace std;

// RAC begin

tuple<int, int> foo()
{
  return tuple<int, int>(1, 2);
}

int bar()
{
  int a[2];
  tie(a[0], a[1]) = foo();
  return 0;
}

// RAC end
