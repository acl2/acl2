#include <tuple>
using namespace std;

// RAC begin

tuple<int, int, int, int, int, int> foo()
{
  return tuple<int, int, int, int, int, int>(1, 2, 3, 4, 5, 6);
}

int bar()
{
  int a[6];
  tie(a[0], a[1], a[2], a[3], a[4], a[5]) = foo();
  return 0;
}

// RAC end
