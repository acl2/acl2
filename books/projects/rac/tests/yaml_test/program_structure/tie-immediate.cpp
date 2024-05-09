#include <tuple>
using namespace std;

// RAC begin

int bar()
{
  int a, b;
  tie(a, b) = tuple<int, int>(1, 2);
  return 0;
}

// RAC end
