#include <tuple>

// grrr
using namespace std;

// RAC begin

tuple<int, int, int> foo3(int a)
{
  return tuple<int, int, int>(a, a, a);
}

tuple<int, int, int, int> foo4(int a)
{
  return tuple<int, int, int, int>(a, a, a, a);
}

tuple<int, int, int, int, int> foo5(int a)
{
  return tuple<int, int, int, int, int>(a, a, a, a, a);
}

tuple<int, int, int, int, int, int> foo6(int a)
{
  return tuple<int, int, int, int, int, int>(a, a, a, a, a, a);
}

tuple<int, int, int, int, int, int, int> foo7(int a)
{
  return tuple<int, int, int, int, int, int, int>(a, a, a, a, a, a, a);
}

tuple<int, int, int, int, int, int, int, int> foo8(int a)
{
  return tuple<int, int, int, int, int, int, int, int>(a, a, a, a, a, a, a, a);
}

// RAC end
