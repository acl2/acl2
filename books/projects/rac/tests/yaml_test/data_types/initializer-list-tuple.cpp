#include <tuple>
using namespace std;

// RAC begin

tuple<int, int> foo() {
  tuple<int, int> t = { 1, 2 };
  return t;
}

// RAC end
