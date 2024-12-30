#include <ac_int.h>

// rac begin

typedef ac_int<32, true> i32;

int div_int() { return 10 / -7; }

i32 div_reg() {
  i32 a = 10;
  i32 b = -7;
  return a / b;
}

int mod_int() { return 10 % -7; }

i32 mod_reg() {
  i32 a = 10;
  i32 b = -7;
  return a % b;
}

// RAC end

#include <iostream>

int main() { std::cout << div_int() << '\n'; }
