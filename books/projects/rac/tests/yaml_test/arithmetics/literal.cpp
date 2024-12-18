// RAC begin

int foo() {

  int dec_nothting = 1;
  int dec_u = 1u;
  int dec_l = 1ll;
  int dec_ul = 1ull;

  int hex_nothting = 0x1;
  int hex_u = 0x1u;
  int hex_l = 0x1ll;
  int hex_ul = 0x1ull;

  int hex_max_unsigned = 0xFFFFFFFF;
  int dec_max_unsigned = 4294967295;

  return 0;
}

// RAC end

#include <type_traits>

int main() {
  static_assert(std::is_same_v<decltype(1), int>);
  static_assert(std::is_same_v<decltype(1u), unsigned>);
  static_assert(std::is_same_v<decltype(1l), long long>);
  static_assert(std::is_same_v<decltype(1ul), unsigned long long>);

  static_assert(std::is_same_v<decltype(0x1), int>);
  static_assert(std::is_same_v<decltype(0x1u), unsigned>);
  static_assert(std::is_same_v<decltype(0x1l), long long>);
  static_assert(std::is_same_v<decltype(0x1ul), unsigned long long>);

  static_assert(std::is_same_v<decltype(0xFFFFFFFF), unsigned>);
  static_assert(std::is_same_v<decltype(4294967295), long long>);
}
