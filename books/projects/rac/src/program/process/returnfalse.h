#include <cstdlib>

inline bool bypass_errors() {
  // If RAC_BYPASS_ERROR, getenv return nullptr aka 0.
  static bool b = []() { return std::getenv("RAC_BYPASS_ERROR"); }();
  return b;
}

inline bool error() { return bypass_errors(); }
