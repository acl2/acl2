#ifdef MY_MACRO
  #if MY_MACRO != 1
    #error("MY_MACRO does not have value 1.");
  #endif
#else
  #error("MY_MACRO is not defined.");
#endif

int bar(void) {
  return MY_MACRO;
}
