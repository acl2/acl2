#ifdef MY_MACRO
  #if MY_MACRO != 0
    #error("MY_MACRO does not have value 0.");
  #endif
#else
  #error("MY_MACRO is not defined.");
#endif

int foo(void) {
  return MY_MACRO;
}
