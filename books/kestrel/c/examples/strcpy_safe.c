// A safe version of the C library function strcpy(),
// with some non-essential modifications (e.g. 'while' instead of 'for' loop)
// to fit the subset of C for which we currently have formal semantics,
// and with a small buffer size to facilitate the proof in strcpy-safe.lisp.
unsigned char* strcpy_safe(unsigned char* dst, unsigned char* src) {
  int buffersize = 4;
  int i = 0;
  while (i < buffersize - 1 && src[i]) {
    dst[i] = src[i];
    i = i + 1;
  }
  dst[i] = (unsigned char) 0;
  return dst;
}

// This was the original form of the code, before our slight modifications.
// The ${BUFFER_SIZE} is a placeholder, not actual C syntax.
/*
char* strcpy_safe(char* dst, const char* src) {
  volatile int buffersize = ${BUFFER_SIZE};
  int i;
  for (i = 0; i < buffersize - 1 && src[i]; i++) {
    dst[i] = src[i];
  }
  dst[i] = 0;
  return dst;
}
*/
