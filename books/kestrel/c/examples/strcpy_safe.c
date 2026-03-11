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
