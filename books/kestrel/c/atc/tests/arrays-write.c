
void f(unsigned char *a, int i) {
    a[i] = (unsigned char) 88;
}

void copy(unsigned char *a, unsigned char *b, int len) {
    int i = 0;
    while (i < len) {
        b[i] = a[i];
        i = i + 1;
    }
}
