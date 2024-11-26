; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../validator")
(include-book "../disambiguator")
(include-book "../parser")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; INPUT is an ACL2 string with the text to parse and validate.
;; GCC flag says whether GCC extensions are enabled.
;; SHORT-BYTES is the number of bytes of shorts (default 2).
;; INT-BYTES is the number of bytes of ints (default 4).
;; LONG-BYTES is the number of bytes of longs (default 8).
;; LLONG-BYTES is the number of bytes of long longs (default 8).
;; PLAIN-SIGNED is T if plain chars are signed, else NIL (which the default).

(defmacro test-valid (input &key
                            gcc
                            short-bytes
                            int-bytes
                            long-bytes
                            llong-bytes
                            plain-signed)
  `(assert-event
    (b* ((short-bytes (or ,short-bytes 2))
         (int-bytes (or ,int-bytes 4))
         (long-bytes (or ,long-bytes 8))
         (llong-bytes (or ,llong-bytes 8))
         (ienv (make-ienv :short-bytes short-bytes
                          :int-bytes int-bytes
                          :long-bytes long-bytes
                          :llong-bytes llong-bytes
                          :plain-char-signedp ,plain-signed))
         ((mv erp1 ast) (parse-file (filepath "test")
                                    (acl2::string=>nats ,input)
                                    ,gcc))
         ((mv erp2 ast) (dimb-transunit ast ,gcc))
         ((mv erp3 &) (valid-transunit ast ienv)))
      (cond (erp1 (cw "~%PARSER ERROR: ~@0~%" erp1))
            (erp2 (cw "~%DISAMBIGUATOR ERROR: ~@0~%" erp2))
            (erp3 (cw "~%VALIDATOR ERROR: ~@0~%" erp3))
            (t t)))))

(defmacro test-valid-fail (input &key
                                 gcc
                                 short-bytes
                                 int-bytes
                                 long-bytes
                                 llong-bytes
                                 plain-signed)
  `(assert-event
    (b* ((short-bytes (or ,short-bytes 2))
         (int-bytes (or ,int-bytes 4))
         (long-bytes (or ,long-bytes 8))
         (llong-bytes (or ,llong-bytes 8))
         (ienv (make-ienv :short-bytes short-bytes
                          :int-bytes int-bytes
                          :long-bytes long-bytes
                          :llong-bytes llong-bytes
                          :plain-char-signedp ,plain-signed))
         ((mv erp1 ast) (parse-file (filepath "test")
                                    (acl2::string=>nats ,input)
                                    ,gcc))
         ((mv erp2 ast) (dimb-transunit ast ,gcc))
         ((mv erp3 &) (valid-transunit ast ienv)))
      (cond (erp1 (not (cw "~%PARSER ERROR: ~@0~%" erp1)))
            (erp2 (not (cw "~%DISAMBIGUATOR ERROR: ~@0~%" erp2)))
            (erp3 (not (cw "~%VALIDATOR ERROR: ~@0~%" erp3)))
            (t nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-valid
 "int x;
")

(test-valid-fail
 "int x;
  float x;
")

(test-valid
 "enum {a, b, c};
  int x = b;
")

(test-valid
 "int main(void) {
    return 0;
  }
")

(test-valid
 "void f();
")

(test-valid
 "void f() {}
")

(test-valid
 "int x;
  void f() {
  int y = sizeof(x);
  }
")

(test-valid
 "typedef char x;
  void f() {
  int y = sizeof(x);
  }
")

(test-valid
 "int x;
  void f(x) {}
")

(test-valid
 "typedef char x;
  void f(x);
")

(test-valid
 "void f(int(x));
")

(test-valid
 "typedef char x;
  void f(int(x));
")

(test-valid
 "void f(int *(x));
")

(test-valid
 "typedef char x;
  void f(int *(x));
")

(test-valid
 "int a;
  void f() {
  int b;
  a * b;
  }
")

(test-valid
 "typedef _Bool a;
  void f() {
  int b;
  a * c;
  }
")

(test-valid
 "void f() {
  int a(int);
  int b;
  int amb = (a)(b);
  }
")

(test-valid
 "void f() {
  typedef int a;
  int b;
  int amb = (a)(b);
  }
")

(test-valid
 "void f() {
  int a(int);
  int b;
  int amb = (a)(b);
  }
")

(test-valid
 "void f() {
  typedef int a;
  int b;
  int amb = (a)--++--++(b);
  }
")

(test-valid
 "void f() {
  int a;
  int b;
  int amb = (a)*b;
  }
")

(test-valid
 "void f() {
  typedef int a;
  int *b;
  int amb = (a)*b;
  }
")

(test-valid
 "void f() {
  int a;
  int b;
  int amb = (a)+b;
  }
")

(test-valid
 "void f() {
  typedef int a;
  int b;
  int amb = (a)+b;
  }
")

(test-valid
 "void f() {
  int a;
  int b;
  int c;
  int amb = (a)+b*c;
  }
")

(test-valid
 "void f() {
  typedef int a;
  int b;
  int c;
  int amb = (a)+b*c;
  }
")

(test-valid
 "void f() {
  int a;
  int b;
  int c;
  int amb = (a)&b;
  }
")

(test-valid
 "void f() {
  typedef int a;
  int b;
  int c;
  int amb = (a)&b;
  }
")

(test-valid
 "void f() {
  int a;
  int b;
  int c;
  int amb = (a)&b+c;
  }
")

(test-valid
 "void f() {
  typedef int a;
  int b;
  int c;
  int amb = (a)&b+c;
  }
")

(test-valid
 "unsigned int size_t;
  void foo() {
  for (size_t; ; ) {}
  }
")

(test-valid
 "typedef unsigned int size_t;
  void foo() {
  for (size_t i; ; ) {}
  }
")

(test-valid
 "int myarray[];
  int foo () {
  int x = sizeof(myarray);
  }
")

(test-valid
 "int foo (int *a, int *b) {
 return (char *) (a) - b;
}
")

(test-valid
 "int foo (int a, int b, int c) {
 return a + (b) + c;
}
")

(test-valid
 "int foo (int a, int b, int c) {
  return (a) + (b) + c;
}
")

(test-valid
 "int foo (int a, int b, int c, int d) {
  return a + (b) + (c) + d;
}
")

(test-valid
 "int foo (int a, int b) {
  return ~ (a) + b;
}
")
