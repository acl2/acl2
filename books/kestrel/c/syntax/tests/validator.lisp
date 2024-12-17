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
;; PLAIN-CHAR-SIGNEDP is T if plain chars are signed, else NIL (the default).
;; Optional COND may be over variables AST.

(defmacro test-valid (input &key
                            gcc
                            short-bytes
                            int-bytes
                            long-bytes
                            llong-bytes
                            plain-char-signedp
                            cond)
  `(assert-event
    (b* ((short-bytes (or ,short-bytes 2))
         (int-bytes (or ,int-bytes 4))
         (long-bytes (or ,long-bytes 8))
         (llong-bytes (or ,llong-bytes 8))
         (ienv (make-ienv :short-bytes short-bytes
                          :int-bytes int-bytes
                          :long-bytes long-bytes
                          :llong-bytes llong-bytes
                          :plain-char-signedp ,plain-char-signedp))
         ((mv erp1 ast) (parse-file (filepath "test")
                                    (acl2::string=>nats ,input)
                                    ,gcc))
         ((mv erp2 ast) (dimb-transunit ast ,gcc))
         ((mv erp3 ?ast &) (valid-transunit ast ,gcc ienv)))
      (cond (erp1 (cw "~%PARSER ERROR: ~@0~%" erp1))
            (erp2 (cw "~%DISAMBIGUATOR ERROR: ~@0~%" erp2))
            (erp3 (cw "~%VALIDATOR ERROR: ~@0~%" erp3))
            (t ,(or cond t))))))

(defmacro test-valid-fail (input &key
                                 gcc
                                 short-bytes
                                 int-bytes
                                 long-bytes
                                 llong-bytes
                                 plain-char-signedp)
  `(assert-event
    (b* ((short-bytes (or ,short-bytes 2))
         (int-bytes (or ,int-bytes 4))
         (long-bytes (or ,long-bytes 8))
         (llong-bytes (or ,llong-bytes 8))
         (ienv (make-ienv :short-bytes short-bytes
                          :int-bytes int-bytes
                          :long-bytes long-bytes
                          :llong-bytes llong-bytes
                          :plain-char-signedp ,plain-char-signedp))
         ((mv erp1 ast) (parse-file (filepath "test")
                                    (acl2::string=>nats ,input)
                                    ,gcc))
         ((mv erp2 ast) (dimb-transunit ast ,gcc))
         ((mv erp3 & &) (valid-transunit ast ,gcc ienv)))
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
"
 :cond (b* ((edecls (transunit->decls ast))
            (edecl (cadr edecls))
            (fundef (extdecl-fundef->unwrap edecl))
            (stmt (fundef->body fundef))
            (items (stmt-compound->items stmt))
            (item (car items))
            (decl (block-item-decl->unwrap item))
            (ideclors (decl-decl->init decl))
            (ideclor (car ideclors))
            (initer (initdeclor->init? ideclor))
            (expr-sizeof (initer-single->expr initer))
            (expr-xp (expr-unary->arg expr-sizeof))
            (expr-x (expr-paren->inner expr-xp)))
         (and (expr-case expr-x :ident)
              (equal (expr-ident->info expr-x)
                     (type-sint)))))

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

(test-valid
 "static int f();
  extern int f();
")

(test-valid-fail
 "extern int f();
  static int f();
")

(test-valid-fail
 "int f();
  static int f();
")

(test-valid
 "typedef unsigned short __uint16_t;
static __inline __uint16_t
__bswap_16 (__uint16_t __bsx)
{
  return 0;
}
"
 :gcc t)

(test-valid
 "typedef unsigned char uint8_t;
static uint8_t g_2[2][1][1] = {{{0UL}},{{0UL}}};
")
