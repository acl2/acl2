; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)
; Author: Grant Jurgensen (grant@kestrel.edu)

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
         (int-bytes (or ,int-bytes 2))
         (long-bytes (or ,long-bytes 4))
         (llong-bytes (or ,llong-bytes 8))
         (ienv (ienv-simple short-bytes
                            int-bytes
                            long-bytes
                            llong-bytes
                            ,plain-char-signedp
                            ,gcc))
         ((mv erp1 ast) (parse-file (filepath "test")
                                    (acl2::string=>nats ,input)
                                    ,gcc))
         ((mv erp2 ast) (dimb-transunit ast ,gcc))
         ((mv erp3 ?ast) (valid-transunit ast ienv)))
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
         (ienv (ienv-simple short-bytes
                            int-bytes
                            long-bytes
                            llong-bytes
                            ,plain-char-signedp
                            ,gcc))
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
 "_Bool b = 1;
")

(test-valid
 "_Bool b = ((void *) 0);
")

(test-valid
 "int a;
_Bool b = &a;
")

(test-valid
 "int * x = 0;
")

(test-valid
 "int * x;
void f() {
  x = 0;
}
")

(test-valid
 "int * x;
void f() {
  if (x == 0) {}
}
")

(test-valid
 "void f() {
  int a;
  if (0 < &a) {}
}
"
 :gcc t)

(test-valid
 "int * x;
void f() {
  if (x) {}
}
")

(test-valid-fail
 "int * f() {
  int * x = 0;
  return 0 - x;
}
")

(test-valid
 "void f(void * x) {
  f(0);
}
")

(test-valid-fail
 "void f() {
  *0;
}
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
                     (make-var-info :type (type-sint)
                                    :linkage (linkage-external))))))

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

(test-valid
  "struct my_struct { int x; };
struct my_struct foo(void);
void bar(void) {
  struct my_struct baz = foo();
}
")

(test-valid
  "void foo(void) {
struct my_struct { int x; };
struct my_struct bar(void);
  struct my_struct baz = bar();
}
")

(test-valid
  "struct my_struct { int x; };
void foo(void) {
  struct my_struct a;
  struct my_struct b;
  a = b;
}
")

(test-valid-fail
  "struct my_struct1 { int x; };
struct my_struct2 { _Bool y; };
void foo(void) {
  struct my_struct1 a;
  struct my_struct2 b;
  a = b;
}
")

(test-valid
  "struct my_struct { int x; };
void foo(void) {
  struct my_struct a;
  struct my_struct b = a;
}
")

(test-valid-fail
  "struct my_struct1 { int x; };
struct my_struct2 { _Bool y; };
void foo(void) {
  struct my_struct1 a;
  struct my_struct2 b = a;
}
")

(test-valid
 "typedef struct foo_s { int x; } foo_t;
typedef foo_t foo_t_alias;
foo_t_alias bar;
")

(test-valid
 "typedef int * foo;
foo bar;
int main(void) {
  *bar;
  return 0;
}
")

(test-valid
 "typedef unsigned int size_t;
void foo() {
  for (size_t i; ; ) {}
    typedef signed int size_t;
  }
")

(test-valid-fail
 "extern int f();
  static int f();
")

(test-valid-fail
 "int f();
  static int f();
")

(test-valid-fail
 "int x;
typedef int x;
")

(test-valid-fail
 "typedef int x;
int x;
")

(test-valid-fail
 "typedef int x;
typedef short x;
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

(test-valid
 "__int128 x;
"
 :gcc t)

(test-valid
 "unsigned __int128 x;
__int128 unsigned y;
"
 :gcc t)

(test-valid
 "__int128 x;
signed __int128 y;
__int128 signed z;
"
 :gcc t)

(test-valid
 "__int128 x;
__signed __int128 y;
__int128 __signed z;
"
 :gcc t)

(test-valid
 "__int128 x;
__signed__ __int128 y;
__int128 __signed__ z;
"
 :gcc t)

(test-valid
 "__int128_t x;
__int128 y;
unsigned __int128_t z;
"
 :gcc t)

(test-valid
 "void main(void) {
  int x = ({ int a = 0; a; });
  int y = ({ int a = 1; a; });
}
"
 :gcc t)

(test-valid
 "int foo (void);
int bar (void);
typeof(bar) foo;
"
 :gcc t)

(test-valid
 "int foo (void);
typeof(foo) bar;
int bar (void);
"
 :gcc t)
