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

(defconst *test-valid-allowed-options*
  '(:gcc
    :short-bytes
    :int-bytes
    :long-bytes
    :llong-bytes
    :plain-char-signedp
    :cond))

(defconst *test-valid-fail-allowed-options*
  '(:gcc
    :short-bytes
    :int-bytes
    :long-bytes
    :llong-bytes
    :plain-char-signedp
    :cond))

(define make-dummy-filepath-filedata-map ((filepath-names true-listp) input)
  :returns (map filepath-filedata-mapp)
  (b* (((when (endp filepath-names))
        (raise "Too many translation units provided."))
       ((when (atom input))
        nil)
       ((unless (stringp (first input)))
        (raise "Not a string: ~x0" (first input)))
       (bytes (acl2::string=>nats (first input)))
       ((unless (byte-listp bytes))
        (raise "Internal error: converted string is not a byte list: ~x0"
               bytes)))
    (omap::update (filepath (first filepath-names))
                  (filedata bytes)
                  (make-dummy-filepath-filedata-map (rest filepath-names)
                                                    (rest input)))))


(define make-dummy-fileset (input)
  :returns (fileset fileset)
  (fileset (make-dummy-filepath-filedata-map
             '("test0" "test1" "test2" "test2" "test3" "test4" "test5" "test6")
             input)))

(defmacro test-valid (&rest args)
  (b* (((mv erp inputs options)
        (partition-rest-and-keyword-args args *test-valid-allowed-options*))
       ((when erp)
        (cw "The inputs must be a sequence of strings ~
             followed by the options ~&0."
            *test-valid-allowed-options*)
        `(mv t nil state))
       (short-bytes (or (cdr (assoc-eq :short-bytes options)) 2))
       (int-bytes (or (cdr (assoc-eq :int-bytes options)) 2))
       (long-bytes (or (cdr (assoc-eq :long-bytes options)) 4))
       (llong-bytes (or (cdr (assoc-eq :llong-bytes options)) 8))
       (plain-char-signedp (cdr (assoc-eq :plain-char-signedp options)))
       (gcc (cdr (assoc-eq :gcc options)))
       (cond (cdr (assoc-eq :cond options)))
       (ienv (make-ienv :short-bytes short-bytes
                        :int-bytes int-bytes
                        :long-bytes long-bytes
                        :llong-bytes llong-bytes
                        :plain-char-signedp plain-char-signedp
                        :gcc gcc))
       (fileset (make-dummy-fileset inputs)))
    `(assert-event
       (b* (((mv erp1 ast) (parse-fileset ',fileset ,gcc))
            ((mv erp2 ast) (dimb-transunit-ensemble ast ,gcc))
            ((mv erp3 ?ast) (valid-transunit-ensemble ast ',ienv)))
         (cond (erp1 (cw "~%PARSER ERROR: ~@0~%" erp1))
               (erp2 (cw "~%DISAMBIGUATOR ERROR: ~@0~%" erp2))
               (erp3 (cw "~%VALIDATOR ERROR: ~@0~%" erp3))
               (t ,(or cond t)))))))

(defmacro test-valid-fail (&rest args)
  (b* (((mv erp inputs options)
        (partition-rest-and-keyword-args args
                                         *test-valid-fail-allowed-options*))
       ((when erp)
        (cw "The inputs must be a sequence of strings ~
             followed by the options ~&0."
            *test-valid-fail-allowed-options*)
        `(mv t nil state))
       (short-bytes (or (cdr (assoc-eq :short-bytes options)) 2))
       (int-bytes (or (cdr (assoc-eq :int-bytes options)) 2))
       (long-bytes (or (cdr (assoc-eq :long-bytes options)) 4))
       (llong-bytes (or (cdr (assoc-eq :llong-bytes options)) 8))
       (plain-char-signedp (cdr (assoc-eq :plain-char-signedp options)))
       (gcc (cdr (assoc-eq :gcc options)))
       (ienv (make-ienv :short-bytes short-bytes
                        :int-bytes int-bytes
                        :long-bytes long-bytes
                        :llong-bytes llong-bytes
                        :plain-char-signedp plain-char-signedp
                        :gcc gcc))
       (fileset (make-dummy-fileset inputs)))
    `(assert-event
       (b* (((mv erp1 ast) (parse-fileset ',fileset ,gcc))
            ((mv erp2 ast) (dimb-transunit-ensemble ast ,gcc))
            ((mv erp3 ?ast) (valid-transunit-ensemble ast ',ienv)))
         (cond (erp1 (not (cw "~%PARSER ERROR: ~@0~%" erp1)))
               (erp2 (not (cw "~%DISAMBIGUATOR ERROR: ~@0~%" erp2)))
               (erp3 (not (cw "~%VALIDATOR ERROR: ~@0~%" erp3)))
               (t nil))))))

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
 :cond (b* ((transunit (omap::head-val (transunit-ensemble->unwrap ast)))
            (edecls (transunit->decls transunit))
            (edecl (cadr edecls))
            (fundef (extdecl-fundef->unwrap edecl))
            (items (fundef->body fundef))
            (item (car items))
            (decl (block-item-decl->decl item))
            (ideclors (decl-decl->init decl))
            (ideclor (car ideclors))
            (initer (initdeclor->init? ideclor))
            (expr-sizeof (initer-single->expr initer))
            (expr-xp (expr-unary->arg expr-sizeof))
            (expr-x (expr-paren->inner expr-xp)))
         (and (expr-case expr-x :ident)
              (equal (var-info->type (expr-ident->info expr-x))
                     (type-sint))
              (equal (var-info->linkage (expr-ident->info expr-x))
                     (linkage-external)))))

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

(test-valid
 "_Thread_local int x;
")

(test-valid
 "_Thread_local int x;
"
 :gcc t)

(test-valid-fail
 "__thread int x;
")

(test-valid
 "__thread int x;
"
 :gcc t)

(test-valid-fail
  "int foo(void) {
  int x;
  extern int x;
  return x;
}
")

(test-valid
  "int foo(void) {
  int x;
  {
    extern int x;
    return x;
  }
}
")

(test-valid-fail
  "int foo(void) {
  extern int x;
  return x;
}

static int x;
")

(test-valid
  "int foo(void) {
  static int x;
  return x;
}

extern int x;
")

(test-valid
  "static int x;

int foo(void) {
  extern int x;
  return x;
}
")

(test-valid-fail
  "static int x;

int * foo(void) {
  extern int * x;
  return * x;
}
")

(test-valid-fail
  "static int x;

int foo(void) {
  int x;
  {
    extern int x;
    return x;
  }
}
")

(test-valid
  "int foo(void) {
 extern int x;
 return x;
}

int bar(void) {
 extern int x;
 return x;
}
")

(test-valid-fail
  "int foo(void) {
 extern int x;
 return x;
}

int * bar(void) {
 extern int * x;
 return x;
}
")

(test-valid
  "int * foo(void) {
 extern int x;
 {
   int * x;
   {
     extern int x;
     return x;
   }
 }
}
")

(test-valid-fail
  "int * foo(void) {
 extern int x;
 {
   int x;
   {
     extern int * x;
     return x;
   }
 }
}
")

(test-valid
  "inline int foo(void) { return 0; }
"
  "int foo(void) { return 1; }
")

(test-valid
  "extern int x;
"
  "static int * x;
")

(test-valid-fail
  "extern int x;
"
  "extern int * x;
")

(test-valid-fail
  "int foo(void) {
 extern int x;
 return x;
}
"
  "extern int * x;
")

(test-valid-fail
  "static int foo(void);

void bar(void) {
  int foo;
  {
    extern int foo(void);
  }
}
")

(test-valid-fail
  "int foo(void) {
  return 0;
}
"
  "int foo;
")

(test-valid
  "int foo(void);

  int bar(short x) {
    int foo = x;
    {
      extern int foo(void);
    }
    return foo;
  }
"
  "static int bar = 0;

   extern int foo(void) {
  return bar;
}
"
  :cond (b* ((filepath-transunit-map (transunit-ensemble->unwrap ast))
             (transunit1 (omap::head-val filepath-transunit-map))
             (transunit2 (omap::head-val (omap::tail filepath-transunit-map)))
             (edecls1 (transunit->decls transunit1))
             (foo-init1 (first (decl-decl->init (extdecl-decl->unwrap (first edecls1)))))
             (foo-init1-uid (initdeclor-info->uid? (initdeclor->info foo-init1)))
             ;; (- (cw "foo-init1 uid: ~x0~%" foo-init1-uid))
             (bar-fundef (extdecl-fundef->unwrap (second edecls1)))
             (bar-fundef-uid (fundef-info->uid (fundef->info bar-fundef)))
             ;; (- (cw "bar-fundef uid: ~x0~%" bar-fundef-uid))
             (bar-params (dirdeclor-function-params->params (declor->direct (fundef->declor bar-fundef))))
             (bar-param-declon (param-declon->declor (first bar-params)))
             (x-param-uid (param-declor-info->uid (param-declor-nonabstract->info bar-param-declon)))
             ;; (- (cw "x-param uid: ~x0~%" x-param-uid))
             (bar-body-decl1 (first (fundef->body bar-fundef)))
             (foo-init2 (first (decl-decl->init (block-item-decl->decl bar-body-decl1))))
             (foo-init2-uid (initdeclor-info->uid? (initdeclor->info foo-init2)))
             ;; (- (cw "foo-init2 uid: ~x0~%" foo-init2-uid))
             (x-expr (initer-single->expr (initdeclor->init? foo-init2)))
             (x-expr-uid (var-info->uid (expr-ident->info x-expr)))
             ;; (- (cw "x-expr uid: ~x0~%" x-expr-uid))
             (bar-body-decl2 (first (stmt-compound->items (block-item-stmt->stmt (second (fundef->body bar-fundef))))))
             (foo-init3 (first (decl-decl->init (block-item-decl->decl bar-body-decl2))))
             (foo-init3-uid (initdeclor-info->uid? (initdeclor->info foo-init3)))
             ;; (- (cw "foo-init3 uid: ~x0~%" foo-init3-uid))
             (bar-return-stmt (block-item-stmt->stmt (third (fundef->body bar-fundef))))
             (foo-expr-uid (var-info->uid (expr-ident->info (stmt-return->expr? bar-return-stmt))))
             ;; (- (cw "foo-expr uid: ~x0~%" foo-expr-uid))
             (edecls2 (transunit->decls transunit2))
             (bar-init (first (decl-decl->init (extdecl-decl->unwrap (first edecls2)))))
             (bar-init-uid (initdeclor-info->uid? (initdeclor->info bar-init)))
             ;; (- (cw "bar-init uid: ~x0~%" bar-init-uid))
             (foo-fundef (extdecl-fundef->unwrap (second edecls2)))
             (foo-fundef-uid (fundef-info->uid (fundef->info foo-fundef)))
             ;; (- (cw "foo-fundef uid: ~x0~%" foo-fundef-uid))
             (foo-return-stmt (block-item-stmt->stmt (first (fundef->body foo-fundef))))
             (bar-expr-uid (var-info->uid (expr-ident->info (stmt-return->expr? foo-return-stmt))))
             ;; (- (cw "bar-expr uid: ~x0~%" bar-expr-uid))
             )
          (and (equal foo-init1-uid foo-init3-uid)
               (not (equal foo-init1-uid foo-init2-uid))
               (equal foo-init2-uid foo-expr-uid)
               (equal x-param-uid x-expr-uid)
               (not (equal x-param-uid foo-init1-uid))
               (not (equal bar-init-uid foo-init1-uid))
               (not (equal bar-init-uid foo-init2-uid))
               (not (equal bar-init-uid x-param-uid))
               (not (equal bar-init-uid bar-fundef-uid))
               (equal foo-fundef-uid foo-init1-uid)
               (equal bar-expr-uid bar-init-uid))))
