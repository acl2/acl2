; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "preprocessor-testing-macros")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Single-file tests.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-examples/empty.c")

(test-preproc-1 "empty.c"
                ""
                :base-dir "preproc-examples")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-examples/whitespace.c")

(test-preproc-1 "whitespace.c"
                (list 10
                      32 32 32 10 ; SP SP SP
                      9 10 ; HT
                      11 10 ; VT
                      12 10) ; FF
                :base-dir "preproc-examples")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-examples/comments.c")

(test-preproc-1 "comments.c"
                "/* block
 * comment
 */

// line comment
"
                :base-dir "preproc-examples")

; This is the same test but dropping comments.

(test-preproc-1 "comments.c"
                "


"
                :base-dir "preproc-examples"
                :keep-comments nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-examples/text.c")

(test-preproc-1 "text.c"
                "int x = 0;

void f(double y) {
  y = 0.1;
}
"
                :base-dir "preproc-examples")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-examples/null-directive.c")

(test-preproc-1 "null-directive.c"
                "/*#*/
/* comment */ /*#*/
/*#*/ // comment
/* comment */ /*#*/ // comment
    /*#*/
"
                :base-dir "preproc-examples")

; This is the same test but dropping comments.

(test-preproc-1 "null-directive.c"
                (list 10
                      32 10 ; SP
                      32 10 ; SP
                      32 32 10 ; SP SP
                      32 32 32 32 10) ; SP SP SP SP
                :base-dir "preproc-examples"
                :keep-comments nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-examples/macros.c")

(test-preproc-1 "macros.c"
                "
char[100] buffer;

int x =  0;

int y = 3;

int z1 = (1, );
int z2 = (1, i);
int z3 = (1, a,b);
int z4 = (1, a, b);
int z5 = (1, a, b);
int z6 = (1, (a,b));

+;
+3;
+5.7e88;
+x;
+ +uu;
+x+y;
+ +7;

-;
-3;
-5.7e88;
-x;
-+uu;
-x+y;
-0;

(a)+(b);
(a * b)+(a / b);
()+(78);
(87)+();
()+();
(f(x,y))+(g(w));

((a)*(b),);
((a + b)*(a - b),);
(()*(78),);
((87)*(),);
(()*(),);
((f(x,y))*(g(w)),);
((1)*(2),3);
((1)*(2),3, 4);
"
                :base-dir "preproc-examples")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-examples/stringize.c")

(test-preproc-1 "stringize.c"
                "
\"\";
\"id\";
\"+=\";
\"739.88e+78\";
\"'a'\";
\"'\\\\n'\";
\"'\\\\002'\";
\"L'a'\";
\"U'a'\";
\"u'a'\";
\"\\\"abc\\\"\";
"
                :base-dir "preproc-examples")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-examples/concatenate.c")

(test-preproc-1 "concatenate.c"
                "
a b cd e;
x334;
6e+8P-;
>>=;
"
                :base-dir "preproc-examples")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-examples/c17-std-example-6.10.3.3.c")

(test-preproc-1 "c17-std-example-6.10.3.3.c"
                ""
                :base-dir "preproc-examples")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-examples/c17-std-example-6.10.3.4.c")

(test-preproc-1 "c17-std-example-6.10.3.4.c"
                "
2*9*g
"
                :base-dir "preproc-examples")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-examples/c17-std-example1-6.10.3.5.c")

(test-preproc-1 "c17-std-example1-6.10.3.5.c"
                "
int table[100];
"
                :base-dir "preproc-examples")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-examples/c17-std-example2-6.10.3.5.c")

(test-preproc-1 "c17-std-example2-6.10.3.5.c"
                ""
                :base-dir "preproc-examples")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-examples/c17-std-example3-6.10.3.5.c")

(test-preproc-1 "c17-std-example3-6.10.3.5.c"
                "
f(2 * (y+1)) + f(2 * (f(2 * (z[0])))) % f(2 * (0)) + t(1);
f(2 * (2+(3,4)-0,1)) | f(2 * (\\~{ } 5)) & f(2 * (0,1))^m(0,1);
int i[] = { 1, 23, 4, 5,  };
char c[2][6] = { \"hello\", \"\" };
"
                :base-dir "preproc-examples")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-examples/c17-std-example4-6.10.3.5.c")

(test-preproc-1 "c17-std-example4-6.10.3.5.c"
                "
printf(\"x\" \"1\" \"= %d, x\" \"2\" \"= %s\", x1, x2);
fputs(\"strncmp(\\\"abc\\\\0d\\\", \\\"abc\\\", '\\\\4') == 0\" \": @\\n\", s);
include \"vers2.h\" // omit # in #include to avoid access
\"hello\";
\"hello\" \", world\"
"
                :base-dir "preproc-examples")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-examples/c17-std-example5-6.10.3.5.c")

(test-preproc-1 "c17-std-example5-6.10.3.5.c"
                "
int j[] = { 123, 45, 67, 89,
           10, 11, 12,  };
"
                :base-dir "preproc-examples")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-examples/c17-std-example6-6.10.3.5.c")

(test-preproc-1 "c17-std-example6-6.10.3.5.c"
                ""
                :base-dir "preproc-examples")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-examples/c17-std-example7-6.10.3.5.c")

(test-preproc-1 "c17-std-example7-6.10.3.5.c"
                "
fprintf(stderr, \"Flag\");
fprintf(stderr, \"X = %d\\n\", x);
puts(\"The first, second, and third items.\");
((x>y)?puts(\"x>y\"): printf(\"x is %d but y is %d\", x, y));
"
                :base-dir "preproc-examples")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-examples/conditional.c")

(test-preproc-1 "conditional.c"
                "M_is_not_defined


M_is_defined
"
                :base-dir "preproc-examples")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Multi-file tests.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-example1/including.c")
; (depends-on "preproc-example1/included.h")
; (depends-on "preproc-example1/subdir/included2.h")

(test-preproc '("including.c")
              :expected (fileset-of "including.c"
                                    "#include \"included.h\"
/* comment
   on two lines */ #include \"subdir/included2.h\"
#include \"included.h\" // comment
   #include \"included.h\"
"
                                    "included.h"
                                    "#include \"subdir/included2.h\"
"
                                    "subdir/included2.h"
                                    "/*#*/ // null directive
")
              :base-dir "preproc-example1")

; This is the same test but with full expansion.

(test-preproc '("including.c")
              :expected (fileset-of "including.c"
                                    "// #include \"included.h\" >>>>>>>>>>
// #include \"subdir/included2.h\" >>>>>>>>>>
/*#*/ // null directive
// <<<<<<<<<< #include \"subdir/included2.h\"
// <<<<<<<<<< #include \"included.h\"
// #include \"subdir/included2.h\" >>>>>>>>>>
/*#*/ // null directive
// <<<<<<<<<< #include \"subdir/included2.h\"
// #include \"included.h\" >>>>>>>>>>
// #include \"subdir/included2.h\" >>>>>>>>>>
/*#*/ // null directive
// <<<<<<<<<< #include \"subdir/included2.h\"
// <<<<<<<<<< #include \"included.h\"
// #include \"included.h\" >>>>>>>>>>
// #include \"subdir/included2.h\" >>>>>>>>>>
/*#*/ // null directive
// <<<<<<<<<< #include \"subdir/included2.h\"
// <<<<<<<<<< #include \"included.h\"
")
              :base-dir "preproc-example1"
              :full-expansion t)

; Check against full expansion.

(test-preproc-fullexp '("including.c")
                      :base-dir "preproc-example1")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-example2/gincluder1.c")
; (depends-on "preproc-example2/gincluder2.c")
; (depends-on "preproc-example2/gincluder1.h")
; (depends-on "preproc-example2/gincluder2.h")
; (depends-on "preproc-example2/guarded.h")
; (depends-on "preproc-example2/gincludermod1.c")
; (depends-on "preproc-example2/gincludermod2.c")

; In this test:
; - gincluder1.c includes gincluder1.h and gincluder2.h in that order
; - gincluder2.c includes gincluder2.h and gincluder1.h in that order
; - gincluder1.h includes guarded.h and then introduces x1
; - gincluder2.h includes guarded.h and then introduces x2
; - guarded.h has a header guard, and introduces f
; All the #include directives are preserved.

(test-preproc '("gincluder1.c"
                "gincluder2.c")
              :expected (fileset-of "gincluder1.c"
                                    "
#include \"gincluder1.h\"
#include \"gincluder2.h\"
"
                                    "gincluder2.c"
                                    "
#include \"gincluder2.h\"
#include \"gincluder1.h\"
"
                                    "gincluder1.h"
                                    "
#include \"guarded.h\"
int x1 = 0;
"
                                    "gincluder2.h"
                                    "
#include \"guarded.h\"
int x2 = 0;
"
                                    "guarded.h"
                                    "
#ifndef GUARDED
#define GUARDED
void f() {}
#endif
")
              :base-dir "preproc-example2")

; This is the same test but with full expansion.

(test-preproc '("gincluder1.c"
                "gincluder2.c")
              :expected (fileset-of "gincluder1.c"
                                    "
// #include \"gincluder1.h\" >>>>>>>>>>

// #include \"guarded.h\" >>>>>>>>>>

void f() {}
// <<<<<<<<<< #include \"guarded.h\"
int x1 = 0;
// <<<<<<<<<< #include \"gincluder1.h\"
// #include \"gincluder2.h\" >>>>>>>>>>

// #include \"guarded.h\" >>>>>>>>>>

// <<<<<<<<<< #include \"guarded.h\"
int x2 = 0;
// <<<<<<<<<< #include \"gincluder2.h\"
"
                                    "gincluder2.c"
                                    "
// #include \"gincluder2.h\" >>>>>>>>>>

// #include \"guarded.h\" >>>>>>>>>>

void f() {}
// <<<<<<<<<< #include \"guarded.h\"
int x2 = 0;
// <<<<<<<<<< #include \"gincluder2.h\"
// #include \"gincluder1.h\" >>>>>>>>>>

// #include \"guarded.h\" >>>>>>>>>>

// <<<<<<<<<< #include \"guarded.h\"
int x1 = 0;
// <<<<<<<<<< #include \"gincluder1.h\"
")
              :base-dir "preproc-example2"
              :full-expansion t)

; This is the same test but with full expansion and without tracing.

(test-preproc '("gincluder1.c"
                "gincluder2.c")
              :expected (fileset-of "gincluder1.c"
                                    "


void f() {}
int x1 = 0;


int x2 = 0;
"
                                    "gincluder2.c"
                                    "


void f() {}
int x2 = 0;


int x1 = 0;
")
              :base-dir "preproc-example2"
              :full-expansion t
              :trace-expansion nil)

; Check against full expansion.

(test-preproc-fullexp '("gincluder1.c"
                        "gincluder2.c")
                      :base-dir "preproc-example2")

;;;;;;;;;;;;;;;;;;;;

; This is a variant of the previous test in which
; instead of gincluder1.c and gincluder2.c,
; we have gincludermod1.c and gincludermod2.c,
; which "modify" f by #define'ing it to be f1 and f2 respectively.
; Thus:
; - guarded.h and gincluder1.h are expanded in gincludermod1.c,
;   but not ginluder2.h
; - guarded.h and gincluder2.h are expanded in gincludermod2.c,
;   but not ginluder1.h

(test-preproc '("gincludermod1.c"
                "gincludermod2.c")
              :expected (fileset-of "gincludermod1.c"
                                    "
// #include \"gincluder1.h\" >>>>>>>>>>

// #include \"guarded.h\" >>>>>>>>>>

#ifndef GUARDED
#define GUARDED
void f1() {}
#endif
// <<<<<<<<<< #include \"guarded.h\"
int x1 = 0;
// <<<<<<<<<< #include \"gincluder1.h\"
#include \"gincluder2.h\"
"
                                    "gincludermod2.c"
                                    "
// #include \"gincluder2.h\" >>>>>>>>>>

// #include \"guarded.h\" >>>>>>>>>>

#ifndef GUARDED
#define GUARDED
void f2() {}
#endif
// <<<<<<<<<< #include \"guarded.h\"
int x2 = 0;
// <<<<<<<<<< #include \"gincluder2.h\"
#include \"gincluder1.h\"
"
                                    "gincluder1.h"
                                    "
#include \"guarded.h\"
int x1 = 0;
"
                                    "gincluder2.h"
                                    "
#include \"guarded.h\"
int x2 = 0;
"
                                    "guarded.h"
                                    "
#ifndef GUARDED
#define GUARDED
void f() {}
#endif
")
              :base-dir "preproc-example2")

; This is the same test but without tracing.

(test-preproc '("gincludermod1.c"
                "gincludermod2.c")
              :expected (fileset-of "gincludermod1.c"
                                    "


#ifndef GUARDED
#define GUARDED
void f1() {}
#endif
int x1 = 0;
#include \"gincluder2.h\"
"
                                    "gincludermod2.c"
                                    "


#ifndef GUARDED
#define GUARDED
void f2() {}
#endif
int x2 = 0;
#include \"gincluder1.h\"
"
                                    "gincluder1.h"
                                    "
#include \"guarded.h\"
int x1 = 0;
"
                                    "gincluder2.h"
                                    "
#include \"guarded.h\"
int x2 = 0;
"
                                    "guarded.h"
                                    "
#ifndef GUARDED
#define GUARDED
void f() {}
#endif
")
              :base-dir "preproc-example2"
              :trace-expansion nil)

; This is the same test but with full expansion.

(test-preproc '("gincludermod1.c"
                "gincludermod2.c")
              :expected (fileset-of "gincludermod1.c"
                                    "
// #include \"gincluder1.h\" >>>>>>>>>>

// #include \"guarded.h\" >>>>>>>>>>

void f1() {}
// <<<<<<<<<< #include \"guarded.h\"
int x1 = 0;
// <<<<<<<<<< #include \"gincluder1.h\"
// #include \"gincluder2.h\" >>>>>>>>>>

// #include \"guarded.h\" >>>>>>>>>>

// <<<<<<<<<< #include \"guarded.h\"
int x2 = 0;
// <<<<<<<<<< #include \"gincluder2.h\"
"
                                    "gincludermod2.c"
                                    "
// #include \"gincluder2.h\" >>>>>>>>>>

// #include \"guarded.h\" >>>>>>>>>>

void f2() {}
// <<<<<<<<<< #include \"guarded.h\"
int x2 = 0;
// <<<<<<<<<< #include \"gincluder2.h\"
// #include \"gincluder1.h\" >>>>>>>>>>

// #include \"guarded.h\" >>>>>>>>>>

// <<<<<<<<<< #include \"guarded.h\"
int x1 = 0;
// <<<<<<<<<< #include \"gincluder1.h\"
")
              :base-dir "preproc-example2"
              :full-expansion t)

; Check against full expansion.

(test-preproc-fullexp '("gincludermod1.c"
                        "gincludermod2.c")
                      :base-dir "preproc-example2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-example3/f.c")
; (depends-on "preproc-example3/g.c")
; (depends-on "preproc-example3/h.c")
; (depends-on "preproc-example3/i.c")
; (depends-on "preproc-example3/j.c")

(test-preproc '("i.c" "j.c")
              :expected (fileset-of "f.c"
                                    "#ifndef F
#define F
x
#endif
"
                                    "g.c"
                                    "#include \"f.c\"
z
"
                                    "h.c"
                                    "#include \"f.c\"
#include \"g.c\"
"

                                    "i.c"
                                    "#include \"h.c\"
"
                                    "j.c"
                                    "#include \"g.c\"
")
              :base-dir "preproc-example3")

; This is the same test but with full expansion.

(test-preproc '("i.c" "j.c")
              :expected (fileset-of "i.c"
                                    "// #include \"h.c\" >>>>>>>>>>
// #include \"f.c\" >>>>>>>>>>
x
// <<<<<<<<<< #include \"f.c\"
// #include \"g.c\" >>>>>>>>>>
// #include \"f.c\" >>>>>>>>>>
// <<<<<<<<<< #include \"f.c\"
z
// <<<<<<<<<< #include \"g.c\"
// <<<<<<<<<< #include \"h.c\"
"
                                    "j.c"
                                    "// #include \"g.c\" >>>>>>>>>>
// #include \"f.c\" >>>>>>>>>>
x
// <<<<<<<<<< #include \"f.c\"
z
// <<<<<<<<<< #include \"g.c\"
")
              :base-dir "preproc-example3"
              :full-expansion t)

; Check against full expansion.

(test-preproc-fullexp '("i.c" "j.c")
                      :base-dir "preproc-example3")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-example4/f.c")
; (depends-on "preproc-example4/g.c")
; (depends-on "preproc-example4/h.c")
; (depends-on "preproc-example4/i.c")
; (depends-on "preproc-example4/j.c")

(test-preproc '("i.c" "j.c")
              :expected (fileset-of "f.c"
                                    "#ifndef F
#define F
x
#endif
"
                                    "g.c"
                                    "// #include \"f.c\" >>>>>>>>>>
#ifndef F
#define F
y
#endif
// <<<<<<<<<< #include \"f.c\"
z
"
                                    "h.c"
                                    "#include \"f.c\"
// #include \"g.c\" >>>>>>>>>>
#include \"f.c\"
z
// <<<<<<<<<< #include \"g.c\"
"

                                    "i.c"
                                    "#include \"h.c\"
"
                                    "j.c"
                                    "#include \"g.c\"
")
              :base-dir "preproc-example4")

; This is the same test but with full expansion.

(test-preproc '("i.c" "j.c")
              :expected (fileset-of "i.c"
                                    "// #include \"h.c\" >>>>>>>>>>
// #include \"f.c\" >>>>>>>>>>
x
// <<<<<<<<<< #include \"f.c\"
// #include \"g.c\" >>>>>>>>>>
// #include \"f.c\" >>>>>>>>>>
// <<<<<<<<<< #include \"f.c\"
z
// <<<<<<<<<< #include \"g.c\"
// <<<<<<<<<< #include \"h.c\"
"
                                    "j.c"
                                    "// #include \"g.c\" >>>>>>>>>>
// #include \"f.c\" >>>>>>>>>>
y
// <<<<<<<<<< #include \"f.c\"
z
// <<<<<<<<<< #include \"g.c\"
")
              :base-dir "preproc-example4"
              :full-expansion t)

; Check against full expansion.

(test-preproc-fullexp '("i.c" "j.c")
                      :base-dir "preproc-example4")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "preproc-example5/a.c")
; (depends-on "preproc-example5/b.c")
; (depends-on "preproc-example5/c.c")

(test-preproc '("b.c")
              :expected (fileset-of "a.c"
                                    "#ifndef A
#define A
int a;
#endif
"
                                    "b.c"
                                    "#include \"a.c\"
#include \"c.c\"
"
                                    "c.c"
                                    "#include \"a.c\"
void f();
")
              :base-dir "preproc-example5")

; This is the same test but with full expansion.

(test-preproc '("b.c")
              :expected (fileset-of "b.c"
                                    "// #include \"a.c\" >>>>>>>>>>
int a;
// <<<<<<<<<< #include \"a.c\"
// #include \"c.c\" >>>>>>>>>>
// #include \"a.c\" >>>>>>>>>>
// <<<<<<<<<< #include \"a.c\"
void f();
// <<<<<<<<<< #include \"c.c\"
")
              :base-dir "preproc-example5"
              :full-expansion t)

; Check against full expansion.

(test-preproc-fullexp '("b.c")
                      :base-dir "preproc-example5")
