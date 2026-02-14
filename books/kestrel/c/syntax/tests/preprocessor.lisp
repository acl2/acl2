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

; (depends-on "empty.c")

(test-preproc-1 "empty.c" "")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "whitespace.c")

(test-preproc-1 "whitespace.c"
                (list 10
                      32 32 32 10 ; SP SP SP
                      9 10 ; HT
                      11 10 ; VT
                      12 10)) ; FF

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "comments.c")

(test-preproc-1 "comments.c"
                "/* block
 * comment
 */

// line comment
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "text.c")

(test-preproc-1 "text.c"
                "int x = 0;

void f(double y) {
  y = 0.1;
}
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "null-directive.c")

(test-preproc-1 "null-directive.c"
                "/*#*/
/* comment */ /*#*/
/*#*/ // comment
/* comment */ /*#*/ // comment
    /*#*/
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "including.c")
; (depends-on "included.h")
; (depends-on "subdir/included2.h")

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
"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "macros.c")

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
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "stringize.c")

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
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "concatenate.c")

(test-preproc-1 "concatenate.c"
                "
a b cd e;
x334;
6e+8P-;
>>=;
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "c17-std-example-6.10.3.3.c")

(test-preproc-1 "c17-std-example-6.10.3.3.c" "")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "c17-std-example-6.10.3.4.c")

(test-preproc-1 "c17-std-example-6.10.3.4.c"
                "
2*9*g
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "c17-std-example1-6.10.3.5.c")

(test-preproc-1 "c17-std-example1-6.10.3.5.c"
                "
int table[100];
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "c17-std-example2-6.10.3.5.c")

(test-preproc-1 "c17-std-example2-6.10.3.5.c" "")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "c17-std-example3-6.10.3.5.c")

(test-preproc-1 "c17-std-example3-6.10.3.5.c"
                "
f(2 * (y+1)) + f(2 * (f(2 * (z[0])))) % f(2 * (0)) + t(1);
f(2 * (2+(3,4)-0,1)) | f(2 * (\\~{ } 5)) & f(2 * (0,1))^m(0,1);
int i[] = { 1, 23, 4, 5,  };
char c[2][6] = { \"hello\", \"\" };
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "c17-std-example4-6.10.3.5.c")

(test-preproc-1 "c17-std-example4-6.10.3.5.c"
                "
printf(\"x\" \"1\" \"= %d, x\" \"2\" \"= %s\", x1, x2);
fputs(\"strncmp(\\\"abc\\\\0d\\\", \\\"abc\\\", '\\\\4') == 0\" \": @\\n\", s);
include \"vers2.h\" // omit # in #include to avoid access
\"hello\";
\"hello\" \", world\"
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "c17-std-example5-6.10.3.5.c")

(test-preproc-1 "c17-std-example5-6.10.3.5.c"
                "
int j[] = { 123, 45, 67, 89,
           10, 11, 12,  };
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "c17-std-example6-6.10.3.5.c")

(test-preproc-1 "c17-std-example6-6.10.3.5.c" "")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "c17-std-example7-6.10.3.5.c")

(test-preproc-1 "c17-std-example7-6.10.3.5.c"
                "
fprintf(stderr, \"Flag\");
fprintf(stderr, \"X = %d\\n\", x);
puts(\"The first, second, and third items.\");
((x>y)?puts(\"x>y\"): printf(\"x is %d but y is %d\", x, y));
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "conditional.c")

(test-preproc-1 "conditional.c"
                "M_is_not_defined


M_is_defined
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "gincluder1.c")
; (depends-on "gincluder2.c")
; (depends-on "gincluder1.h")
; (depends-on "gincluder2.h")
; (depends-on "guarded.h")

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
"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "gincludermod1.c")
; (depends-on "gincludermod2.c")
; (depends-on "gincluder1.c")
; (depends-on "gincluder2.c")
; (depends-on "gincluder1.h")
; (depends-on "gincluder2.h")
; (depends-on "guarded.h")

; This is a variant of the previous test in which we have two additional files,
; gincludermod1.c and gincludermod2.c,
; which "modify" f by #define'ing it to be f1 and f2 respectively.
; Thus:
; - guarded.h and gincluder1.h are expanded in gincludermod1.c,
;   but not ginluder2.h
; - guarded.h and gincluder2.h are expanded in gincludermod2.c,
;   but not ginluder1.h

(test-preproc '("gincluder1.c"
                "gincluder2.c"
                "gincludermod1.c"
                "gincludermod2.c")
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
"
                                    "gincludermod1.c"
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
"))
