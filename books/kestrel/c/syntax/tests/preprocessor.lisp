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

(test-preproc-1 "empty.c" "")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-preproc-1 "whitespace.c"
                (list 10
                      32 32 32 10 ; SP SP SP
                      9 10 ; HT
                      11 10 ; VT
                      12 10)) ; FF

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-preproc-1 "comments.c"
                "/* block
 * comment
 */

// line comment
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-preproc-1 "text.c"
                "int x = 0;

void f(double y) {
  y = 0.1;
}
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-preproc-1 "null-directive.c"
                "/*#*/
/* comment */ /*#*/
/*#*/ // comment
/* comment */ /*#*/ // comment
    /*#*/
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(test-preproc-1 "concatenate.c"
                "
a b cd e;
x334;
6e+8P-;
>>=;
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-preproc-1 "c17-std-example-6.10.3.3.c" "")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-preproc-1 "c17-std-example-6.10.3.4.c"
                "
2*9*g
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-preproc-1 "c17-std-example1-6.10.3.5.c"
                "
int table[100];
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-preproc-1 "c17-std-example2-6.10.3.5.c" "")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-preproc-1 "c17-std-example3-6.10.3.5.c"
                "
f(2 * (y+1)) + f(2 * (f(2 * (z[0])))) % f(2 * (0)) + t(1);
f(2 * (2+(3,4)-0,1)) | f(2 * (\\~{ } 5)) & f(2 * (0,1))^m(0,1);
int i[] = { 1, 23, 4, 5,  };
char c[2][6] = { \"hello\", \"\" };
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-preproc-1 "c17-std-example4-6.10.3.5.c"
                "
printf(\"x\" \"1\" \"= %d, x\" \"2\" \"= %s\", x1, x2);
fputs(\"strncmp(\\\"abc\\\\0d\\\", \\\"abc\\\", '\\\\4') == 0\" \": @\\n\", s);
include \"vers2.h\" // omit # in #include to avoid access
\"hello\";
\"hello\" \", world\"
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-preproc-1 "c17-std-example5-6.10.3.5.c"
                "
int j[] = { 123, 45, 67, 89,
           10, 11, 12,  };
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-preproc-1 "c17-std-example6-6.10.3.5.c" "")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-preproc-1 "c17-std-example7-6.10.3.5.c"
                "
fprintf(stderr, \"Flag\");
fprintf(stderr, \"X = %d\\n\", x);
puts(\"The first, second, and third items.\");
((x>y)?puts(\"x>y\"): printf(\"x is %d but y is %d\", x, y));
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-preproc-1 "conditional.c"
                "M_is_not_defined


M_is_defined
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;; (test-preproc '("gincluder.c")
;;               :expected (fileset-of))
