; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../input-files")
(include-book "../preprocessor")

(include-book "std/testing/assert-bang-stobj" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Build a fileset from alternating paths and contents,
; e.g. (fileset-of "file1.c" "void f() {}" "file2.c" "int g(int x);").

(defmacro fileset-of (&rest paths+contents)
  `(fileset (fileset-map (list ,@paths+contents))))

(defun fileset-map (paths+contents)
  (b* (((when (endp paths+contents)) nil)
       (path (car paths+contents))
       (content (cadr paths+contents))
       (content (if (stringp content)
                    (acl2::string=>nats content)
                  content)))
    (omap::update (filepath path)
                  (filedata content)
                  (fileset-map (cddr paths+contents)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Turn fileset into map from strings to strings.

(defun fileset-map-to-string-map (fileset-map)
  (b* (((when (omap::emptyp fileset-map)) nil)
       ((mv filepath filedata) (omap::head fileset-map)))
    (omap::update (filepath->unwrap filepath)
                  (acl2::nats=>string (filedata->unwrap filedata))
                  (fileset-map-to-string-map (omap::tail fileset-map)))))

(defun fileset-to-string-map (fileset)
  (fileset-map-to-string-map (fileset->unwrap fileset)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check result of preprocessing against expectation.

(defmacro test-preproc (files &key expected)
  `(assert!-stobj
    (b* ((files ,files)
         (base-dir ".")
         (include-dirs nil)
         (ienv (ienv-default))
         ((mv erp fileset state)
          (pproc-files files base-dir include-dirs ienv state 1000000000)))
      (mv (if erp
              (cw "~@0" erp) ; CW returns NIL, so ASSERT!-STOBJ fails
            (or (equal fileset ,expected)
                (cw "Actual:~%~x0" ; CW returns nil (see above)
                    (fileset-to-string-map fileset))))
          state))
    state))

;;;;;;;;;;;;;;;;;;;;

; Specialization to one file.

(defmacro test-preproc-1 (file expected)
  `(test-preproc '(,file)
                 :expected (fileset-of ,file ,expected)))

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
++uu; // needs a space: + +uu
+x+y;
++7; // needs a space: + +7

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
; TODO: printer must add space where needed (see comments)

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
