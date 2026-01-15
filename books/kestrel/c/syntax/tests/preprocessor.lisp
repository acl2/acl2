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
                (cw "Actual:~%~x0" fileset))) ; CW returns nil (see above)
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

(test-preproc-1 "macros.c" "")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-preproc-1 "c17-std-example-6.10.3.3.c" "")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-preproc-1 "c17-std-example-6.10.3.4.c" "")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: handle macro replacement
(test-preproc-1 "c17-std-example1-6.10.3.5.c"
                "
// int table[TABSIZE];
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-preproc-1 "c17-std-example2-6.10.3.5.c" "")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: handle #undef directive
; TODO: handle macro replacement
(test-preproc-1 "c17-std-example3-6.10.3.5.c"
                "// #undef x
// #define x 2

/*
f(y+1) + f(f(z)) % t(t(g)(0) + t)(1);
g(x+(3,4)-w) | h 5) & m
      (f)^m(m);
p() i[q()] = { q(1), r(2,3), r(4,), r(,5), r(,) };
char c[2][6] = { str(hello), str() };
*/
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: handle macro replacement
(test-preproc-1 "c17-std-example4-6.10.3.5.c"
                "
/*
debug(1, 2);
fputs(str(strncmp(\"abc\\0d\", \"abc\", ’\\4’) // this goes away
      == 0) str(: @\\n), s);
#include xstr(INCFILE(2).h)
glue(HIGH, LOW);
xglue(HIGH, LOW)
*/
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: handle macro replacement
(test-preproc-1 "c17-std-example5-6.10.3.5.c"
                "/*
int j[] = { t(1,2,3), t(,4,5), t(6,,7), t(8,9,),
t(10,,), t(,11,), t(,,12), t(,,) };
*/
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: fails ([C17] is ambiguous)
;(test-preproc-1 "c17-std-example6-6.10.3.5.c" "")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: handle macro replacement
(test-preproc-1 "c17-std-example7-6.10.3.5.c"
                "/*
debug(\"Flag\");
debug(\"X = %d\\n\", x);
showlist(The first, second, and third items.);
report(x>y, \"x is %d but y is %d\", x, y);
*/
")
