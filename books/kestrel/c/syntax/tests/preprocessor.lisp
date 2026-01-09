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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-preproc '("empty.c")
              :expected (fileset-of "empty.c" ""))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-preproc '("whitespace.c")
              :expected (fileset-of "whitespace.c"
                                    (list 10
                                          32 32 32 10 ; SP SP SP
                                          9 10 ; HT
                                          11 10 ; VT
                                          12 10))) ; FF

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-preproc '("comments.c")
              :expected (fileset-of "comments.c"
                                    "/* block
 * comment
 */

// line comment
"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-preproc '("text.c")
              :expected (fileset-of "text.c"
                                    "int x = 0;

void f(double y) {
  y = 0.1;
}
"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-preproc '("null-directive.c")
              :expected (fileset-of "null-directive.c"
                                    "/*#*/
/* comment */ /*#*/
/*#*/ // comment
/* comment */ /*#*/ // comment
    /*#*/
"))

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
"
                                    ))
