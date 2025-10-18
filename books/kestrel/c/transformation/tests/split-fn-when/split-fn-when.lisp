; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

(include-book "../../../syntax/input-files")
(include-book "../../../syntax/output-files")

(include-book "../../split-fn-when")
(include-book "../utilities")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files '("test1.c")
                   :const *old*)

  (split-fn-when *old*
                 *new*
                 :triggers "bar")

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/test1.c"
    :content "void bar(int *);
int foo_0(int *x, int *y) {
  bar(&(*y));
  return (*x) + (*y);
}
int foo(int y) {
  int x = 5;
  return foo_0(&x, &y);
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files '("test2.c")
                   :const *old*)

  (split-fn-when *old*
                 *new*
                 :triggers ("setuid" "fork"))

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/test2.c"
    :content "int setuid(int);
int fork(void);
int foo_0_0_0(int ***x, int ***y) {
  setuid((*(*(*x))));
  return (*(*(*x))) + (*(*(*y)));
}
int foo_0_0(int **x, int **y) {
  fork();
  return foo_0_0_0(&x, &y);
}
int foo_0(int *x, int *y) {
  setuid((*y));
  (*x) += 1;
  return foo_0_0(&x, &y);
}
int foo(int y) {
  int x = 5;
  return foo_0(&x, &y);
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files '("test3.c")
                   :const *old*)

  (split-fn-when *old*
                 *new*
                 :triggers "bar")

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/test3.c"
    :content "void bar(int *);
int foo_0(int *x, int *y) {
  bar(&(*y));
  return (*x) + (*y);
}
int foo() {
  int x = 5;
  int y = 0;
  return foo_0(&x, &y);
}
")

  :with-output-off nil)
