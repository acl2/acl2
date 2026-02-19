; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
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

(include-book "../../wrap-fn")
(include-book "../utilities")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files '("test1.c")
                   :const *old*)

  (wrap-fn *old*
           *new*
           :targets (("foo" . "wrapper_foo")))

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/test1.c"
    :content "extern double foo(int x, int y);

static double wrapper_foo(int x, int y) {
  return foo(x, y);
}

int main(void) {
  wrapper_foo(0, 1);
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files '("test2.c")
                   :const *old*)

  (wrap-fn *old*
           *new*
           :targets ("foo"))

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/test2.c"
    :content "extern double foo(int x, int y) {
  return 0;
}

static double wrapper_foo(int x, int y) {
  return foo(x, y);
}

int main(void) {
  int (*foo)(double, double) = 0;
  return foo(0.0, 1.0);
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files '("test3.c")
                   :const *old*)

  (wrap-fn *old*
           *new*
           :targets ("foo"))

  (c$::output-files :const *new*
                    :base-dir "new")

  (assert-file-contents
    :file "new/test3.c"
    :content "double foo(int, int *);

static double wrapper_foo(int arg_0, int *arg_1) {
  return foo(arg_0, arg_1);
}

int main(void) {
  return wrapper_foo(0, 0);
}
")

  :with-output-off nil)
