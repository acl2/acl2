; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/testing/must-succeed-star" :dir :system)

(include-book "../../../syntax/input-files")
(include-book "../../../syntax/output-files")

(include-book "../../copy-fn")
(include-book "../utilities")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("test1.c")
                   :const *old*)

  ;; TODO: transformation should define the const
  ;; TODO: transformation should take strings, not idents
  (defconst *new*
    (copy-fn-transunit-ensemble *old*
                                (c$::ident "foo")
                                (c$::ident "bar")))

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/test1.c"
    :content "int foo(int y, int z) {
  int x = 5;
  return x + y - z;
}
int bar(int y, int z) {
  int x = 5;
  return x + y - z;
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("fib.c")
                   :const *old*)

  (defconst *new*
    (copy-fn-transunit-ensemble *old*
                                (c$::ident "fibonacci")
                                (c$::ident "fib")))

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/fib.c"
    :content "int fibonacci(int x) {
  if (x <= 1) {
    return x;
  }
  return fibonacci(x - 1) + fibonacci(x - 2);
}
int fib(int x) {
  if (x <= 1) {
    return x;
  }
  return fib(x - 1) + fib(x - 2);
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This example shows the nuance of looking for direct recursive calls. Here,
;; the function foo is within a generic selection, which itself is (needlessly)
;; parenthesized. There is also a statement expression which uses the name of
;; the function as the name of a variable of a different type, which clearly
;; should not be renamed.

(acl2::must-succeed*
  (c$::input-files :files ("generic-selection.c")
                   :gcc t
                   :const *old*)

  (defconst *new*
    (copy-fn-transunit-ensemble *old*
                                (c$::ident "foo")
                                (c$::ident "bar")))

  (c$::output-files :const *new*
                    :path "new"
                    :gcc t)

  (assert-file-contents
    :file "new/generic-selection.c"
    :content "int foo(int x) {
  if (x == 0) {
    return x;
  }
  return (_Generic((x), default: foo))(({
    int foo = x - 1;
    foo;
  }));
}
int bar(int x) {
  if (x == 0) {
    return x;
  }
  return (_Generic((x), default: bar))(({
    int foo = x - 1;
    foo;
  }));
}
")

  :with-output-off nil)
