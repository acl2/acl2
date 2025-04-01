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

(include-book "../../split-fn-proofs")
(include-book "../utilities")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("test1.c")
                   :const *old*)

  (split-fn
    *old*
    *new*
    (c$::ident "foo")
    (c$::ident "bar")
    1
    :proofs t)

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/test1.c"
    :content "int bar(int x, int y) {
  return x + y;
}
int foo(int y) {
  int x = 5;
  return bar(x, y);
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("test2.c")
                   :const *old*)

  (split-fn
    *old*
    *new*
    (c$::ident "add_and_sub_all")
    (c$::ident "sub_all")
    2)

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/test2.c"
    :content "unsigned long sub_all(long arr[], unsigned int len, long total) {
  for (unsigned int i = 0; i < len; i++) {
    total -= arr[i];
  }
  return (unsigned long) total;
}
unsigned long add_and_sub_all(long arr[], unsigned int len) {
  long total = 0l;
  for (unsigned int i = 0; i < len; i++) {
    total += arr[i];
  }
  return sub_all(arr, len, total);
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("test3.c")
                   :process :parse
                   :const *old*)

  (split-fn
    *old*
    *new*
    (c$::ident "foo")
    (c$::ident "baz")
    1)

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/test3.c"
    :content "int w = 42;
int baz(int x, long y, long z) {
  y = bar(x);
  return x + y + z;
}
int foo(int x) {
  long y = 0, z = 5;
  return baz(x, y, z);
}
")

  :with-output-off nil)
