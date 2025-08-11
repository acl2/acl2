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

(include-book "../../constant-propagation")
(include-book "../utilities")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("test1.c")
                   :const *old*)

  (defconst *new*
    (const-prop-code-ensemble *old*))

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/test1.c"
    :content "int foo(void) {
  int x = 0;
  x = 8;
  unsigned int y = -8;
  return 0;
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("test2.c")
                   :process :parse
                   :const *old*)

  (defconst *new*
    (const-prop-code-ensemble *old*))

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/test2.c"
    :content "int foo(int y) {
  int x = 42;
  {
    baz();
  }
  return 0;
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("test3.c")
                   :const *old*)

  (defconst *new*
    (const-prop-code-ensemble *old*))

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/test3.c"
    :content "int foo(int y) {
  int x;
  if (y) {
    x = 0;
  } else {
    x = 0;
  }
  return 0;
}
")

  :with-output-off nil)
