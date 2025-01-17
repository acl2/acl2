; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/testing/must-succeed-star" :dir :system)

(include-book "../../../syntax/input-files")
(include-book "../../../syntax/output-files")

(include-book "../../specialize")
(include-book "../utilities")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("test1.c")
                   :const *old*)

  ;; TODO: transformation should define the const
  ;; TODO: transformation should take strings, not idents
  (defconst *new*
    (b* ((const
           (expr-const
             (c$::const-int
               (c$::make-iconst :core (c$::dec/oct/hex-const-dec 1))))))
      (specialize-transunit-ensemble *old*
                                     (c$::ident "foo")
                                     (c$::ident "y")
                                     const)))

  (c$::output-files :const *new*)

  (assert-file-contents
    :file "test1.SPECIALIZE.c"
    :content "int foo(int z) {
  int y = 1;
  int x = 5;
  return x + y - z;
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("test2.c")
                   :const *old*)

  (defconst *new*
    (b* ((const
           (expr-const
             (c$::const-int
               (c$::make-iconst :core (c$::dec/oct/hex-const-dec 42))))))
      (specialize-transunit-ensemble *old*
                                     (c$::ident "foo")
                                     (c$::ident "z")
                                     const)))

  (c$::output-files :const *new*)

  (assert-file-contents
    :file "test2.SPECIALIZE.c"
    :content "int foo(int y) {
  int z = 42;
  int x = 5;
  z++;
  return x + y - z;
}
")

  :with-output-off nil)
