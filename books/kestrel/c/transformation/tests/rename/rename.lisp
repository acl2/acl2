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

(include-book "../../rename")
(include-book "../utilities")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("test1.c")
                   :const *old*)

  ;; TODO: transformation should define the const
  ;; TODO: transformation should take strings, not idents
  (defconst *new*
    (rename-transunit-ensemble *old*
                               (acons (c$::ident "main") (c$::ident "entry")
                                      (acons (c$::ident "x") (c$::ident "y")
                                             nil))))
  (c$::output-files :const *new*)

  (assert-file-contents
    :file "test1.RENAME.c"
    :content "int entry() {
  int y = 5;
  return y + 0;
}
")

  :with-output-off nil)
