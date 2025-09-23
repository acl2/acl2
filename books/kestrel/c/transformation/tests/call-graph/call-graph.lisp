; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

(include-book "../../../syntax/input-files")
(include-book "../../../syntax/output-files")

(include-book "../../utilities/call-graph")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files
    :const *test*
    :files '("main.c" "file1.c"))

  (defconst *call-graph*
    (call-graph-transunit-ensemble
     (code-ensemble->transunits *test*)))

  (acl2::assert-equal
    *call-graph*
    '((((filepath?)
        (ident (c$::unwrap . "call_main")))
       ((filepath?)
        (ident (c$::unwrap . "main"))))
      (((filepath?)
        (ident (c$::unwrap . "main")))
       ((filepath? (c$::unwrap . "main.c"))
        (ident (c$::unwrap . "foo"))))
      (((filepath? (c$::unwrap . "file1.c"))
        (ident (c$::unwrap . "fibonacci")))
       ((filepath? (c$::unwrap . "file1.c"))
        (ident (c$::unwrap . "fibonacci"))))
      (((filepath? (c$::unwrap . "file1.c"))
        (ident (c$::unwrap . "foo")))
       ((filepath?)
        (ident (c$::unwrap . "call_main"))))
      (((filepath? (c$::unwrap . "main.c"))
        (ident (c$::unwrap . "foo")))
       nil
       ((filepath?)
        (ident (c$::unwrap . "main"))))))

  (defconst *reachable-from-main*
    (call-graph-transitive-closure
      (external-ident (ident "main"))
      *call-graph*))

  (acl2::assert-equal
    *reachable-from-main*
    '(nil
      ((filepath?)
       (ident (c$::unwrap . "main")))
      ((filepath? (c$::unwrap . "main.c"))
       (ident (c$::unwrap . "foo")))))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files
    :const *test*
    :files '("main2.c" "file1.c"))

  (defconst *call-graph*
    (call-graph-transunit-ensemble
     (code-ensemble->transunits *test*)))

  (acl2::assert-equal
    *call-graph*
    '((((filepath?)
        (ident (c$::unwrap . "call_main")))
       ((filepath?)
        (ident (c$::unwrap . "main"))))
      (((filepath?)
        (ident (c$::unwrap . "main")))
       ((filepath? (c$::unwrap . "main2.c"))
        (ident (c$::unwrap . "foo"))))
      (((filepath? (c$::unwrap . "file1.c"))
        (ident (c$::unwrap . "fibonacci")))
       ((filepath? (c$::unwrap . "file1.c"))
        (ident (c$::unwrap . "fibonacci"))))
      (((filepath? (c$::unwrap . "file1.c"))
        (ident (c$::unwrap . "foo")))
       ((filepath?)
        (ident (c$::unwrap . "call_main"))))
      (((filepath? (c$::unwrap . "main2.c"))
        (ident (c$::unwrap . "foo")))
       nil
       ((filepath?)
        (ident (c$::unwrap . "main"))))))

  (defconst *reachable-from-main*
    (call-graph-transitive-closure
      (external-ident (ident "main"))
      *call-graph*))

  (acl2::assert-equal
    *reachable-from-main*
    '(nil
      ((filepath?)
       (ident (c$::unwrap . "main")))
      ((filepath? (c$::unwrap . "main2.c"))
       (ident (c$::unwrap . "foo")))))

  :with-output-off nil)
