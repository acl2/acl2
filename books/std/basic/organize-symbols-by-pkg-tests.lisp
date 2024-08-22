; Standard Basic Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "organize-symbols-by-pkg")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (organize-symbols-by-pkg nil) nil)

(assert! (let ((result (organize-symbols-by-pkg '(:in-keyword
                                                   common-lisp::in-common-lisp
                                                   acl2::in-acl2
                                                   std::in-std))))
           (and (set-equiv (strip-cars result)
                           '("KEYWORD"
                             "COMMON-LISP"
                             "ACL2"
                             "STD"))
                (set-equiv (cdr (assoc-equal "KEYWORD" result))
                           '(:in-keyword))
                (set-equiv (cdr (assoc-equal "COMMON-LISP" result))
                           '(common-lisp::in-common-lisp))
                (set-equiv (cdr (assoc-equal "ACL2" result))
                           '(acl2::in-acl2))
                (set-equiv (cdr (assoc-equal "STD" result))
                           '(std::in-std)))))

(assert! (let ((result (organize-symbols-by-pkg '(:one
                                                  :two
                                                  acl2::one
                                                  std::two
                                                  :three
                                                  acl2::four
                                                  common-lisp::three
                                                  std::one))))
           (and (set-equiv (strip-cars result)
                           '("KEYWORD"
                             "COMMON-LISP"
                             "ACL2"
                             "STD"))
                (set-equiv (cdr (assoc-equal "KEYWORD" result))
                           '(:one :two :three))
                (set-equiv (cdr (assoc-equal "COMMON-LISP" result))
                           '(common-lisp::three))
                (set-equiv (cdr (assoc-equal "ACL2" result))
                           '(acl2::one acl2::four))
                (set-equiv (cdr (assoc-equal "STD" result))
                           '(std::one std::two)))))
