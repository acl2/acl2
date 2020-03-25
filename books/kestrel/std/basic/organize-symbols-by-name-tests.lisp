; Standard Basic Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "organize-symbols-by-name")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (organize-symbols-by-name nil) nil)

(assert! (let ((result (organize-symbols-by-name '(:in-keyword
                                                   common-lisp::in-common-lisp
                                                   acl2::in-acl2
                                                   std::in-std))))
           (and (set-equiv (strip-cars result)
                           '("IN-KEYWORD"
                             "IN-COMMON-LISP"
                             "IN-ACL2"
                             "IN-STD"))
                (set-equiv (cdr (assoc-equal "IN-KEYWORD" result))
                           '(:in-keyword))
                (set-equiv (cdr (assoc-equal "IN-COMMON-LISP" result))
                           '(common-lisp::in-common-lisp))
                (set-equiv (cdr (assoc-equal "IN-ACL2" result))
                           '(acl2::in-acl2))
                (set-equiv (cdr (assoc-equal "IN-STD" result))
                           '(std::in-std)))))

(assert! (let ((result (organize-symbols-by-name '(:one
                                                   :two
                                                   acl2::one
                                                   std::two
                                                   :three
                                                   acl2::four
                                                   common-lisp::three
                                                   std::one))))
           (and (set-equiv (strip-cars result)
                           '("ONE"
                             "TWO"
                             "THREE"
                             "FOUR"))
                (set-equiv (cdr (assoc-equal "ONE" result))
                           '(:one acl2::one std::one))
                (set-equiv (cdr (assoc-equal "TWO" result))
                           '(:two std::two))
                (set-equiv (cdr (assoc-equal "THREE" result))
                           '(:three common-lisp::three))
                (set-equiv (cdr (assoc-equal "FOUR" result))
                           '(acl2::four)))))
