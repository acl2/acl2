; Tests for functions in clean-up-lambdas.lisp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "drop-unused-lambda-bindings")
(include-book "kestrel/utilities/deftest" :dir :system)

;; Drop the binding of __function__(not used in the body), and then drop the
;; entire resulting lambda since it just binds x to itself.
(assert-equal (drop-unused-lambda-bindings '((lambda (__function__ x)
                                               (unsigned-byte-p '8 x))
                                             'n08p
                                             x))
              ;;'(unsigned-byte-p '8 x)
              ;; can be further simplified by drop-trivial-lambdas:
              '((lambda (x)
                 (unsigned-byte-p '8 x))
               x)
              )

;; In this test, we can drop the binding of __function__ but not the entire
;; lambda:
(assert-equal (drop-unused-lambda-bindings '((lambda (__function__ x)
                                               (unsigned-byte-p '8 x))
                                             'n08p
                                             y))
              '((lambda (x) (unsigned-byte-p '8 x)) y))
