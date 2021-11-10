; Tests of serialize-lambdas.lisp
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "serialize-lambdas-in-term")
(include-book "std/testing/assert-equal" :dir :system)

(assert-equal
 (serialize-lambda-application '((lambda (a b) (foo a b)) b a) nil)
 '((lambda (a-temp)
     ((lambda (a)
        ((lambda (b) (foo a b)) a-temp))
      b))
   a))
