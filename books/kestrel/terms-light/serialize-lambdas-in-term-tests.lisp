; Tests of serialize-lambdas.lisp
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "serialize-lambdas-in-term")
(include-book "std/testing/assert-equal" :dir :system)

;;; :trans (let ((x (+ 1 x)) (y (+ 2 y))) (< x y))
(assert-equal
 (serialize-lambdas-in-term '((lambda (x y) (< x y))
                              (binary-+ '1 x)
                              (binary-+ '2 y))
                            nil)
 '((lambda (x y)
     ((lambda (y x) (< x y))
      (binary-+ '2 y)
      x))
   (binary-+ '1 x)
   y))

;; An example where we have to introduce a temporary:
(assert-equal
 ;; swaps a and b:
 (serialize-lambda-application '((lambda (a b) (foo a b)) b a) nil)
 ;; TODO: Generate something better?
 '((lambda (a-temp b)
     ((lambda (a a-temp)
        ((lambda (b a) (foo a b)) a-temp a))
      b
      a-temp))
   a
   b))
