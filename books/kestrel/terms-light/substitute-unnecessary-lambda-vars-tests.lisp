; Tests of substitute-unnecessary-lambda-vars
;
; Copyright (C) 2014-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "substitute-unnecessary-lambda-vars")
(include-book "std/testing/assert-equal" :dir :system)

;;the variable b is unnecessarily lambda-bound, because it only appears once in the lambda body:
(assert-event (equal (substitute-unnecessary-lambda-vars-in-term '((lambda (b) (binary-+ b '1)) (bar a)) nil)
                     '(binary-+ (bar a) '1)))

;;the variable a is unnecessarily lambda-bound, because it only appears once in the lambda body:
(assert-event (equal (substitute-unnecessary-lambda-vars-in-term '((lambda (a) ((lambda (b) (binary-+ b b)) (bar a))) (foo x)) nil)
                     '((lambda (b) (binary-+ b b))
                       (bar (foo x)))))

;; Get rid of x.  It's defined in terms of y, but y is still available inside the lambda because it is bound to itself
(assert-equal (substitute-unnecessary-lambda-vars-in-term '((lambda (x y) (binary-+ x (binary-+ y y))) (bar y) y) nil)
              '(binary-+ (bar y) (binary-+ y y)))

;; Can't get rid of x here because it is expressed in terms of y but y is re-bound in the lambda:
(assert-equal (substitute-unnecessary-lambda-vars-in-term '((lambda (x y) (binary-+ x (binary-+ y y))) (bar y) (baz y)) nil)
              '((lambda (x y) (binary-+ x (binary-+ y y))) (bar y) (baz y)) ;no effect
              )
