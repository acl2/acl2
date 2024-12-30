; Tests of the machinery in cancel-addends.lisp
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "cancel-addends")

;; (equal (cancel-in-sum c (+ a (+ b (+ c d)))) (cancel-in-sum c (- c) (+ e (+ f (+ g c)))))

;; Since cancel-in-sum-same can create an addend of 0.
(defthm +-of-0-arg2
    (equal (+ x 0)
           (fix x)))

;; Since cancel-in-sum-of-+-same can put in a call of fix.
;; but often the fix will be expanded?
;more? also fix-of-+ ?
(defthm +-of-fix-arg2
    (equal (+ x (fix y))
           (+ x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tests

;; We use a stub to prevent linear from seeing the equality
(defstub foo (x) t)

;; Test (the C gets cancelled):
(thm
 (implies t ;(acl2-numberp d)
          (equal (foo (equal (+ a (+ b (+ c d))) (+ e (+ f (+ g c)))))
                 (foo (equal (+ a (+ b d)) (+ e (+ f g))))))
 :hints (("Goal" :in-theory '(cancel-common-addend-in-equal
                              cancel-in-sum-of-+-diff
                              cancel-in-sum-of-+-same
                              cancel-in-sum-same
                              +-of-0-arg2
                              +-of-fix-arg2))))

(thm
 (implies (acl2-numberp c) ; drop?
          (equal (foo (equal c (+ e (+ f (+ g c)))))
                 (foo (equal 0 (+ e (+ f g))))))
 :hints (("Goal" :in-theory '(cancel-common-addend-in-equal
                              cancel-in-sum-of-+-diff
                              cancel-in-sum-of-+-same
                              cancel-in-sum-same
                              +-of-0-arg2
                              +-of-fix-arg2))))

;; not a valid test (acl2 knows that x=x)
(thm
 (equal (foo (equal x x))
        (foo t))
 :hints (("Goal" :in-theory '(cancel-common-addend-in-equal
                              cancel-in-sum-of-+-diff
                              cancel-in-sum-of-+-same
                              cancel-in-sum-same))))
