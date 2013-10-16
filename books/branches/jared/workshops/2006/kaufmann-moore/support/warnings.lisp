; Illustrate some double-rewrite warnings.

(in-package "ACL2")

(defstub pred (x y) nil)
(defstub foo (x y) nil)

(defun equiv1 (x y)
  (equal x y))
(defun equiv2 (x y)
  (equal x y))
(defun equiv3 (x y)
  (equal x y))

(defequiv equiv1)
(defequiv equiv2)
(defequiv equiv3)

(skip-proofs
 (defcong equiv1 iff (pred x y) 1))

(skip-proofs
 (defcong equiv2 iff (pred x y) 2))

(skip-proofs
 (defcong equiv3 iff (pred x y) 1))
(skip-proofs
 (defcong equiv3 iff (pred x y) 2))

; Warn on two hyps (first for y1, then for y2), only one var each time.
(defaxiom test1
  (implies
   (and (pred x1 y1)  ; Double-rewrite warning for y1, equiv3 and equiv2
        (pred x1 y2)) ; Double-rewrite warning for y2, equiv3 and equiv2
   (pred x1 (list y1 y2))))

; Warn on one hyp, two variables:
; Double-rewrite warning for x1 in hyp 1, equiv3 and equiv1
; Double-rewrite warning for y1 in hyp 1, equiv3 and equiv2
(defaxiom test2
  (implies (pred x1 y1)
           (foo x1 y1)))

; Warn on one hyp, one variable, two occurrences
(defaxiom test3
  (implies (pred x1 x1) ; Double-rewrite warning for x1, 2 occs., all 3 equivs
           (foo x1 y1)))

(defmacro dw (x)
  `(double-rewrite ,x))

; Don't warn on dw calls.
(defaxiom test3-fixed
  (implies (pred (dw x1) (dw x1))
           (foo x1 y1)))

; Double-rewrite warning for x1, 1 occurrence, equiv2 and equiv3
(defaxiom test3-half-fixed
  (implies (pred (dw x1) x1)
           (foo x1 y1)))

; Now for linear stuff.

; Warn on one hyp, two variables:
; Double-rewrite warning for x1 in hyp 1, equiv3 and equiv1
; Double-rewrite warning for y1 in hyp 1, equiv3 and equiv2
(defaxiom lin-test1
  (implies (pred x1 y1)
           (< (foo x1 y1) 17))
  :rule-classes :linear)

; Don't give double-rewrite warning for free var.
(defaxiom lin-test2
  (implies (pred x1 z1) ; Double-rewrite warning for x1, equiv3 and equiv1
           (< (foo x1 y1) 17))
  :rule-classes :linear)

; Two maximal terms.
; Double-rewrite warning for x1, equiv3 and equiv1, trigger (FOO Y1 X1)
; Double-rewrite warning for y1, equiv3 and equiv2, trigger (FOO Y1 X1)
; Double-rewrite warning for x1, equiv3 and equiv1, trigger (FOO X1 Y1)
; Double-rewrite warning for y1, equiv3 and equiv2, trigger (FOO X1 Y1)
(defaxiom lin-test3
  (implies (pred x1 y1)
           (< (+ (foo x1 y1) (foo y1 x1))
              17))
  :rule-classes :linear)

; Right-hand side tests.

; Double-rewrite warning for y1, equiv3 and equiv2, rhs
(defaxiom rhs1
  (iff (pred x1 (list y1 y2))
       (pred x1 y1)))

; Double-rewrite warning for y1, equiv3 and equiv2, hyp and also rhs
(defaxiom rhs2
  (implies (pred x1 y1)
           (iff (pred x1 (list y1 y2))
                (pred x1 y1))))

(skip-proofs
 (defcong equiv1 equal (foo x y) 1))

; Double-rewrite warning for x1/equiv1 for conclusion, trigger term (FOO Y1 X1)
; Double-rewrite warning for y1/equiv1 for conclusion, trigger term (FOO X1 Y1)
(defaxiom rhs-lin
  (<= (foo x1 y1)
      (foo y1 x1))
  :rule-classes :linear)
