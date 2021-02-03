; This book provides a few basic checks on our handling of syntax for parallel
; evaluation.

(in-package "ACL2")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/assert-bang-stobj" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed" :dir :system)
;(include-book "make-event/dotimes" :dir :system)

(defun plet-test10 ()
  (declare (xargs :guard t))
  (plet ((x 4)
         (y 6))
        (+ x y)))

(assert! (equal (plet-test10) 10))

(must-fail
 (make-event
  '(let ((q 10)) (plet ((x 4) (y (+ 9 q))) (+ x y)))))

(must-succeed
 (set-parallel-execution nil))

(assert!
 (and (pand)
      (pand (equal 4 4))
      (pand (equal 4 4) (equal 6 6) (equal 9 9) (equal 1 1) (equal 5 5))
      (not (pand (equal 4 5)))
      (not (pand (equal 4 4) (equal 4 5)))
      (not (pand (equal 1 1) (equal 2 3) (equal 1 1)))
      (pand '(consp 3))
      (not (pand (consp 3)))))

(assert!
 (and (por '(consp 3))
      (not (por (consp 3)))))

(defun pfib (x)
  (declare (xargs :guard (natp x)))
  (cond ((or (zp x) (<= x 0)) 0)
        ((= x 1) 1)
        (t (pargs
            (declare (granularity (> x 15)))
            (binary-+ (pfib (- x 1))
                      (pfib (- x 2)))))))

(must-succeed
 (assert! (equal (pfib 10) 55)))

; Test the ability of plet to bind variables in weird locations.

; First, use the lexical variable q inside the binding of the plet.
(assert!
 (equal
  (let ((q 10))
    (plet ((x 4)
           (y (+ 9 q)))
          (+ x y)))
  23))

; Second, use the lexical variable q inside the body of the plet.
(assert!
 (equal
  (let ((q 10))
    (plet ((x 4)
           (y 9))
          (+ x y q)))
  23))

; Finally, use the lexical variable q inside both the binding and the body of
; the plet.
(assert!
 (equal
  (let ((q 10))
    (plet ((x 4)
           (y (+ 9 q)))
          (+ x y q)))
  33))

(assert!
 (equal
  (plet () 4)
  4))

(must-fail
 (make-event
  '(value-triple (pargs 4))))

; Can use globals in plet bindings (of course!).
(defconst *tmp* 4)
(assert! (equal (plet ((x *tmp*)) x)
                4))

(defun test-granularity1 (x)
  (declare (xargs :guard (natp x)))
  (pargs
   (declare (granularity (> x 5)))
   (binary-+ x x)))

; Needs to error
(must-fail
 (defun test-granularity2 (x)
   (declare (xargs :guard (natp x)))
   (pargs
    (declare (wrong-name (> x 5)))
    (binary-+ x x))))

(defun foo-por-check (x)
  (declare (xargs :guard (natp x)))
  (por (+ x x) 20))

(defun foo-por-check2 (x)
  (declare (xargs :guard (natp x)))
  (por
   (declare (granularity (< x 5)))
   (+ x x) 20))

(defun foo-pand-check (x)
  (declare (xargs :guard (natp x)))
  (pand (+ x x) *tmp* 20))

(defun foo-pand-check2 (x)
  (declare (xargs :guard (natp x)))
  (pand
   (declare (granularity (< x 5)))
   (+ x x) *tmp* 20))

; The below should not admit because of guard violations.  Pand is different
; from And!
(must-fail
 (defun error-pand (x)
   (declare (xargs :guard t))
   (pand (consp x)
         (equal (car x) 4))))

; The below should not admit because of guard violations.  Por is different
; from Or!
(must-fail
 (defun error-por (x)
   (declare (xargs :guard t))
   (por (atom x)
        (equal (car x) 4))))

; The below should not admit, because it doesn't make sense to pargs a let or a
; plet!
(must-fail
 (defun pargs-let ()
   (pargs
    (let ((x 4)
          (y 5))
      (+ x y)))))

(must-fail
 (defun pargs-plet ()
   (pargs
    (plet ((x 4)
           (y 5))
          (+ x y)))))

(defstobj foo field1 field2)

; These are OK because plet devolves into let for a single binding:
(local
 (encapsulate
  ()

  (defun test-stobj (x foo)
    (declare (xargs :stobjs foo))
    (plet ((foo (update-field1 17 foo)))
          (update-field2 x foo)))

  (assert!-stobj (let* ((foo (test-stobj 14 foo)))
                   (mv (equal (field1 foo)
                              17)
                       foo))
                 foo)

  (assert!-stobj (let* ((foo (test-stobj 14 foo)))
                   (mv (equal (field1 foo)
                              17)
                       foo))
                 foo)

  (assert!-stobj (let* ((foo (test-stobj 14 foo)))
                   (mv (equal (field1 foo)
                              17)
                       foo))
                 foo)

  (must-fail
   (assert!-stobj (let* ((foo (test-stobj 14 foo)))
                    (mv (equal (field1 foo)
                               14)
                        foo))
                  foo))
  ))

(must-fail
 (defun test-stobj-pwrite (foo)
   (declare (xargs :stobjs foo
                   :guard (and (acl2-numberp (field1 foo))
                               (acl2-numberp (field2 foo)))))
   (plet ((foo (update-field1 foo 14))
          (foo (update-field2 foo 15)))
         (field1 foo))))

(defstobj bar fieldA fieldB)

(defun init-stobj-bar (bar)
  (declare (xargs :stobjs bar))
  (plet ((bar (update-fielda 7 bar)))
        (update-fieldb 14 bar)))

(defun test-stobj-pread (bar)
  (declare (xargs :stobjs bar
                  :guard (and (acl2-numberp (fielda bar))
                              (acl2-numberp (fieldb bar)))))
  (plet ((bar1 (fielda bar))
         (bar2 (fieldb bar)))
        (+ bar1 bar2)))

(defun init-stobj-bar2 (bar)
  (declare (xargs :stobjs bar))
  (plet ((bar (update-fielda 17 bar)))
        (update-fieldb 14 bar)))

(must-succeed
 (defun plet-declare-test0 (x)
   (declare (xargs :guard (integerp x)))
   (plet (declare (granularity (> x 4)))
         ((y x)
          (z 8))
         (declare (ignore z))
         y)))

(must-fail
 (defun plet-declare-test1 (x)
   (declare (xargs :guard t))
   (plet (declare (granularity (> x 4)))
         ((y x)
          (z 8))
         (declare (ignore z))
         y)))

(must-succeed
 (defun plet-declare-test2 (x)
   (declare (xargs :guard (integerp x)))
   (plet (declare (granularity (> x 4)))
         ((y x)
          (z 8)
          (booga 'the_clouds))
         (declare (ignore z))
         (declare (ignore booga))
         y)))

(must-fail
 (defun plet-declare-test3 (x)
   (declare (xargs :guard (integerp x)))
   (plet (declare (granularity (> x 4)))
         ((y x) (z 8))
         (declare (ignore z))
         (declare (fixnum y))
         y)))

(must-fail
 (defun plet-declare-test4 (x)
   (declare (xargs :guard (integerp x)))
   (plet (declare (granularity (> x 4)))
         ((y x) (z 8))
         (declare (fixnum y))
         y)))

(must-fail
 (defun let-declare-test0 (x)
   (declare (xargs :guard t))
   (let ((y x)
         (z 8))
     (declare (ignore z))
     y y)))
