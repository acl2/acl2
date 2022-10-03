;; Author: Grant Jurgensen (grant@kestrel.edu)

(in-package "ACL2")

(include-book "find-a-base-case")

(include-book "std/testing/must-succeed-star" :dir :system)
(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-fail-with-hard-error" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test find-a-base-case-translated

(must-succeed*
 (defun f (x)
   (declare (xargs :guard (natp x)))
   (if (zp x)
       (1+ x)
     (1+ (f (- x 1)))))

 (assert-equal
  '(binary-+ '1 x)
  (find-a-base-case-translated
   '(IF (ZP X)
        (BINARY-+ '1 X)
        (BINARY-+ '1 (F (BINARY-+ '-1 X))))
   '(f)
   t))

 (assert-equal
  '(binary-+ '1 x)
  (find-a-base-case-translated
   '(IF (ZP X)
        (BINARY-+ '1 X)
        (BINARY-+ '1 (F (BINARY-+ '-1 X))))
   '(f)
   nil))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test find-a-base-case-translated on multiple-base-cases term

(must-succeed*
 (defun f (x)
   (declare (xargs :guard (natp x)))
   (if (zp x)
       (if nil
           (f (- x 1))
         (1+ x))
     (if (< 1 x)
         (1+ (f (- x 1)))
       0)))

 (assert-equal
  '(binary-+ '1 x)
  (find-a-base-case-translated
   '(IF (ZP X)
        (IF 'NIL
            (F (BINARY-+ '-1 X))
            (BINARY-+ '1 X))
        (IF (< '1 X)
            (BINARY-+ '1 (F (BINARY-+ '-1 X)))
            '0))
   '(f)
   t))

 (assert-equal
  ''0
  (find-a-base-case-translated
   '(IF (ZP X)
        (IF 'NIL
            (F (BINARY-+ '-1 X))
            (BINARY-+ '1 X))
        (IF (< '1 X)
            (BINARY-+ '1 (F (BINARY-+ '-1 X)))
            '0))
   '(f)
   nil))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test find-a-base-case

(must-succeed*
 (defun f (x)
   (declare (xargs :guard (natp x)))
   (if (zp x)
       (if nil
           (f (- x 1))
         (1+ x))
     (if (< 1 x)
         (1+ (f (- x 1)))
       0)))

 (assert-equal
  '(1+ x)
  (find-a-base-case
   '(if (zp x)
        (if nil
            (f (- x 1))
          (1+ x))
      (if (< 1 x)
          (1+ (f (- x 1)))
        0))
   '(f)
   nil
   t
   state))

 (assert-equal
  '0
  (find-a-base-case
   '(if (zp x)
        (if nil
            (f (- x 1))
          (1+ x))
      (if (< 1 x)
          (1+ (f (- x 1)))
        0))
   '(f)
   nil
   nil
   state))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test find-a-base-case with fake-fns

(must-succeed*
 (assert-equal
  '(1+ x)
  (find-a-base-case
   '(if (zp x)
        (if nil
            (f (- x 1))
          (1+ x))
      (if (< 1 x)
          (1+ (f (- x 1)))
        0))
   nil
   '((f . 1))
   t
   state))

 (assert-equal
  '0
  (find-a-base-case
   '(if (zp x)
        (if nil
            (f (- x 1))
          (1+ x))
      (if (< 1 x)
          (1+ (f (- x 1)))
        0))
   nil
   '((f . 1))
   nil
   state))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test find-a-base-case with flet

(must-succeed*
 (defun f (x)
   (declare (xargs :guard (natp x)))
   (if (zp x)
       (flet ((f (x) x))
         (f (1+ x)))
     (1+ (f (- x 1)))))

 (assert-equal
  '(flet ((f (x) x)) (f (1+ x)))
  (find-a-base-case
   '(if (zp x)
        (flet ((f (x) x))
          (f (1+ x)))
      (1+ (f (- x 1))))
   '(f)
   nil
   t
   state))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test find-a-base-case on macro forms

(must-succeed*
 (defun f (x)
   (declare (xargs :guard (natp x)))
   (cond ((zp x)
          (cond (nil (f (- x 1)))
                (t (1+ x))))
         (t
          (cond ((< 1 x) (1+ (f (- x 1))))
                (t 0)))))

 (assert-equal
  '(1+ x)
  (find-a-base-case
   '(cond ((zp x)
           (cond (nil (f (- x 1)))
                 (t (1+ x))))
          (t
           (cond ((< 1 x) (1+ (f (- x 1))))
                 (t 0))))
   '(f)
   nil
   t
   state))

 (assert-equal
  '0
  (find-a-base-case
   '(cond ((zp x)
           (cond (nil (f (- x 1)))
                 (t (1+ x))))
          (t
           (cond ((< 1 x) (1+ (f (- x 1))))
                 (t 0))))
   '(f)
   nil
   nil
   state))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test find-a-base-case with multiple fns

(must-succeed*
 (defun f (x)
   (declare (xargs :guard t))
   x)

 (defun g (x)
   (declare (xargs :guard (natp x)))
   (if (zp x)
       (if (equal 1 x)
           (f 1)
         (1+ x))
     (1+ (g (- x 1)))))

 (assert-equal
  '(if (equal 1 x) (f 1) (1+ x))
  (find-a-base-case
   '(if (zp x)
        (if (equal 1 x)
            (f 1)
          (1+ x))
      (1+ (g (- x 1))))
   '(g)
   nil
   t
   state))

 (assert-equal
  '(1+ x)
  (find-a-base-case
   '(if (zp x)
        (if (equal 1 x)
            (f 1)
          (1+ x))
      (1+ (g (- x 1))))
   '(f g)
   nil
   t
   state))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test find-a-base-case failure when no base-case

(must-fail-with-hard-error
 (find-a-base-case
  '(if (zp x)
       (f (1+ x))
     (if (< 1 x)
         (1+ (f (- x 1)))
       (f 0)))
  nil
  '((f . 1))
  t
  state))
