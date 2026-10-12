; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "../acl2/portcullis")

(defun polyp (x)

; A polynomial is a list of pairs (constant . exponent), sorted by decreasing
; exponent.  Example:

; '((3 . 2) (5 . 0)) ; 3a^2 + 5a^0 = 3a^2 + 5

  (declare (xargs :guard t))
  (cond ((atom x) (null x))
        (t (let ((m (car x)))  ; first monomial
             (and (consp (car x))
                  (let* ((c (car m)) ; coefficient of m
                         (e (cdr m)) ; exponent of m
                         (r (cdr x))) ; rest of poly
                    (and (polyp r)
                         (posp c)
                         (natp e)
                         (or (null r)
                             (< (cdr (car r)) ; next exponent
                                e)))))))))

(defun eval-poly (x v)

; Evaluate the polynomial x for the value v.  Example:

; (eval-poly '((3 . 2) (5 . 0)) ; 3a^2 + 5
;            4)                 ; where a = 4
; = 53

  (declare (xargs :guard (and (polyp x)
                              (natp v)))) ; could be (acl2-numberp v)
  (cond ((endp x) 0)
        (t (+ (* (car (car x))
                 (expt v (cdr (car x))))
              (eval-poly (cdr x) v)))))

(defun sum-polys (x y)

; Add the two given polynomials to produce a new polynomial.  The recursion
; here ensures that the result is sorted by decreasing exponent, as is
; required by polyp.

  (declare (xargs :guard (and (polyp x)
                              (polyp y))
                  :measure (+ (len x) (len y))))
  (cond ((endp x) y)
        ((endp y) x)
        ((= (cdr (car x)) (cdr (car y))) ; same exponent
         (cons (cons (+ (car (car x))  (car (car y)))
                     (cdr (car x)))
               (sum-polys (cdr x) (cdr y))))
        ((< (cdr (car x)) (cdr (car y)))
         (cons (car y)
               (sum-polys x (cdr y))))
        (t
         (cons (car x)
               (sum-polys (cdr x) y)))))

; Here is an example showing the evaluation of two polynomials to 53 and 78,
; respectively, where the sum of those polynomials evaluates to 53+78 = 131.
(thm (and (equal (eval-poly '((3 . 2) (5 . 0)) 4) ; 3a^2 + 5a^0
                 53)
          (equal (eval-poly '((4 . 2) (3 . 1) (2 . 0)) 4) ; 4a^2 + 3a^1 + 2a^0
                 78)
          (equal (sum-polys '((3 . 2) (5 . 0))
                            '((4 . 2) (3 . 1) (2 . 0)))
                 '((7 . 2) (3 . 1) (7 . 0)))
          (equal (eval-poly (sum-polys '((3 . 2) (5 . 0))
                                       '((4 . 2) (3 . 1) (2 . 0)))
                            4)
                 131)))

; The following theorem generalizes the example just above.
(defthm eval-poly-sum-polys
  (equal (eval-poly (sum-polys x y) v)
         (+ (eval-poly x v) (eval-poly y v))))

; Here is an extra theorem, just for fun.
(defthm polyp-sum-polys
  (implies (and (polyp x)
                (polyp y))
           (polyp (sum-polys x y))))
