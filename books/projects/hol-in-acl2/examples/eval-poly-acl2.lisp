; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "../acl2/portcullis")

(defun polyp (x)

; A polynomial is a list of pairs (constant . exponent), sorted by decreasing
; order of exponent.  Example:

; '((3 . 2) (5 . 0)) ; 3a^2 + 5a^0 = 3a^2 + 5

  (declare (xargs :guard t))
  (cond ((atom x) (null x))
        (t (let ((m (car x)))  ; monomial
             (and (consp (car x))
                  (let* ((c (car m)) ; coefficient
                         (e (cdr m)) ; exponent
                         (r (cdr x))) ; rest of poly
                    (and (polyp r)
                         (posp c)
                         (natp e)
                         (or (null r)
                             (< (cdar r) ; next exponent
                                e)))))))))

(defun eval-poly (x v)

; Evaluate the polynomial x for the value v.  Example:
; (eval-poly '((3 . 2) (5 . 0)) ; 3a^2 + 5
;            4)
; = 53

  (declare (xargs :guard (and (polyp x)
                              (natp v)))) ; could be (acl2-numberp v)
  (cond ((endp x) 0)
        (t (+ (* (caar x)
                 (expt v (cdar x)))
              (eval-poly (cdr x) v)))))

(defun sum-polys (x y)
  (declare (xargs :guard (and (polyp x)
                              (polyp y))
                  :measure (+ (len x) (len y))))
  (cond ((endp x) y)
        ((endp y) x)
        ((= (cdar x) (cdar y)) ; same exponent
         (cons (cons (+ (caar x)  (caar y))
                     (cdar x))
               (sum-polys (cdr x) (cdr y))))
        ((< (cdar x) (cdar y))
         (cons (car y)
               (sum-polys x (cdr y))))
        (t
         (cons (car x)
               (sum-polys (cdr x) y)))))

; Example showing evaluation of two polynomials to 58 and 78, respectively, as
; being equal to the evaluation of their sum to 58+78 = 131.
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

; Theorem generalizing the example just above:
(defthm eval-poly-sum-polys
  (equal (eval-poly (sum-polys x y) v)
         (+ (eval-poly x v) (eval-poly y v))))

; Just for fun:
(defthm polyp-sum-polys
  (implies (and (polyp x)
                (polyp y))
           (polyp (sum-polys x y))))
