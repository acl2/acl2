; Copyright (C) 2020, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; On February 28, 2020, Dave Greve asked the acl2-help list "if it would be
; possible to define a `generic' k-induction schema that could be instantiated
; at proof time".  I believe that this book provides a positive answer to that
; question.

(in-package "ACL2")

; Introduce generic predicate on a natural number n and a list of parameters,
; together with a positive "k" for k-induction and a "badguy" that provides,
; when the predicate fails on n, for a natural number i with n-k <= i < n such
; that the predicate fails on i.
(encapsulate
  ((pk (n params) t)
   (pk-k () t)
   (pk-badguy (n params) t))

  (local (defun pk (n params)
           (declare (ignore n params))
           t))

  (local (defun pk-k ()
           1))

  (local (defun pk-badguy (n params)
           (declare (ignore n params))
           0))

  (defthm posp-pk-k ; could include 0, I think
    (posp (pk-k))
    :rule-classes :type-prescription)

  (defthm natp-pk-badguy
    (natp (pk-badguy n params))
    :rule-classes :type-prescription)

  (defthm pk-badguy-range
    (implies (and (natp n)
                  (not (pk n params)))
             (and (< (pk-badguy n params)
                     n)
                  (>= (pk-badguy n params)
                      (- n (pk-k)))))
    :rule-classes (:linear :rewrite))

  (defthm pk-badguy-is-counterexample
    (implies (and (natp n)
                  (not (pk n params)))
             (not (pk (pk-badguy n params) params)))))

(defun pk-induction (n params)
  (if (or (zp n) (pk n params))
      t
    (pk-induction (pk-badguy n params) params)))

(defthm pk-0
  (pk 0 params)
  :hints (("Goal" :use ((:instance pk-badguy-range (n 0))))))

(defthm pk-holds
  (implies (natp n)
           (pk n params))
  :hints (("Goal" :induct (pk-induction n params))))

; Below is an example for how to apply k-induction with k=3.  It is quite
; artificial, and surely there are opportunities for the use of macros, and
; perhaps a fancier :functional-instance hint, to simplify the process.  But
; this basic example shows how to apply k-induction in ACL2.

(encapsulate
  ((q (n x y) t))
  (local (defun q (n x y)
           (declare (ignore n x y))
           t))
  (defthm q-3-properties
    (and (q 0 x y)
         (q 1 x y)
         (q 2 x y)
         (implies (and (natp n)
                       (<= 3 n)
                       (q (- n 3) x y)
                       (q (- n 2) x y)
                       (q (- n 1) x y))
                  (q n x y)))))

; Introduce a version of our predicate that takes only two arguments, so that
; the resulting predicate has the same signature as pk.
(defun q-params (n params)
  (q n (nth 0 params) (nth 1 params)))

; Define a counterexample function, so that if q-params fails for n then when
; this function is called on n at the top level, then it returns i such that
; n-3 <= i < n.
(defun q-params-badguy (n params)
  (cond ((zp n) 0) ; no badguy
        ((not (q-params (- n 1) params))
         (- n 1))
        ((equal n 1) 0) ; no badguy
        ((not (q-params (- n 2) params))
         (- n 2))
        ((equal n 2) 0) ; no badguy
        (t (- n 3))))

; The following illustrates Greve's requirement, "instantiated at proof time".
(defthmd q-params-holds
  (implies (natp n)
           (q-params n params))
  :hints (("Goal" :use ((:functional-instance pk-holds
                                              (pk q-params)
                                              (pk-k (lambda () 3))
                                              (pk-badguy q-params-badguy))))))

; We can now trivially derive the desired result.
(defthm q-holds
  (implies (natp n)
           (q n x y))
  :hints (("Goal" :use ((:instance q-params-holds
                                   (params (list x y)))))))
