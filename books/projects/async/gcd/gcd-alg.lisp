;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; January 2018

(in-package "ADE")

(local (include-book "arithmetic-5/top" :dir :system))

;; ======================================================================

;; A greatest-common-divisor algorithm

(defun gcd-alg (a b)
  (declare (xargs :guard (and (natp a)
                              (natp b))
                  :measure (nfix (+ a b))))
  (cond ((zp a) (nfix b))
        ((zp b) (nfix a))
        ((equal a b) a)
        ((< a b)
         (gcd-alg a (- b a)))
        (t (gcd-alg (- a b) b))))

(defthm gcd-alg-is-positive
  (implies (or (posp a) (posp b))
           (< 0 (gcd-alg a b)))
  :rule-classes :linear)

(defthmd gcd-alg-commutative
  (equal (gcd-alg a b) (gcd-alg b a))
  :rule-classes ((:rewrite :loop-stopper ((a b)))))

(defthm gcd-alg-is-COMMON-divisor
  (implies (and (natp a)
                (natp b))
           (and (equal (mod a (gcd-alg a b)) 0)
                (equal (mod b (gcd-alg a b)) 0))))

(defthm gcd-alg-is-LARGEST-common-divisor-mod
  (implies (and (equal (mod a d) 0)
                (equal (mod b d) 0))
           (equal (mod (gcd-alg a b) d)
                  0)))

(defthm gcd-alg-is-LARGEST-common-divisor-<=
  (implies (and (or (posp a) (posp b))
                (equal (mod a d) 0)
                (equal (mod b d) 0))
           (<= d (gcd-alg a b))))
