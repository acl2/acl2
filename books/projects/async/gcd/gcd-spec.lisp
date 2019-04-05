;; Copyright (C) 2018, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; March 2019

(in-package "ADE")

(include-book "../comparators/v-less")

(local (include-book "gcd-alg"))
(local (include-book "../adders/subtractor"))

(local (include-book "arithmetic-3/top" :dir :system))

;; ======================================================================

;; A greatest-common-divisor specification

(local
 (defthm v-<-correct-instance
   (implies (and (natp data-size)
                 (equal (len x) (* 2 data-size))
                 (bvp x)
                 (v-< nil t
                      (rev (take data-size x))
                      (rev (nthcdr data-size x))))
            (< (v-to-nat (take data-size x))
               (v-to-nat (nthcdr data-size x))))
   :hints (("Goal"
            :use (:instance v-<-correct-1
                            (a (take data-size x))
                            (b (nthcdr data-size x)))
            :in-theory (disable v-<-correct-1)))
   :rule-classes :linear))

(local
 (defthm v-to-nat-of-v-zp
   (equal (v-zp x)
          (equal (v-to-nat x) 0))
   :hints (("Goal" :in-theory (enable v-zp v-nzp v-to-nat)))))

(local
 (defun my-count (x)
   (nfix (+ (v-to-nat (take (/ (len x) 2) x))
            (v-to-nat (nthcdr (/ (len x) 2) x))))))

(local
 (defun gcd$op (x)
   (declare (xargs :hints (("Goal"
                            :in-theory (e/d ()
                                            (v-not-take
                                             v-not-nthcdr))))
                   :measure (my-count x)))
   (b* ((data-size (/ (len x) 2))
        (a (take data-size x))
        (b (nthcdr data-size x))
        (a-b (v-adder-output t a (v-not b)))
        (b-a (v-adder-output t b (v-not a)))
        (a<b (v-< nil t (rev a) (rev b))))
     (cond
      ((or (atom x)
           (zp data-size)
           (not (bvp x)))
       x)
      ((v-zp a) b)
      ((v-zp b) a)
      ((equal a b) a)
      (t (gcd$op
          (v-if a<b
                (append b-a a)
                (append a-b b))))))))

(defun gcd$op (x)
  (declare (xargs :measure (:? x)))
  (b* ((data-size (/ (len x) 2))
       (a (take data-size x))
       (b (nthcdr data-size x))
       (a-b (v-adder-output t a (v-not b)))
       (b-a (v-adder-output t b (v-not a)))
       (a<b (v-< nil t (rev a) (rev b))))
    (cond
     ((or (atom x)
          (zp data-size)
          (not (bvp x)))
      x)
     ((v-zp a) b)
     ((v-zp b) a)
     ((equal a b) a)
     (t (gcd$op
         (v-if a<b
               (append b-a a)
               (append a-b b)))))))

(defthm bvp-gcd$op
  (implies (and (natp (/ (len x) 2))
                (bvp x))
           (bvp (gcd$op x))))

(defthm len-gcd$op
  (implies (and (natp (/ (len x) 2))
                (bvp x))
           (equal (len (gcd$op x))
                  (/ (len x) 2))))

(local
 (defthm gcd$op-lemma-aux
   (implies (and (bv2p a b)
                 (not (v-< nil t (rev a) (rev b)))
                 (equal (v-to-nat a) 0))
            (equal a b))
   :hints (("Goal" :use (v-to-nat-equality
                         v-<-correct-2)))
   :rule-classes nil))

(local
 (defthm v-adder-output-lemma
   (implies (atom a)
            (not (v-adder-output c a b)))
   :hints (("Goal" :in-theory (enable v-adder-output)))))

(defthm gcd$op-lemma
  (b* ((a (take data-size x))
       (b (nthcdr data-size x))
       (a-b (v-adder-output t a (v-not b)))
       (b-a (v-adder-output t b (v-not a)))
       (a<b (v-< nil t (rev a) (rev b))))
    (implies (and (natp data-size)
                  (equal data-size (/ (len x) 2))
                  (bvp x))
             (equal (gcd$op (v-if a<b
                                  (append b-a a)
                                  (append a-b b)))
                    (gcd$op x))))
  :hints (("Goal"
           :induct (gcd$op x)
           :in-theory (e/d ()
                           (v-to-nat-equality
                            v-not-take
                            v-not-nthcdr)))
          ("Subgoal *1/3"
           :use (:instance
                 v-to-nat-equality
                 (a (v-adder-output t
                                    (take data-size x)
                                    (v-not (nthcdr data-size x))))
                 (b (take data-size x))))
          ("Subgoal *1/2"
           :use ((:instance
                  v-to-nat-equality
                  (a (v-adder-output t
                                     (nthcdr data-size x)
                                     (v-not (take data-size x))))
                  (b (nthcdr data-size x)))
                 (:instance
                  gcd$op-lemma-aux
                  (a (take data-size x))
                  (b (nthcdr data-size x)))))))

;; Prove that gcd$op correctly computes the greatest common divisor

(local
 (defthm v-to-nat-of-GCD$OP-is-GCD-ALG
   (implies (and (equal data-size (/ (len x) 2))
                 (bvp x))
            (equal (v-to-nat (gcd$op x))
                   (gcd-alg (v-to-nat (take data-size x))
                            (v-to-nat (nthcdr data-size x)))))
   :hints (("Goal" :in-theory (e/d ()
                                   (v-not-take
                                    v-not-nthcdr))))))

(in-theory (disable gcd$op))

(defthmd gcd$op-commutative
  (implies (bv2p a b)
           (equal (gcd$op (append a b))
                  (gcd$op (append b a))))
  :hints (("Goal"
           :use (:instance v-to-nat-equality
                           (a (gcd$op (append a b)))
                           (b (gcd$op (append b a))))
           :in-theory (e/d (gcd-alg-commutative)
                           (v-to-nat-equality))))
  :rule-classes ((:rewrite :loop-stopper ((a b)))))

;; The operation of GCD over a data sequence

(defun gcd$op-map (x)
  (if (atom x)
      nil
    (cons (gcd$op (car x))
          (gcd$op-map (cdr x)))))

(defthm len-of-gcd$op-map
  (equal (len (gcd$op-map x))
         (len x)))

(defthm gcd$op-map-of-append
  (equal (gcd$op-map (append x y))
         (append (gcd$op-map x) (gcd$op-map y))))


