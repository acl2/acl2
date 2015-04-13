; Copyright (C) 2015, Regents of the University of Texas
; Written by Matt Kaufmann in consultation with Cuong Chau, April, 2015
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; cert_param: (uses-acl2r)

(in-package "ACL2")

; Formalization of the overspill property in ACL2(r)

; The first main result in this book is as follows.  The details of functions
; large-n-for-overspill-p and overspill-p-failure-witness don't matter here;
; what's important is that overspill-p is an arbitrary classical function with
; trivial constraint of t.

;   (defthm overspill-p-overspill
;     (let ((n (large-n-for-overspill-p x))
;           (k (overspill-p-failure-witness x)))
;       (or (and (natp k)
;                (standardp k)
;                (not (overspill-p k x)))
;           (and (natp n)
;                (i-large n)
;                (overspill-p n x))))
;     :hints ...
;     :rule-classes nil)

; Suppose that you functionally instantiate the above lemm to a lemma
; p-overspill, where p-overspill is bound to your own predicate, (p n x).  Also
; suppose that you prove a theorem of the form:

;   (implies (and (hyps x) (natp i) (standardp i))
;            (p i x))

; Then you can easily conclude the following, saying that p "overspills" to
; some nonstandard n:

;   (implies (hyps x)
;            (let ((n (large-n-for-overspill-p x)))
;              (and (natp n)
;                   (overspill-p n x)
;                   (i-large n)))

; In the second half of this book we extend this result to "overspill" a
; predicate in a stronger sense, namely, so that the predicate holds for all
; natural numbers less than some nonstandard n.

;   (defthm overspill-p-overspill-strong
;     (let ((n (large-n-for-overspill-p* x))
;           (k (least-overspill-p-failure (overspill-p*-failure-witness x)
;                                         x)))
;       (or (and (natp k)
;                (standardp k)
;                (not (overspill-p k x)))
;           (and (natp n)
;                (i-large n)
;                (implies (and (natp m)
;                              (<= m n))
;                         (overspill-p m x)))))
;     :hints ...
;     :rule-classes nil)

(defstub overspill-p (n x) t)

(defchoose choose-n-for-not-overspill-p (n) (x)
  (and (natp n)
       (not (overspill-p n x))))

(defun large-n-for-overspill-p-aux (n x)

; Return the first n' reached below n, as we count down, such that (overspill-p
; n' x).

  (cond ((zp n)
         0)
        ((overspill-p n x)
         n)
        (t (large-n-for-overspill-p-aux (1- n) x))))

(defun large-n-for-overspill-p (x)
  (let ((n (choose-n-for-not-overspill-p x)))
    (if (not (and (natp n)
                  (not (overspill-p n x))))
        (i-large-integer)
      (large-n-for-overspill-p-aux n x))))

(local
 (defthm large-n-for-overspill-p-aux-makes-overspill-p-true
   (implies (and (natp m)
                 (natp n)
                 (<= m n)
                 (overspill-p m x))
            (and (>= (large-n-for-overspill-p-aux n x)
                     m)
                 (overspill-p (large-n-for-overspill-p-aux n x) x)))
   :rule-classes nil))

(local
 (defthm choose-n-for-not-overspill-p-rewrite
   (implies (and (not (let ((n (choose-n-for-not-overspill-p x)))
                        (and (natp n) (not (overspill-p n x)))))
                 (natp n))
            (overspill-p n x))
   :hints (("Goal" :use choose-n-for-not-overspill-p))))

(local
 (defthm i-large-is-not-standardp
   (implies (natp x)
            (equal (i-large x)
                   (not (standardp x))))
   :hints (("Goal"
            :in-theory (disable standard-constants-are-limited
                                limited-integers-are-standard)
            :use (standard-constants-are-limited
                  limited-integers-are-standard)))))

(local
 (defthm not-standardp-i-large-integer
   (not (standardp (i-large-integer)))
   :hints (("Goal"
            :use
            (i-large-integer-is-large
             (:instance i-large-is-not-standardp
                        (x (i-large-integer))))
            :in-theory (disable i-large-is-not-standardp)))))

(local (in-theory (disable i-large)))

(local
 (defthm one-more-than-large-n-for-overspill-p-aux-makes-overspill-p-false
   (implies (and (posp n)
                 (not (overspill-p n x)))
            (not (overspill-p (1+ (large-n-for-overspill-p-aux n x)) x)))
   :hints (("Goal" :expand ((large-n-for-overspill-p-aux 1 x))))
   :rule-classes nil))

(defund overspill-p-failure-witness (x)
  (cond ((not (overspill-p 0 x))
         0)
        ((not (overspill-p 1 x))
         1)
        (t
         (1+ (large-n-for-overspill-p x)))))

(defthm overspill-p-overspill
  (let ((n (large-n-for-overspill-p x))
        (k (overspill-p-failure-witness x)))
    (or (and (natp k)
             (standardp k)
             (not (overspill-p k x)))
        (and (natp n)
             (overspill-p n x)
             (i-large n))))
  :hints (("Goal"
           :in-theory (enable overspill-p-failure-witness)
           :use ((:instance
                  large-n-for-overspill-p-aux-makes-overspill-p-true (m 1)
                  (n (choose-n-for-not-overspill-p x)))
                 (:instance
                  one-more-than-large-n-for-overspill-p-aux-makes-overspill-p-false
                  (n (choose-n-for-not-overspill-p x))))))
  :rule-classes nil)

; Now, apply the above generic result to prove a better generic result, namely,
; that we overspill to some n such that the property holds not only for n, but
; also for all i < n.

(defun overspill-p* (n x)
  (if (zp n)
      (overspill-p 0 x)
    (and (overspill-p n x)
         (overspill-p* (1- n) x))))

(defchoose choose-n-for-not-overspill-p* (n) (x)
  (and (natp n)
       (not (overspill-p* n x))))

(defun large-n-for-overspill-p*-aux (n x)

; Return the first n' reached below n, as we count down, such that (overspill-p*
; n' x).

  (cond ((zp n) ; impossible
         0)
        ((overspill-p* n x)
         n)
        (t (large-n-for-overspill-p*-aux (1- n) x))))

(defun large-n-for-overspill-p* (x)
  (let ((n (choose-n-for-not-overspill-p* x)))
    (if (not (and (natp n)
                  (not (overspill-p* n x))))
        (i-large-integer)
      (large-n-for-overspill-p*-aux n x))))

(local
 (defthm choose-n-for-not-overspill-p*-rewrite
   (implies (and (not (let ((n (choose-n-for-not-overspill-p* x)))
                        (and (natp n) (not (overspill-p* n x)))))
                 (natp n))
            (overspill-p* n x))
   :hints (("Goal" :use choose-n-for-not-overspill-p*))))

(defund overspill-p*-failure-witness (x)
  (cond ((not (overspill-p* 0 x))
         0)
        ((not (overspill-p* 1 x))
         1)
        (t
         (1+ (large-n-for-overspill-p* x)))))

(defthm overspill-p*-overspill
  (let ((n (large-n-for-overspill-p* x))
        (k (overspill-p*-failure-witness x)))
    (or (and (natp k)
             (standardp k)
             (not (overspill-p* k x)))
        (and (natp n)
             (i-large n)
             (overspill-p* n x))))
  :hints (("Goal"
           :in-theory (enable overspill-p*-failure-witness)
           :by (:functional-instance
                overspill-p-overspill
                (overspill-p overspill-p*)
                (choose-n-for-not-overspill-p choose-n-for-not-overspill-p*)
                (large-n-for-overspill-p-aux large-n-for-overspill-p*-aux)
                (large-n-for-overspill-p large-n-for-overspill-p*)
                (overspill-p-failure-witness overspill-p*-failure-witness))))
  :rule-classes nil)

(local
 (defthm overspill-p*-implies-overspill-p-smaller
   (implies (and (overspill-p* n x)
                 (natp n)
                 (natp m)
                 (<= m n))
            (overspill-p m x))))

(defun least-overspill-p-failure (k x)
  (cond ((zp k) 0)
        ((not (overspill-p k x)) k)
        (t (least-overspill-p-failure (1- k) x))))

(local
 (defthm not-overspill-p-for-least-overspill-p-failure
   (implies (and (natp k)
                 (not (overspill-p* k x)))
            (not (overspill-p (least-overspill-p-failure k x) x)))))

(local
 (defthm least-overspill-p-failure-<
   (implies (natp k)
            (<= (least-overspill-p-failure k x)
                k))
   :rule-classes :linear))

(local
 (defun add1-induction (n)
   (if (zp n)
       n
     (add1-induction (1- n)))))

(local
 (defthm standard-p-preserved-below-natp
   (implies (and (standardp n)
                 (natp m)
                 (natp n)
                 (<= m n))
            (standardp m))
   :hints (("Goal" :induct (add1-induction n)))))

(defthm overspill-p-overspill-strong
  (let ((n (large-n-for-overspill-p* x))
        (k (least-overspill-p-failure (overspill-p*-failure-witness x)
                                      x)))
    (or (and (natp k)
             (standardp k)
             (not (overspill-p k x)))
        (and (natp n)
             (i-large n)
             (implies (and (natp m)
                           (<= m n))
                      (overspill-p m x)))))
  :hints (("Goal" :use overspill-p*-overspill
           :in-theory (disable large-n-for-overspill-p*)))
  :rule-classes nil)
