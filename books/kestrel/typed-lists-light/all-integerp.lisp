; A recognizer for lists of integers.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; ALL-INTEGERP is like the built-in INTEGER-LISTP but does not require the
;; list to be a true list.  Thus, it may allow for better congruence rules.

;; Note that any atom satisfies this!
(defund all-integerp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (integerp (car x))
           (all-integerp (cdr x)))
      t))

(defthm all-integerp-of-cdr
  (implies (all-integerp x)
           (all-integerp (cdr x)))
  :hints (("Goal" :in-theory (enable all-integerp))))

;; Disabled since it may be expensive
(defthmd integerp-of-car-when-all-integerp
  (implies (all-integerp x)
           (equal (integerp (car x))
                  (consp x)))
  :hints (("Goal" :in-theory (enable all-integerp))))

(defthm integerp-of-car-when-all-integerp-cheap
  (implies (all-integerp x)
           (equal (integerp (car x))
                  (consp x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable all-integerp))))

(defthm all-integerp-of-cons
  (equal (all-integerp (cons x y))
         (and (integerp x)
              (all-integerp y)))
  :hints (("Goal" :in-theory (enable all-integerp ))))

(defthm all-integerp-of-append
  (equal (all-integerp (append x y))
         (and (all-integerp x)
              (all-integerp y)))
  :hints (("Goal" :in-theory (enable all-integerp append))))

(defthm all-integerp-of-nthcdr
  (implies (all-integerp x)
           (all-integerp (nthcdr n x)))
  :hints (("Goal" :in-theory (enable all-integerp nthcdr))))

;okay to backchain?
(defthm integerp-of-nth-when-all-integerp
  (implies (and (all-integerp x)
                (natp n)
                (< n (len x)))
           (integerp (nth n x)))
  :hints (("Goal" :in-theory (enable all-integerp nth))))

(defthm all-integerp-of-update-nth
  (implies (and (integerp val)
                (<= index (len lst))
                (all-integerp lst))
           (all-integerp (update-nth index val lst)))
  :hints (("Goal" :in-theory (enable update-nth all-integerp)
           :induct (update-nth index val lst))))

;auto-generate?
(defthm all-integerp-of-true-list-fix
  (equal (all-integerp (true-list-fix lst))
         (all-integerp lst))
  :hints (("Goal" :in-theory (enable all-integerp true-list-fix))))

(defthmd all-integerp-when-not-consp
  (implies (not (consp x))
           (all-integerp x))
  :hints (("Goal" :in-theory (enable all-integerp))))

(defthm all-integerp-when-not-consp-cheap
  (implies (not (consp x))
           (all-integerp x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable all-integerp))))

(defthm all-integerp-of-take
  (implies (all-integerp lst)
           (equal (all-integerp (take n lst))
                  (<= (nfix n) (len lst))))
  :hints (("Goal" :in-theory (enable all-integerp take))))
