; A utility to check whether all values in a list are less than a given value
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/sequences/defforall" :dir :system)

;; Checks whether each element of X is less than N.
(defforall all-< (x n) (< x n) :fixed (n) :declares ((xargs :guard (and (rational-listp x) (rationalp n)))))

(defthm all-<-of-nil
  (all-< nil x)
  :hints (("Goal" :in-theory (enable all-<))))

(defthm all-<-of-reverse-list
  (equal (all-< (reverse-list x) n)
         (all-< x n))
  :hints (("Goal" :in-theory (enable reverse-list all-<))))

;; todo: strengthen the one that defforall generates
(defthm all-<-of-revappend-2
  (equal (all-< (revappend x y) n)
         (and (all-< x n)
              (all-< y n)))
  :hints (("Goal" :induct (REVAPPEND X Y)
           :in-theory (enable revappend all-<))))

(defthm <-of-nth-of-0-when-all-<-cheap
  (implies (and (all-< items x)
                (consp items))
           (< (nth 0 items) x))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (enable all-<))))

(defthm all-<-of-set-difference-equal
  (implies (all-< x bound)
           (all-< (set-difference-equal x y) bound))
  :hints (("Goal" :in-theory (enable set-difference-equal))))

(defthm not-all-<-when-member-equal
  (implies (and (member-equal a x)
                (>= a n))
           (not (all-< x n)))
  :hints (("Goal" :in-theory (enable all-<))))

(defthm not-all-<-when-memberp
  (implies (and (memberp a x)
                (>= a n))
           (not (all-< x n)))
  :hints (("Goal" :in-theory (enable all-< memberp))))

(defthm all-<-transitive
  (implies (and (all-< lst freevar)
                (<= freevar x))
           (all-< lst x))
  :hints (("Goal" :in-theory (enable all-<))))

;slow?
(defthmd not-<-of-car-when-all-<
  (implies (and (all-< items bound)
                (consp items))
           (not (< bound (car items)))))

(defthm all-<-transitive-free
  (implies (and (all-< items free)
                (<= free x)
                (rationalp x)
                (rationalp free)
                )
           (all-< items x))
  :hints (("Goal" :in-theory (enable all-<))))

(defthm all-<-transitive-free-2
  (implies (and (<= free x)
                (all-< items free)
                (rationalp x)
                (rationalp free)
                )
           (all-< items x))
  :hints (("Goal" :in-theory (enable all-<))))

(defthm not-<-of-nth-when-all-<
  (implies (and (all-< x bound)
                (natp n)
                (< n (len x)))
           (not (< bound (nth n x))))
  :hints (("Goal" :in-theory (enable all-< nth))))

(defthmd <-of-nth-when-all-<
  (implies (and (all-< l bound)
                (natp n)
                (< n (len l)))
           (< (nth n l) bound))
  :hints (("Goal" :in-theory (e/d (all-< nth) ()))))
