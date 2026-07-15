; A utility to check whether all values in a list are less than a given value
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Somewhat similar to bounded-integer-listp, which is built-in.

(include-book "kestrel/lists-light/reverse-list-def" :dir :system)
(local (include-book "kestrel/sequences/defforall" :dir :system))

;; Checks whether each element of X is less than N.
(defforall all-< (x bound) (< x bound) :fixed (bound) :declares ((xargs :guard (and (rational-listp x) (rationalp bound)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Establishing all-<

(defthm all-<-of-nil
  (all-< nil bound)
  :hints (("Goal" :in-theory (enable all-<))))

(defthm all-<-of-reverse-list
  (equal (all-< (reverse-list x) bound)
         (all-< x bound))
  :hints (("Goal" :in-theory (enable reverse-list all-<))))

;; todo: strengthen the one that defforall generates
(defthm all-<-of-revappend-2
  (equal (all-< (revappend x y) bound)
         (and (all-< x bound)
              (all-< y bound)))
  :hints (("Goal" :induct (revappend x y)
           :in-theory (enable revappend all-<))))

(defthm all-<-of-reverse
  (equal (all-< (reverse x) bound)
         (all-< x bound))
  :hints (("Goal" :cases ((stringp x)))))

(defthm all-<-of-set-difference-equal
  (implies (all-< x bound)
           (all-< (set-difference-equal x y) bound))
  :hints (("Goal" :in-theory (enable set-difference-equal))))


; rename "-monotone"?
(defthm all-<-transitive
  (implies (and (all-< lst bound2)
                (<= bound2 bound))
           (all-< lst bound))
  :hints (("Goal" :in-theory (enable all-<))))


;rename monotone?
(defthm all-<-transitive-free
  (implies (and (all-< l free)
                (<= free bound)
                (rationalp bound)
                (rationalp free))
           (all-< l bound))
  :hints (("Goal" :in-theory (enable all-<))))

;rename monotone?
(defthm all-<-transitive-free-2
  (implies (and (<= free bound)
                (all-< l free)
                (rationalp x)
                (rationalp free))
           (all-< l bound))
  :hints (("Goal" :in-theory (enable all-<))))

;; improve?
(defthmd all-<-when-all-<-of-take-and-all-<-of-nthcdr
  (implies (and (all-< (take n x) bound)
                (all-< (nthcdr n x) bound))
           (all-< x bound)))

(defthm all-<-of-take-when-all-<-of-take
  (implies (and (all-< (take num2 l) bound) ; num2 is a free var
                (<= num num2)
                ;; (integerp num)
                (integerp num2))
           (all-< (take num l) bound)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Using all-<

;drop?
(defthm <-of-nth-of-0-when-all-<-cheap
  (implies (and (all-< l bound)
                (consp l))
           (< (nth 0 l) bound))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (enable all-<))))

; make a cheap version?
(defthmd <-of-nth-when-all-<
  (implies (and (all-< l bound)
                (natp n)
                (< n (len l)))
           (< (nth n l) bound))
  :hints (("Goal" :in-theory (enable all-< nth))))

(defthmd <-of-car-when-all-<
  (implies (and (all-< l bound)
                (consp l))
           (< (car l) bound))
  :hints (("Goal" :in-theory (enable all-<))))

(defthm <-of-car-when-all-<-cheap
  (implies (and (all-< l bound)
                (consp l))
           (< (car l) bound))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (enable all-<))))

;slow?
(defthmd not-<-of-car-when-all-<
  (implies (and (all-< l bound)
                (consp l))
           (not (< bound (car l)))))

(defthm not-<-of-nth-when-all-<
  (implies (and (all-< x bound)
                (natp n)
                (< n (len x)))
           (not (< bound (nth n x))))
  :hints (("Goal" :in-theory (enable all-< nth))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Falsifying all-<

(defthm not-all-<-when-member-equal
  (implies (and (member-equal a x)
                (>= a bound))
           (not (all-< x bound)))
  :hints (("Goal" :in-theory (enable all-<))))

(defthm not-all-<-when-memberp
  (implies (and (memberp a x)
                (>= a bound))
           (not (all-< x bound)))
  :hints (("Goal" :in-theory (enable all-< memberp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
