; A lightweight book about the built-in function subsetp-equal.
;
; Copyright (C) 2016-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "member-equal"))

(in-theory (disable subsetp-equal))

;; Kept disabled, but see -cheap version below.
(defthmd subsetp-equal-when-not-consp-arg1
  (implies (not (consp x))
           (subsetp-equal x y))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

;; Kept disabled, but see -cheap version below.
(defthmd subsetp-equal-when-not-consp-arg2
  (implies (not (consp y))
           (equal (subsetp-equal x y)
                  (not (consp x))))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-when-not-consp-arg1-cheap
  (implies (not (consp x))
           (subsetp-equal x y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-when-not-consp-arg2-cheap
  (implies (not (consp y))
           (equal (subsetp-equal x y)
                  (not (consp x))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

;; A simple/abbreviation rule.
(defthm subsetp-equal-of-nil-arg1
  (subsetp-equal nil x)
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-of-nil-arg2
  (equal (subsetp-equal x nil)
         (not (consp x)))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

;; Disabled because it might be slow, so we include a cheap version below.
(defthmd subsetp-equal-when-subsetp-equal-of-cdr
  (implies (subsetp-equal x (cdr y))
           (subsetp-equal x y))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-when-subsetp-equal-of-cdr-cheap
  (implies (subsetp-equal x (cdr y))
           (subsetp-equal x y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-self
  (subsetp-equal x x)
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-of-append
  (equal (subsetp-equal (append x y) z)
         (and (subsetp-equal x z)
              (subsetp-equal y z)))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-of-cons-arg1
  (equal (subsetp-equal (cons a x) y)
         (and (member-equal a y)
              (subsetp-equal x y)))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-of-cons-arg2
  (implies (and (syntaxp (not (and (quotep a)
                                   (quotep y))))
                (subsetp-equal x y))
           (subsetp-equal x (cons a y)))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

;; Disabled since it can be expensive
(defthmd subsetp-equal-of-cons-arg2-irrel
  (implies (not (member-equal a x))
           (equal (subsetp-equal x (cons a y))
                  (subsetp-equal x y)))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-of-cons-arg2-same
  (subsetp-equal x (cons a x))
  :hints (("Goal" :in-theory (enable subsetp-equal
                                     subsetp-equal-of-cons-arg2-irrel
                                     subsetp-equal-when-subsetp-equal-of-cdr))))

(defthm subsetp-equal-of-add-to-set-equal-arg1
  (equal (subsetp-equal (add-to-set-equal a x) y)
         (and (member-equal a y)
              (subsetp-equal x y)))
  :hints (("Goal" :in-theory (enable subsetp-equal add-to-set-equal))))

(defthm subsetp-equal-of-add-to-set-equal-arg2
  (implies (subsetp-equal x y)
           (subsetp-equal x (add-to-set-equal a y)))
  :hints (("Goal" :in-theory (enable subsetp-equal add-to-set-equal))))

(defthm subsetp-equal-of-add-to-set-equal-arg2-same
  (subsetp-equal x (add-to-set-equal a x))
  :hints (("Goal" :in-theory (enable subsetp-equal add-to-set-equal))))

;; Disabled but see subsetp-equal-of-add-to-set-equal-arg2-irrel-cheap.
(defthmd subsetp-equal-of-add-to-set-equal-arg2-irrel
  (implies (not (member-equal a x))
           (equal (subsetp-equal x (add-to-set-equal a y))
                  (subsetp-equal x y)))
  :hints (("Goal" :in-theory (enable member-equal add-to-set-equal))))

(defthm subsetp-equal-of-add-to-set-equal-arg2-irrel-cheap
  (implies (not (member-equal a x))
           (equal (subsetp-equal x (add-to-set-equal a y))
                  (subsetp-equal x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable member-equal add-to-set-equal))))

(defthm subsetp-equal-of-union-equal-arg1
  (equal (subsetp-equal (union-equal x y) z)
         (and (subsetp-equal x z)
              (subsetp-equal y z)))
  :hints (("Goal" :in-theory (enable union-equal subsetp-equal))))

(defthm subsetp-equal-of-union-equal-arg2
  (implies (or (subsetp-equal x y)
               (subsetp-equal x z))
           (subsetp-equal x (union-equal y z)))
  :hints (("Goal" :in-theory (enable subsetp-equal union-equal))))

(defthm subsetp-equal-of-union-equal-arg2-same
  (subsetp-equal x (union-equal x y)))

(defthm subsetp-equal-of-union-equal-arg2-same-alt
  (subsetp-equal x (union-equal y x)))

(defthm subsetp-equal-of-remove-equal-arg1
  (implies (subsetp-equal x y)
           (subsetp-equal (remove-equal a x) y))
  :hints (("Goal" :in-theory (enable subsetp-equal remove-equal))))

(defthm subsetp-equal-of-remove-equal-arg1-same
  (subsetp-equal (remove-equal a x) x)
  :hints (("Goal" :in-theory (enable subsetp-equal remove-equal))))

(defthmd subsetp-equal-of-remove-equal-arg1-irrel
  (implies (member-equal a y)
           (equal (subsetp-equal (remove-equal a x) y)
                  (subsetp-equal x y)))
  :hints (("Goal" :in-theory (enable subsetp-equal remove-equal))))

(defthm subsetp-equal-of-remove-equal-arg1-irrel-cheap
  (implies (member-equal a y)
           (equal (subsetp-equal (remove-equal a x) y)
                  (subsetp-equal x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable subsetp-equal remove-equal))))

(defthmd subsetp-equal-of-remove-equal-arg2-irrel
  (implies (not (member-equal a x))
	   (equal (subsetp-equal x (remove-equal a y))
                  (subsetp-equal x y)))
  :hints (("Goal" :in-theory (enable subsetp-equal remove-equal))))

(defthm subsetp-equal-of-remove-equal-arg2-irrel-cheap
  (implies (not (member-equal a x))
	   (equal (subsetp-equal x (remove-equal a y))
                  (subsetp-equal x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :use (:instance subsetp-equal-of-remove-equal-arg2-irrel))))

(defthm subsetp-equal-of-remove1-equal-arg1
  (implies (subsetp-equal x y)
           (subsetp-equal (remove1-equal a x) y))
  :hints (("Goal" :in-theory (enable subsetp-equal remove1-equal))))

(defthm subsetp-equal-of-remove1-equal-arg1-same
  (subsetp-equal (remove1-equal a x) x)
  :hints (("Goal" :in-theory (enable subsetp-equal remove1-equal))))

(defthmd subsetp-equal-of-remove1-equal-arg1-irrel
  (implies (member-equal a y)
           (equal (subsetp-equal (remove1-equal a x) y)
                  (subsetp-equal x y)))
  :hints (("Goal" :in-theory (enable subsetp-equal remove-equal))))

(defthmd subsetp-equal-of-remove1-equal-arg2-irrel
  (implies (not (member-equal a x))
           (equal (subsetp-equal x (remove1-equal a y))
                  (subsetp-equal x y)))
  :hints (("Goal" :in-theory (enable subsetp-equal remove-equal))))

(defthm subsetp-equal-of-remove1-equal-arg1-irrel-cheap
  (implies (member-equal a y)
           (equal (subsetp-equal (remove1-equal a x) y)
                  (subsetp-equal x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable subsetp-equal remove-equal))))

;todo: this must be proved somewhere else
;The -alt avoids a name clash
(defthm subsetp-equal-transitive-alt
  (implies (and (subsetp-equal x y) ;y is a free var
                (subsetp-equal y z))
           (subsetp-equal x z))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

;The -alt avoids a name clash
(defthm subsetp-equal-transitive-2-alt
  (implies (and (subsetp-equal y z) ;y is a free var
                (subsetp-equal x y))
           (subsetp-equal x z))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-of-cdr-arg1
  (implies (subsetp-equal x y)
           (subsetp-equal (cdr x) y))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-of-cdr-arg2-cheap
  (implies (subsetp-equal x (cdr y))
           (subsetp-equal x y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

;; Would loop if enabled.
(defthmd subsetp-equal-of-cdr-arg2
  (implies (subsetp-equal x (cdr y))
           (subsetp-equal x y)))

(defthm subsetp-equal-of-true-list-fix-arg1
  (equal (subsetp-equal (true-list-fix x) y)
         (subsetp-equal x y))
  :hints (("Goal" :in-theory (enable subsetp-equal true-list-fix))))

(defthm subsetp-equal-of-true-list-fix-arg2
  (equal (subsetp-equal x (true-list-fix y))
         (subsetp-equal x y))
  :hints (("Goal" :in-theory (enable subsetp-equal true-list-fix))))

(defthm subsetp-equal-of-append-2-1
  (implies (subsetp-equal x z)
           (subsetp-equal x (append y z)))
  :hints (("Goal" :in-theory (enable append))))

(defthm subsetp-equal-of-append-2-2
  (implies (subsetp-equal x y)
           (subsetp-equal x (append y z)))
  :hints (("Goal" :in-theory (enable append subsetp-equal))))

(defthm subsetp-equal-of-take-same
  (implies (and (natp n)
                (< n (len x)))
           (subsetp-equal (take n x) x)))

(defthm subsetp-equal-of-take
  (implies (and (subsetp-equal x y)
                (natp n)
                (< n (len x)))
           (subsetp-equal (take n x) y)))

(defthm subsetp-equal-of-nthcdr-same
  (subsetp-equal (nthcdr n x) x))

(defthm subsetp-equal-of-nthcdr
  (implies (subsetp-equal x y)
           (subsetp-equal (nthcdr n x) y))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm subsetp-equal-of-set-difference-equal-arg1-same
  (subsetp-equal (set-difference-equal x y) x))

(defthm subsetp-equal-of-set-difference-equal-arg1
  (implies (subsetp-equal x z)
	   (subsetp-equal (set-difference-equal x y) z)))

(defthm subsetp-equal-of-intersection-equal-arg1
  (implies (or (subsetp-equal x z)
               (subsetp-equal y z))
           (subsetp-equal (intersection-equal x y) z))
  :hints (("Goal" :in-theory (enable subsetp-equal intersection-equal))))

(defthm subsetp-equal-of-intersection-equal-arg1-same-1
  (subsetp-equal (intersection-equal x y) x))

(defthm subsetp-equal-of-intersection-equal-arg1-same-2
  (subsetp-equal (intersection-equal x y) y))

(defthm subsetp-equal-of-cons-and-cons-same
  (implies (subsetp-equal x y)
           (subsetp-equal (cons a x) (cons a y))))

(defthm subsetp-equal-of-cons-and-cons
  (equal (subsetp-equal (cons a x) (cons a y))
         (subsetp-equal (remove-equal a x) (remove-equal a y))))

(defthm subsetp-equal-of-remove-equal-and-remove-equal
  (implies (subsetp-equal x y)
           (subsetp-equal (remove-equal a x)
                          (remove-equal a y)))
  :hints (("Goal" :in-theory (enable subsetp-equal remove-equal))))

(defthm member-equal-when-subsetp-equal-1
  (implies (and (subsetp-equal lst2 lst) ;lst2 is a free var
                (member-equal x lst2))
           (member-equal x lst))
  :hints (("Goal" :in-theory (enable subsetp-equal member-equal))))

(defthm member-equal-when-subsetp-equal-2
  (implies (and (member-equal x lst2) ;lst2 is a free var
                (subsetp-equal lst2 lst))
           (member-equal x lst))
  :hints (("Goal" :in-theory (enable subsetp-equal member-equal))))
