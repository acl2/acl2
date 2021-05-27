; A lightweight book about the built-in function member-equal.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable member-equal))

(defthm member-equal-of-append-iff
  (iff (member-equal a (append x y))
       (or (member-equal a x)
           (member-equal a y)))
  :hints (("Goal" :in-theory (enable member-equal))))

(defthm member-equal-of-car-same
  (equal (member-equal (car x) x)
         (if (consp x)
             x
           nil))
  :hints (("Goal" :in-theory (enable member-equal))))

(defthm member-equal-when-not-consp-cheap
  (implies (not (consp x))
           (not (member-equal a x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable member-equal))))

(defthmd member-equal-when-not-member-equal-of-cdr
  (implies (not (member-equal a (cdr x)))
           (iff (member-equal a x)
                (if (consp x)
                    (equal a (car x))
                  nil)))
  :hints (("Goal" :in-theory (enable member-equal))))

(defthm not-member-equal-when-not-member-equal-of-cdr-cheap
  (implies (not (member-equal a (cdr x)))
           (iff (member-equal a x)
                (if (consp x)
                    (equal a (car x))
                  nil)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable member-equal))))

(defthm member-equal-when-member-equal-of-cdr-cheap
  (implies (member-equal a (cdr x))
           (member-equal a x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable member-equal))))

;; Disabled since ACL2 will match (cons b x) with a constant, possibly leading
;; to large case splits when rewriting (member-equal x <large-constant-list>).
(defthmd member-equal-of-cons
  (equal (member-equal a (cons b x))
         (if (equal a b)
             (cons b x)
           (member-equal a x)  ))
  :hints (("Goal" :in-theory (enable member-equal))))

(defthm member-equal-of-cons-non-constant
  (implies (syntaxp (not (and (quotep b)
                              (quotep x))))
           (equal (member-equal a (cons b x))
                  (if (equal a b)
                      (cons b x)
                    (member-equal a x)  )))
  :hints (("Goal" :in-theory (enable member-equal))))

(defthmd member-equal-of-true-list-fix
  (equal (member-equal a (true-list-fix x))
         (true-list-fix (member-equal a (true-list-fix x))))
  :hints (("Goal" :in-theory (enable member-equal))))

(defthm member-equal-of-true-list-fix-iff
  (iff (member-equal x (true-list-fix y))
       (member-equal x y))
  :hints (("Goal" :in-theory (enable member-equal true-list-fix))))

(defthm member-equal-when-member-equal-of-member-equal
  (implies (member-equal item1 (member-equal item2 lst))
           (member-equal item1 lst))
  :hints (("Goal" :in-theory (enable member-equal))))

(defthm member-equal-of-union-equal
  (iff (member-equal a (union-equal x y))
       (or (member-equal a x)
           (member-equal a y)))
  :hints (("Goal" :in-theory (enable union-equal no-duplicatesp-equal))))

(defthm member-equal-of-set-difference-equal
  (iff (member-equal a (set-difference-equal x y))
       (and (member-equal a x)
            (not (member-equal a y))))
  :hints (("Goal" :in-theory (enable set-difference-equal no-duplicatesp-equal))))

(defthm member-equal-of-remove-equal
  (iff (member-equal a (remove-equal b x))
       (if (equal a b)
           nil
         (member-equal a x)))
  :hints (("Goal" :in-theory (enable member-equal remove-equal))))

(defthm member-equal-of-remove-equal-irrel
  (implies (not (equal a b))
           (iff (member-equal a (remove-equal b x))
                (member-equal a x)))
  :hints (("Goal" :in-theory (enable member-equal remove-equal))))

(defthm member-equal-of-remove1-equal-irrel
  (implies (not (equal a b))
           (iff (member-equal a (remove1-equal b x))
                (member-equal a x)))
  :hints (("Goal" :in-theory (enable member-equal))))

;; Disabled since consp is so common.
(defthmd consp-when-member-equal
  (implies (member-equal a x) ;note that a is a free var
	   (consp x)))

(defthm true-listp-of-member-equal
  (implies (true-listp x)
           (true-listp (member-equal a x))))

(defthm not-member-equal-of-member-equal-when-not-member-equal
  (implies (not (member-equal a1 x))
           (not (member-equal a1 (member-equal a2 x)))))

(defthm not-member-equal-of-cdr-when-not-member-equal
  (implies (not (member-equal a x))
           (not (member-equal a (cdr x)))))

(defthm consp-of-member-equal-iff
  (iff (consp (member-equal a x))
       (member-equal a x))
  :hints (("Goal" :in-theory (enable member-equal))))

(defthm member-equal-of-constant-when-not-equal-car
  (implies (and (syntaxp (and (quotep x)
                              (consp (unquote x))))
                (not (equal a (car x))))
           (equal (member-equal a x)
                  (member-equal a (cdr x))))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0)))
  :hints (("Goal" :in-theory (enable member-equal))))

(defthm member-equal-when-singleton
  (equal (member-equal x (list y))
         (if (equal x y)
             (list x)
           nil)))

;; Should avoid case splitsa
(defthm member-equal-when-singleton-iff
  (iff (member-equal x (list y))
       (equal x y)))

;use polarities?
(defthm member-equal-of-constant-trim
  (implies (and (syntaxp (quotep k))
                (not (equal x val)) ;val is a free var
                (syntaxp (quotep val))
                (member-equal val k))
           (iff (member-equal x k)
                (member-equal x (remove-equal val k))))
  :hints (("Goal" :in-theory (enable member-equal))))

(defthm member-equal-of-nth-same
  (implies (< (nfix n) (len x))
           (member-equal (nth n x) x)))
