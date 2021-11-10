; Theorems about memberp.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; A lightweight book about the function memberp, which is like member-equal
;; but always returns a boolean.

(include-book "memberp-def")
(local (include-book "len"))
(local (include-book "nth"))

;; This enforces memberp as the normal form.
;; TODO: Consider disabling.
(defthm member-equal-becomes-memberp
  (iff (member-equal a x)
       (memberp a x))
  :hints (("Goal" :in-theory (enable memberp member-equal))))

;; The syntaxp hyp avoids splitting "memberp of <constant>" into many cases.
(defthm memberp-of-cons
  (implies (syntaxp (not (and (quotep b)
                              (quotep x))))
           (equal (memberp a (cons b x))
                  (or (equal a b)
                      (memberp a x))))
  :hints (("Goal" :in-theory (enable memberp))))

;; Kept disabled to avoid splitting
(defthmd memberp-of-cons-when-constant
  (implies (syntaxp (and (quotep b)
                         (quotep x)))
           (equal (memberp a (cons b x))
                  (or (equal a b)
                      (memberp a x))))
  :hints (("Goal" :in-theory (enable memberp))))

(defthm memberp-of-append
  (equal (memberp a (append x y))
         (or (memberp a x)
             (memberp a y)))
  :hints (("Goal" :in-theory (enable memberp))))

(defthm memberp-of-car-same
  (equal (memberp (car x) x)
         (consp x))
  :hints (("Goal" :in-theory (enable memberp))))

;; a simple/abbreviation rule
(defthm memberp-of-nil
  (not (memberp a nil))
  :hints (("Goal" :in-theory (enable memberp))))

(defthm memberp-when-not-consp-cheap
  (implies (not (consp x))
           (not (memberp a x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable memberp))))

(defthm memberp-when-not-memberp-of-cdr-cheap
  (implies (not (memberp a (cdr x)))
           (equal (memberp a x)
                  (if (consp x)
                      (equal a (car x))
                    nil)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable memberp))))

(defthm memberp-when-memberp-of-cdr-cheap
  (implies (memberp a (cdr x))
           (memberp a x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable memberp))))

(defthm memberp-when-subsetp-equal-1
  (implies (and (subsetp-equal y x) ;y is a free var
                (memberp a y))
           (memberp a x)))

(defthm memberp-when-subsetp-equal-2
  (implies (and (memberp a y) ;y is a free var
                (subsetp-equal y x))
           (memberp a x)))

(local
 (defthm memberp-of-nth-same-helper
   (implies (< (nfix n) (len x))
            (memberp (nth n x) x))
   :hints (("Goal" :in-theory (e/d (len nth)
                                   (nth-of-cdr
                                    len-of-cdr))))))

(defthm memberp-of-nth-same
  (equal (memberp (nth n x) x)
         (if (< (nfix n) (len x))
             t
           (memberp nil x))))

;the -2 avoids a name clash
(defthm memberp-of-update-nth-same-2
  (memberp val (update-nth n val lst))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm memberp-of-update-nth-when-not-memberp
  (implies (and (not (memberp val1 lst))
                (natp n)
                (<= n (len lst)) ; update-nth might lengthen the list by 1
                )
           (equal (memberp val1 (update-nth n val2 lst))
                  (equal val1 val2)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm memberp-of-nth-and-nthcdr
  (implies (and (<= start n)
                (< n (len lst))
                (natp n)
                (natp start))
           (memberp (nth n lst) (nthcdr start lst)))
  :hints (("Goal" :in-theory (e/d (nthcdr nth) (nth-of-cdr)))))

(defthm not-subsetp-equal-when-memberp
  (implies (and (memberp a x) ;a is a free var
                (not (memberp a y)))
           (not (subsetp-equal x y))))

(defthm memberp-of-true-list-fix
  (equal (memberp a (true-list-fix x))
         (memberp a x)))

(defthm not-memberp-of-nthcdr
  (implies (not (memberp a x))
           (not (memberp a (nthcdr n x))))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm memberp-of-car-of-last
  (equal (memberp (car (last x)) x)
         (consp x)))

(defthm memberp-when-singleton-cheap
  (implies (equal 1 (len x))
           (equal (memberp a x)
                  (equal a (car x))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable memberp))))

(local
 (defthm memberp-of-revappend-forward
   (implies (memberp a (revappend x y))
            (or (memberp a x)
                (memberp a y)))
   :hints (("Goal" :in-theory (enable memberp revappend)))))

(local
 (defthm memberp-of-revappend-backward
   (implies (or (memberp a x)
                (memberp a y))
            (memberp a (revappend x y)))
   :hints (("Goal" :in-theory (enable memberp revappend)))))

(defthm memberp-of-revappend
  (equal (memberp a (revappend x y))
         (or (memberp a x)
             (memberp a y))))

(defthmd not-memberp-when-memberp-and-not-intersection-equal
  (implies (and (memberp a y) ;y is a free var
                (not (intersection-equal x y)))
           (not (memberp a x))))

(defthm not-memberp-when-memberp-and-not-intersection-equal-cheap
  (implies (and (syntaxp (quotep x))
                (memberp a y)
                (syntaxp (quotep y))
                (not (intersection-equal x y)))
           (not (memberp a x))))

(defthm memberp-when-not-equal-of-car-cheap
  (implies (and (syntaxp (quotep x))
                (not (equal a (car x)))
                (consp x) ;prevent loops
                )
           (equal (memberp a x)
                  (memberp a (cdr x))))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0 nil))))

(defthm memberp-of-set-difference-equal
  (equal (memberp a (set-difference-equal x y))
         (and (memberp a x)
              (not (memberp a y))))
  :hints (("Goal" :in-theory (enable memberp-of-cons))))

(defthm memberp-of-intersection-equal
  (equal (memberp a (intersection-equal x y))
         (and (memberp a x)
              (memberp a y)))
  :hints (("Goal" :in-theory (enable memberp intersection-equal))))

(defthm intersection-equal-when-memberp-and-memberp-same-iff
  (implies (and (memberp a y) ;a is a free var
                (memberp a x))
           (intersection-equal x y))
  :hints (("Goal" :in-theory (enable intersection-equal))))

(defthm memberp-of-union-equal
  (equal (memberp a (union-equal x y))
         (or (memberp a x)
             (memberp a y)))
  :hints (("Goal" :in-theory (enable union-equal
                                     ;subsetp-equal
                                     add-to-set-equal))))

(defthm not-memberp-when-memberp-of-take
  (implies (and (memberp a (take n x)) ;n is a free var
                (<= (nfix n) (len x)))
           (memberp a x)))

;; Disabled since it is hung on equal.
(defthmd not-equal-when-memberp-cheap
  (implies (and (syntaxp (quotep k))
                (memberp x free)
                (syntaxp (quotep free))
                (not (memberp k free)))
           (not (equal k x))))

(defthm memberp-of-constant-when-not-member-of-constant
  (implies (and (syntaxp (quotep k1))
                (not (memberp a k2))
                (syntaxp (quotep k1))
                (intersection-equal k1 k2) ;gets computed
                )
           (equal (memberp a k1)
                  (memberp a (set-difference-equal k1 k2)))))

;; This version has memberp in the hyp.
(defthm subsetp-equal-of-add-to-set-equal-arg2-irrel-cheap-alt
  (implies (not (memberp a x))
           (equal (subsetp-equal x (add-to-set-equal a y))
                  (subsetp-equal x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable memberp add-to-set-equal))))

;; This version has memberp in the hyp.
(defthm subsetp-equal-of-remove-equal-arg1-irrel-cheap-alt
  (implies (memberp a y)
           (equal (subsetp-equal (remove-equal a x) y)
                  (subsetp-equal x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable subsetp-equal remove-equal))))

(defthm not-memberp-of-remove-equal-same
  (not (memberp a (remove-equal a x)))
  :hints (("Goal" :in-theory (enable memberp remove-equal))))

(defthm memberp-of-remove-equal-diff
  (implies (not (equal a b))
           (equal (memberp a (remove-equal b x))
                  (memberp a x)))
  :hints (("Goal" :in-theory (enable memberp remove-equal))))

;todo: move
(defthm member-equal-of-remove-equal-diff
  (implies (not (equal a b))
           (iff (member-equal a (remove-equal b x))
                (member-equal a x)))
  :hints (("Goal" :in-theory (enable member-equal remove-equal))))

;todo: move?
(defthm subsetp-equal-of-remove-equal-irrel
  (implies (not (memberp a x))
           (equal (subsetp-equal x (remove-equal a y))
                  (subsetp-equal x y)))
  :hints (("Goal" :in-theory (enable memberp remove-equal subsetp-equal))))

(defthm memberp-of-remove1-equal-irrel
  (implies (not (equal a b))
           (equal (memberp a (remove1-equal b x))
                  (memberp a x)))
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm memberp-of-car-and-take
  (equal (memberp (car lst) (take n lst))
         (and (integerp n)
              (< 0 n)))
  :hints (("Goal" :in-theory (enable take))))

(defthm memberp-of-nth-and-take
  (implies (and (< (nfix m) (nfix n))
                (< (nfix n) (len l)))
           (memberp (nth m l) (take n l)))
  :hints (("Goal" :in-theory (e/d (take nth) (nth-of-cdr)))))

(defthm not-memberp-of-take
  (implies (and (not (memberp a l))
                (<= n (len l)))
           (not (memberp a (take n l))))
  :hints (("Goal" :in-theory (enable take))))

(defthm memberp-when-not-cons-of-cdr-cheap
  (implies (not (consp (cdr l)))
           (equal (memberp x l)
                  (and (consp l)
                       (equal x (car l)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable memberp))))

(defthm memberp-of-add-to-set-equal
  (equal (memberp a (add-to-set-equal x l))
         (or (equal a x)
             (memberp a l))))

(defthm memberp-nth-of-self-helper
  (implies (< n (len lst))
           (equal (memberp (nth n lst) lst)
                  (if (<= 0 n)
                      t
                    (consp lst)
                    )))
  :hints (("Goal" :in-theory (enable memberp))))

(defthm memberp-nth-of-self
  (equal (memberp (nth n lst) lst)
         (if (<= 0 n)
             (if (< n (len lst))
                 t
               (if (integerp n)
                   (memberp nil lst)
                 (consp lst))) ;clean this up?
           (consp lst)))
  :hints (("Goal" :in-theory (enable memberp ))))
