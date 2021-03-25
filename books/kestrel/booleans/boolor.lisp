; A book about boolor (boolean-valued disjunction)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: In-progress

(include-book "bool-fix")

(defund boolor (x y)
  (declare (type t x y))
  (if x t (if y t nil)))

(defthm booleanp-of-boolor
  (booleanp (boolor x y)))

(defthm boolor-associative
  (equal (boolor (boolor x y) z)
         (boolor x (boolor y z)))
  :hints (("Goal" :in-theory (enable boolor))))

(defthm boolor-commutative
  (equal (boolor x y)
         (boolor y x))
  :hints (("Goal" :in-theory (enable boolor))))

(defthm boolor-commutative-2
  (equal (boolor x (boolor y z))
         (boolor y (boolor x z)))
  :hints (("Goal" :in-theory (enable boolor))))

(defthm boolor-combine-constants
  (implies (syntaxp (and (quotep a) (quotep b)))
           (equal (boolor a (boolor b c))
                  (boolor (boolor a b) c))))

(defthm boolor-same
  (equal (boolor x x)
         (bool-fix x))
  :hints (("Goal" :in-theory (enable boolor))))

(defthm boolor-same-2
  (equal (boolor x (boolor x y))
         (boolor x y))
  :hints (("Goal" :in-theory (enable boolor))))

;gen to non-nil?
(defthm boolor-of-t-arg1
  (equal (boolor t x)
         t)
  :hints (("Goal" :in-theory (enable boolor))))

;gen to non-nil?
(defthm boolor-of-t-arg2
  (equal (boolor x t)
         t)
  :hints (("Goal" :in-theory (enable boolor))))

(defthm boolor-of-nil-arg1
  (equal (boolor nil x)
         (bool-fix x))
  :hints (("Goal" :in-theory (enable boolor))))

(defthm boolor-of-nil-arg2
  (equal (boolor x nil)
         (bool-fix x))
  :hints (("Goal" :in-theory (enable boolor))))

(defthm boolor-of-non-nil
  (implies (and (syntaxp (quotep k))
                k)
           (equal (boolor k x)
                  t))
  :hints (("Goal" :in-theory (enable boolor))))

(defthm boolor-of-non-nil-arg2
  (implies (and (syntaxp (quotep k))
                k)
           (equal (boolor x k)
                  t))
  :hints (("Goal" :in-theory (enable boolor))))

;the x and the (not x) may be separated by other disjuncts unless we ignore not when sorting terms..
(defthm boolor-of-not-same
  (equal (boolor x (not x))
         t)
  :hints (("Goal" :in-theory (enable boolor))))

;if we sort args to boolor, this shouldn't happen
(defthm boolor-of-not-same-alt
  (equal (boolor (not x) x)
         t)
  :hints (("Goal" :in-theory (enable boolor))))

(defthm boolor-of-not-same-three-terms
  (equal (boolor x (boolor (not x) y))
         t))

(defthm boolor-of-not-same-three-terms-alt
  (equal (boolor (not x) (boolor x y))
         t))

;TODO: should commute args and ignore the not..
(defthm boolor-not-hack
  (equal (boolor (not x) (boolor y (boolor x z)))
         t))

;how many more like this are there?
;can we safely assume the first argument of a boolor false when rewriting the 2nd argument?
(defthm boolor-of-not-of-boolor-same
  (equal (boolor x (not (boolor x y)))
         (boolor x (not y))))

;; Helps justify the STP translation.
(defthm boolor-of-bool-fix-arg1
  (equal (boolor (bool-fix x) y)
         (boolor x y))
  :hints (("Goal" :in-theory (enable bool-fix$inline))))

;; Helps justify the STP translation.
(defthm boolor-of-bool-fix-arg2
  (equal (boolor x (bool-fix y))
         (boolor x y))
  :hints (("Goal" :in-theory (enable bool-fix$inline))))

;; These help justify some things that Axe does:
(defcong iff equal (boolor x y) 1 :hints (("Goal" :in-theory (enable boolor))))
(defcong iff equal (boolor x y) 2 :hints (("Goal" :in-theory (enable boolor))))

(defthmd not-of-if-of-nil-arg3-when-booleans
  (implies (and (booleanp x)
                (booleanp y))
           (equal (not (if x y nil)) ;; "not and"
                  (acl2::boolor (not x) (not y)))))
