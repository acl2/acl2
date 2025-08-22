; A book about boolif (boolean-valued if-then-else)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: In-progress

(include-book "bool-fix")

(defund boolif (test x y)
  (declare (xargs :guard t))
  (if (if test x y)
      t
    nil))

;; Only needed for Axe?
(defthmd booleanp-of-boolif
  (booleanp (boolif x y z)))

;; See also boolif-when-quotep-arg2 and boolif-when-quotep-arg3 elsewhere.
(defthm boolif-when-quotep-arg1
  (implies (syntaxp (quotep test))
           (equal (boolif test x y)
                  (if test
                      (bool-fix x)
                    (bool-fix y))))
  :hints (("Goal" :in-theory (enable boolif))))

(defthm boolif-when-quotep-and-not-booleanp-arg2
  (implies (and (syntaxp (quotep x))
                (not (booleanp x)))
           (equal (boolif test x y)
                  (boolif test (bool-fix x) y)))
  :hints (("Goal" :in-theory (enable boolif))))

(defthm boolif-when-quotep-and-not-booleanp-arg3
  (implies (and (syntaxp (quotep y))
                (not (booleanp y)))
           (equal (boolif test x y)
                  (boolif test x (bool-fix y))))
  :hints (("Goal" :in-theory (enable boolif))))


;; Does not introduce bool-fix, unlike boolif-of-t-and-nil.
(defthmd boolif-of-t-and-nil-when-booleanp
  (implies (booleanp x)
           (equal (boolif x t nil)
                  x))
  :hints (("Goal" :in-theory (enable boolif))))

(defthm boolif-of-t-and-nil
  (equal (boolif x t nil)
         (bool-fix x))
  :hints (("Goal" :in-theory (enable boolif))))

(defthm boolif-of-nil-and-t
  (equal (boolif x nil t)
         (not x))
  :hints (("Goal" :in-theory (enable boolif))))

(defthm boolif-same-branches
  (equal (boolif test x x)
         (bool-fix x))
  :hints (("Goal" :in-theory (enable boolif))))

(defthm boolif-same-arg1-arg2
  (implies (syntaxp (not (quotep x))) ; avoids loop when x='t, this hyp is supported by Axe
           (equal (boolif x x y)
                  (boolif x t y)))
  :hints (("Goal" :in-theory (enable boolif))))

(defthm boolif-x-y-x
  (implies (syntaxp (not (quotep x))) ; prevent loops
           (equal (boolif x y x)
                  (boolif x y nil)))
  :hints (("Goal" :in-theory (enable boolif))))

(defthm boolif-of-not
  (equal (boolif (not test) x y)
         (boolif test y x))
  :hints (("Goal" :in-theory (enable boolif))))

;do we want this?
(defthm not-of-boolif
  (equal (not (boolif test x y))
         (boolif test (not x) (not y)))
  :hints (("Goal" :in-theory (enable boolif))))

;; Helps justify the STP translation.
(defthm boolif-of-bool-fix-arg1
  (equal (boolif (bool-fix x) y z)
         (boolif x y z))
  :hints (("Goal" :in-theory (enable boolif))))

;; Helps justify the STP translation.
(defthm boolif-of-bool-fix-arg2
  (equal (boolif x (bool-fix y) z)
         (boolif x y z))
  :hints (("Goal" :in-theory (enable boolif))))

;; Helps justify the STP translation.
(defthm boolif-of-bool-fix-arg3
  (equal (boolif x y (bool-fix z))
         (boolif x y z))
  :hints (("Goal" :in-theory (enable boolif))))

(defthm boolif-of-not-same-arg3-alt
  (equal (boolif x y (not x))
         (boolif x y t))
  :hints (("Goal" :in-theory (enable boolif))))

(defthm boolif-of-not-same-arg2-alt
  (equal (boolif x (not x) y)
         (boolif x nil y))
  :hints (("Goal" :in-theory (enable boolif))))

(defthmd if-becomes-boolif
  (implies (and (booleanp x)
                (booleanp y))
           (equal (if test x y)
                  (boolif test x y)))
  :hints (("Goal" :in-theory (enable boolif))))

;; These help justify some things that Axe does:
(defcong iff equal (boolif test x y) 1 :hints (("Goal" :in-theory (enable boolif))))
(defcong iff equal (boolif test x y) 2 :hints (("Goal" :in-theory (enable boolif))))
(defcong iff equal (boolif test x y) 3 :hints (("Goal" :in-theory (enable boolif))))

;for outside-in rewriting:
(defthm boolif-when-not-nil
  (implies test
           (equal (boolif test x y)
                  (bool-fix x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable boolif)))
  )

;for outside-in rewriting (do not remove the hyp):
(defthm boolif-when-nil
  (implies (equal nil test)
           (equal (boolif test x y)
                  (bool-fix y)))
  :rule-classes nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd boolif-of-if-arg1
  (equal (boolif (if test test1 test2) x y)
         (boolif (boolif test test1 test2) x y)))

(theory-invariant (incompatible (:rewrite boolif-of-if-arg1) (:defintion boolif)))

(defthmd boolif-of-if-arg2
  (equal (boolif test (if test2 x1 x2) y)
         (boolif test (boolif test2 x1 x2) y)))

(theory-invariant (incompatible (:rewrite boolif-of-if-arg2) (:defintion boolif)))

(defthmd boolif-of-if-arg3
  (equal (boolif test x (if test3 y1 y2))
         (boolif test x (boolif test3 y1 y2))))

(theory-invariant (incompatible (:rewrite boolif-of-if-arg3) (:defintion boolif)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; could restrict to v1 and v2 being constants
(defthm boolif-of-equal-and-nil-and-equal-diff
  (implies (not (equal v1 v2))
           (equal (boolif (equal v1 x) nil (equal v2 x))
                  (equal v2 x))))

;; "x or y" and "x" is just x
;todo: rename to have 'same' in the name
(defthm boolif-of-boolif-of-t-and-nil
  (equal (boolif (boolif x t y) x nil)
         (acl2::bool-fix x))
  :hints (("Goal" :in-theory (enable acl2::bool-fix))))

;; This reduces one mention of X and only increases the mentions of nil
(defthm boolif-combine-1
  (equal (boolif (boolif x z1 z2) (boolif x z3 z4) nil)
         (boolif x
                 (boolif z1 z3 nil)
                 (boolif z2 z4 nil)))
  :hints (("Goal" :in-theory (enable boolif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These can help when we have a genealized boolean as an arg:

(defthmd boolif-when-not-booleanp-arg1
  (implies (not (booleanp test))
           (equal (boolif test x y)
                  (bool-fix x))))

(defthmd boolif-when-not-booleanp-arg2
  (implies (not (booleanp x))
           (equal (boolif test x y)
                  (boolif test t y))))

(defthmd boolif-when-not-booleanp-arg3
  (implies (not (booleanp y))
           (equal (boolif test x y)
                  (boolif test x t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; integers are a common kind of generalized boolean
(defthmd boolif-when-integerp-arg2
  (implies (integerp x)
           (equal (boolif test x y)
                  (boolif test t y))))

(defthmd boolif-when-integerp-arg3
  (implies (integerp y)
           (equal (boolif test x y)
                  (boolif test x t))))
