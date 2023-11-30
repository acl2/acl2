; A book about boolif (boolean-valued if-then-else)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
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

(defthm boolif-when-quotep-arg1
  (implies (syntaxp (quotep test))
           (equal (boolif test x y)
                  (if test
                      (bool-fix x)
                    (bool-fix y))))
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
  (equal (boolif test (if test x1 x2) y)
         (boolif test (boolif test x1 x2) y)))

(theory-invariant (incompatible (:rewrite boolif-of-if-arg2) (:defintion boolif)))

(defthmd boolif-of-if-arg3
  (equal (boolif test x (if test y1 y2))
         (boolif test x (boolif test y1 y2))))

(theory-invariant (incompatible (:rewrite boolif-of-if-arg3) (:defintion boolif)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; could restrict to v1 and v2 being constants
(defthm boolif-of-equal-and-nil-and-equal-diff
  (implies (not (equal v1 v2))
           (equal (boolif (equal v1 x) nil (equal v2 x))
                  (equal v2 x))))
