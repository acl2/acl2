; Theorems about boolean operations
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

(include-book "../utilities/myif") ; reduce?
(include-book "bool-fix")
(include-book "boolor")
(include-book "boolxor")
(include-book "booland")
(include-book "boolif")
(include-book "iff")
(include-book "not")

;;These rules and boolif-when-quotep-arg1 should prevent boolif from ever having a constant in any argument position:

(defthm boolif-when-quotep-arg2
  (implies (syntaxp (quotep x))
           (equal (boolif test x y)
                  (if x
                      (boolor test y)
                    (booland (not test) y))))
  :hints (("Goal" :in-theory (enable boolor boolif))))

(defthm boolif-when-quotep-arg3
  (implies (syntaxp (quotep y))
           (equal (boolif test x y)
                  (if y
                      (boolor (not test) x)
                    (booland test x))))
  :hints (("Goal" :in-theory (enable booland boolif))))

(defthm boolif-x-x-y
  (equal (boolif x x y)
         (boolor x y))
  :hints (("Goal" :in-theory (enable boolor boolif))))

(defthm boolif-x-y-x
  (equal (boolif x y x)
         (booland x y))
  :hints (("Goal" :in-theory (enable booland boolif))))

(defthm boolif-boolif-lift-same
  (equal (boolif test1 (boolif test2 x y) y)
         (boolif (booland test1 test2) x y))
  :hints (("Goal" :in-theory (enable boolif booland))))

(defthm equal-of-t-when-booleanp
  (implies (booleanp x)
           (equal (equal t x)
                  x)))

;if we are commuting equalities the other way
(defthm equal-of-t-when-booleanp-arg2
  (implies (booleanp x)
           (equal (equal x t)
                  x)))

;Disabled by default.  We could add an (enabled version) in which both conjuncts are calls to NOT?
(defthmd not-of-booland
  (equal (not (booland x y))
         (boolor (not x) (not y)))
  :hints (("Goal" :in-theory (enable booland))))

;Disabled by default.  We could add an (enabled version) in which both conjuncts are calls to NOT?
(defthmd not-of-boolor
  (equal (not (boolor x y))
         (booland (not x) (not y)))
  :hints (("Goal" :in-theory (enable boolor))))

;use a congruence
(defthm not-of-bool-fix
  (equal (not (bool-fix x))
         (not x)))

;do we prefer (equal nil x) or (not x) - maybe it depends on whether x is boolean
;(equal nil x) allows substitution
;do we have a rule for (equal nil (equal nil x)) ?
(defthm equal-nil-of-not
  (equal (equal 'nil (not x))
         (bool-fix x)))

;drop the bool-fix and add a hyp?
;disabling:
;in acl2 proofs, this seems to match a hyp of the form (equal nil x) and make it into (not x)
(defthmd not-equal-nil
  (equal (not (equal nil x))
         (bool-fix x)))

;do we want this?
(defthm equal-of-nil-when-booleanp
  (implies (booleanp x)
           (equal (equal nil x)
                  (not x))))

;TODO: more like this!
(defthm boolor-of-booland-same
  (equal (boolor x (booland x y))
         (bool-fix x))
  :hints (("Goal" :in-theory (enable boolor))))

(defthm boolor-of-booland-same-alt
  (equal (boolor x (booland y x))
         (bool-fix x))
  :hints (("Goal" :in-theory (enable boolor))))

;others like this? 3 conjuncts?
(defthm booland-of-not-same
  (equal (booland x (not x))
         nil))

;not needed if we commute arguments to booland (ignoring not)
(defthm booland-of-not-same-alt
  (equal (booland (not x) x)
         nil))

;rename?
(defthm booland-of-not-and-booland-same
  (equal (booland x (booland (not x) y))
         nil))

;rename?
;not needed if we commute arguments to booland (ignoring not)
(defthm booland-of-not-and-booland-same-alt
  (equal (booland (not x) (booland x y))
         nil))

(defthm boolor-of-booland-not-boolor
  (equal (boolor (booland (not x) y) (boolor x z))
         (boolor y (boolor x z)))
  :hints (("Goal" :in-theory (enable boolor))))

(defthm boolif-of-not-of-boolor-same
  (equal (boolif test x (not (boolor test y)))
         (boolif test x (not y)))
  :hints (("Goal" :in-theory (enable boolif))))

(defthm booland-of-bool-fix-arg1
  (equal (booland (bool-fix x) y)
         (booland x y))
  :hints (("Goal" :in-theory (enable booland))))

(defthm booland-of-bool-fix-arg2
  (equal (booland x (bool-fix y))
         (booland x y))
  :hints (("Goal" :in-theory (enable booland))))

(defthm boolif-of-not-same-arg3
  (equal (boolif x y (not x))
         (boolor y (not x)))
  :hints (("Goal" :in-theory (enable boolif))))

(defthm boolif-of-not-same-arg2
  (equal (boolif x (not x) y)
         (booland y (not x)))
  :hints (("Goal" :in-theory (enable boolif))))

;more like this?!
;need a booland-when and boolor-when?
(defthm boolif-of-booland-of-boolor
  (equal (boolif x (booland (boolor x y) w) z)
         (boolif x w z))
  :hints (("Goal" :in-theory (enable booland boolif boolor))))

(defthm boolif-of-boolor-of-boolor
  (equal (boolif x y (boolor (boolor x w) z))
         (boolif x y (boolor w z)))
  :hints (("Goal" :in-theory (enable booland boolif boolor))))

(defthm boolif-of-boolor-same
  (equal (boolif x y (boolor x z))
         (boolif x y z))
  :hints (("Goal" :in-theory (enable boolor boolif))))

(defthm boolif-of-booland-same
  (equal (boolif x (booland x z) y)
         (boolif x z y))
  :hints (("Goal" :in-theory (enable boolor boolif booland))))



;seems better than just using the definition of implies:
(defthmd implies-opener
  (equal (implies p q)
         (boolor (not p) q)))


(defthm boolor-of-bool-fix-arg1
  (equal (boolor (bool-fix x) y)
         (boolor x y))
  :hints (("Goal" :in-theory (enable boolor))))

(defthm boolor-of-bool-fix-arg2
  (equal (boolor x (bool-fix y))
         (boolor x y))
  :hints (("Goal" :in-theory (enable boolor))))

(defthmd myif-becomes-boolif
  (implies (and (booleanp b)
                (booleanp c))
           (equal (myif a b c)
                  (boolif a b c)))
  :hints (("Goal" :in-theory (enable myif boolif))))

;or rewrite the not of boolor
(defthm boolor-of-not-of-boolor-of-not-same
  (equal (boolor x (not (boolor y (not x))))
         (bool-fix x)))
