; Theorems about boolean operations
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

(include-book "../utilities/myif")
(include-book "bool-fix")
(include-book "boolor")
(include-book "boolxor")
(include-book "booland")
(include-book "boolif")

;make rules for combining constants?  or not, since we always know what happens to a constant - maybe just for xor?

;;
;; not
;;

;should not be enabled or disabled?

(defthm not-of-not
  (equal (not (not x))
         (bool-fix x)))


;;These 3 rules should prevent boolif from ever having a constant in any argument position:

(defthm boolif-when-quotep-arg1
  (implies (syntaxp (quotep test))
           (equal (boolif test x y)
                  (if test
                      (bool-fix x)
                    (bool-fix y))))
  :hints (("Goal" :in-theory (enable boolif))))

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


(defthm boolif-x-x-y
  (equal (boolif x x y)
         (boolor x y))
  :hints (("Goal" :in-theory (enable boolor boolif))))

(defthm boolif-x-y-x
  (equal (boolif x y x)
         (booland x y))
  :hints (("Goal" :in-theory (enable booland boolif))))

(defthm xor-associative
  (implies (and (booleanp a)
                (booleanp b)
                (booleanp c))
           (equal (xor (xor a b) c)
                  (xor a (xor b c))))
  :hints (("Goal" :in-theory (enable xor))))

(defthm xor-nil
  (implies (booleanp x)
           (equal (xor nil x)
                  x)))

;We have this because we can disable it.
(defund mynot (x)
  (not x))

(defthm xor-t
  (implies (booleanp x)
           (equal (xor t x)
                  (mynot x)))
  :hints (("Goal" :in-theory (enable xor mynot))))

(defthm mynot-mynot
  (implies (booleanp x)
           (equal (mynot (mynot x))
                  x))
  :hints (("Goal" :in-theory (enable mynot))))

(defthm xor-of-mynot-1
  (equal (xor (mynot a) b)
         (mynot (xor a b)))
  :hints (("Goal" :in-theory (enable xor mynot))))

(defthm xor-of-mynot-2
  (equal (xor b (mynot a))
         (mynot (xor b a)))
  :hints (("Goal" :in-theory (enable xor mynot))))

;yuck?!
(defthm xor-when-equal
  (implies (equal x y)
           (equal (xor x y)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

;or should we rewrite the order of equal?
(defthm xor-equal-hack
  (equal (xor (equal x y) (equal y x))
         nil)
  :hints (("Goal" :in-theory (enable xor))))

(defthm xor-combine-constants
  (implies (syntaxp (and (quotep a) (quotep b)))
           (equal (xor a (xor b c))
                  (xor (xor a b) c)))
  :hints (("Goal" :in-theory (enable xor))))

(defthm xor-same
  (implies (booleanp b)
           (equal (xor a (xor a b))
                  b))
  :hints (("Goal" :in-theory (enable xor))))

(defthm xor-same-simple
  (equal (xor a a)
         nil)
  :hints (("Goal" :in-theory (enable xor))))

(defthm xor-mynot
  (equal (xor x (mynot x))
         t)
  :hints (("Goal" :in-theory (enable xor mynot))))

(defthm xor-mynot-2
  (equal (xor (mynot x) x)
         t)
  :hints (("Goal" :in-theory (enable xor mynot))))

(defthm xor-mynot-alt
  (equal (xor x (xor (mynot x) y))
         (mynot y))
  :hints (("Goal" :in-theory (enable xor mynot))))

(defthm xor-mynot-alt2
  (equal (xor (mynot x) (xor x y))
         (mynot y))
  :hints (("Goal" :in-theory (enable xor mynot))))

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

;we may often open up iff, but here are some theorems about it anyway:

(defthm iff-of-t-arg1
  (equal (iff t x)
         (bool-fix x)))

(defthm iff-of-t-arg2
  (equal (iff x t)
         (bool-fix x)))

(defthm iff-of-nil-arg1
  (equal (iff nil x)
         (not x)))

(defthm iff-of-nil-arg2
  (equal (iff x nil)
         (not x)))

(defthm iff-same
  (equal (iff x x)
         t))

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
