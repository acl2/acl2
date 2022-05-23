; Axe rules about booleans
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "known-booleans")
(include-book "kestrel/booleans/booland" :dir :system)
(include-book "kestrel/booleans/boolor" :dir :system)
(include-book "kestrel/booleans/boolxor" :dir :system)
(include-book "axe-syntax-functions") ;for SYNTACTIC-CALL-OF
(include-book "axe-syntax-functions-boolean") ;for syntactic-booleanp
(include-book "kestrel/booleans/boolif" :dir :system)
(include-book "axe-syntax")
(include-book "kestrel/utilities/myif" :dir :system)

(add-known-boolean booland)
(add-known-boolean boolor)
(add-known-boolean boolxor)
(add-known-boolean boolif)
(add-known-boolean bool-fix$inline)

;the axe-syntaxp is new
(defthmd myif-becomes-boolif-axe
  (implies (and (axe-syntaxp (syntactic-booleanp b dag-array)) ;could be optimized with a single call to an axe-syntaxp function that checks both
                (axe-syntaxp (syntactic-booleanp c dag-array))
                (booleanp b)
                (booleanp c))
           (equal (myif a b c)
                  (boolif a b c)))
  :hints (("Goal" :in-theory (enable myif boolif))))

(defthmd equal-of-booleans-axe
  (implies (and (axe-syntaxp (syntactic-booleanp x dag-array))
                (axe-syntaxp (syntactic-booleanp y dag-array))
                (booleanp x)
                (booleanp y))
           (equal (equal x y)
                  (iff x y))))

(defthmd boolor-commutative-axe
  (implies (axe-syntaxp (should-commute-args-dag 'boolor x y dag-array))
           (equal (boolor x y)
                  (boolor y x)))
  :hints (("Goal" :in-theory (enable boolor))))

(defthmd boolor-commutative-2-axe
  (implies (axe-syntaxp (should-commute-args-dag 'boolor x y dag-array))
           (equal (boolor x (boolor y z))
                  (boolor y (boolor x z))))
  :hints (("Goal" :in-theory (enable boolor))))

(defthmd booland-commutative-axe
  (implies (axe-syntaxp (should-commute-args-dag 'booland x y dag-array))
           (equal (booland x y)
                  (booland y x)))
  :hints (("Goal" :in-theory (enable booland))))

(defthmd booland-commutative-2-axe
  (implies (axe-syntaxp (should-commute-args-dag 'booland x y dag-array))
           (equal (booland x (booland y z))
                  (booland y (booland x z))))
  :hints (("Goal" :in-theory (enable booland))))

(defthmd boolxor-commutative-axe
  (implies (axe-syntaxp (should-commute-args-dag 'boolxor x y dag-array))
           (equal (boolxor x y)
                  (boolxor y x)))
  :hints (("Goal" :in-theory (enable boolxor))))

(defthmd boolxor-commutative-2-axe
  (implies (axe-syntaxp (should-commute-args-dag 'boolxor x y dag-array))
           (equal (boolxor x (boolxor y z))
                  (boolxor y (boolxor x z))))
  :hints (("Goal" :in-theory (enable boolxor))))
