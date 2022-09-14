; Rules about sbvdivdown
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "sbvrem-rules")
(include-book "sbvdivdown")
(include-book "sbvdiv")
(include-book "bvdiv")
(include-book "rules8") ; for stuff like FLOOR-OF-SUM-OF-MINUS-EXPT-AND-BVCHOP
(include-book "rules") ; make local or drop
(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor2" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/divide" :dir :system))

(in-theory (enable floor-when-multiple)) ;drop?

;gen
(defthm unsigned-byte-p-of-sbvdivdown
  (unsigned-byte-p 32 (sbvdivdown 32 x y))
  :hints (("Goal" :in-theory (enable sbvdivdown))))

(defthm sbvdivdown-of-bvchop-arg2
  (implies (posp size)
           (equal (sbvdivdown size (bvchop size x) y)
                  (sbvdivdown size x y)))
  :hints (("Goal" :in-theory (enable sbvdivdown))))

(defthm sbvdivdown-of-bvchop-arg3
  (implies (posp size)
           (equal (sbvdivdown size y (bvchop size x))
                  (sbvdivdown size y x)))
  :hints (("Goal" :in-theory (enable sbvdivdown))))

(defthm sbvdivdown-when-bvchop-known-subst-arg2
  (implies (and (equal (bvchop size x) free)
                (syntaxp (quotep free))
                (posp size))
           (equal (sbvdivdown size x y)
                  (sbvdivdown size free y)))
  :hints (("Goal" :in-theory (enable sbvdivdown))))

(defthm sbvdivdown-when-bvchop-known-subst-arg3
  (implies (and (equal (bvchop size x) free)
                (syntaxp (quotep free))
                (posp size))
           (equal (sbvdivdown size y x)
                  (sbvdivdown size y free)))
  :hints (("Goal" :in-theory (enable sbvdivdown))))

(defthmd sbvdivdown-rewrite-case-1
  (implies (and (equal 0 (bvchop size y))
                (posp size))
           (equal (sbvdivdown size x y)
                  0))
  :hints (("Goal" :in-theory (enable sbvdiv sbvdivdown logext logapp))))

(defthm sbvdivdown-rewrite-case-2
  (implies (and (not (equal 0 (bvchop size y)))
                (and (sbvle size 0 x)
                     (sbvle size 0 y))
                (natp x)
                (natp y)
                (posp size))
           (equal (sbvdivdown size x y)
                  (bvdiv (+ -1 size) x y)))
  :hints (("Goal" :in-theory (enable sbvdiv sbvdivdown logext logapp bvdiv sbvlt))))

(defthmd sbvdivdown-rewrite-case-3
  (implies (and (not (equal 0 (bvchop size y)))
                (and (sbvlt size x 0)
                     (sbvlt size y 0))
                (natp x)
                (natp y)
                (posp size))
           (equal (sbvdivdown size x y)
                  (sbvdiv size x y)))
  :hints (("Goal" :in-theory (e/d (sbvdiv sbvdivdown logext logapp bvdiv sbvlt bvplus bvuminus bvminus
                                          bvchop-of-sum-cases
                                          BVCHOP-REDUCE-WHEN-TOP-BIT-KNOWN
                                          bvcat
                                          logapp
                                          TRUNCATE-BECOMES-FLOOR-GEN
                                          )
                                  (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   SBVLT-REWRITE
                                   ;anti-bvplus
                                   )))))

(defthmd sbvdivdown-rewrite-case-4
  (implies (and (not (equal 0 (bvchop size y)))
                (not (and (sbvle size 0 x)
                          (sbvle size 0 y)))
                (not (and (sbvlt size x 0)
                          (sbvlt size y 0)))
                (equal 0 (sbvrem size x y)) ;todo: use bvmod instead?
                (natp x)
                (natp y)
                (posp size))
           (equal (sbvdivdown size x y)
                  (sbvdiv size x y)))
  :hints (("Goal" :in-theory (e/d (sbvdiv
                                   sbvdivdown
                                   LOGEXT-NEGATIVE
                                   LOGEXT-WHEN-NEGATIVE-2
;logext logapp bvdiv
                                   sbvlt ;sbvrem
                                   BVCHOP-REDUCE-WHEN-TOP-BIT-KNOWN
                                   bvchop-when-top-bit-not-1
                                   bvchop-of-sum-cases
                                   bvmod
                                   bvuminus
                                   bvminus
                                   bvplus
                                   bvcat logapp
                                   truncate-becomes-floor-other
                                   ) (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   ;mod-sum-cases
;NOT-EQUAL-CONSTANT-WHEN-BOUND-FORBIDS-IT2 ;add syntaxp hyp?
                                   ;anti-bvplus
                                   ;SBVDIV-rewrite
                                      )))))


;; ;move
;; (defthm equal-of-0-and-mod-forward
;;   (implies (and (equal 0 (mod (+ x y) z))
;;                 (rationalp x)
;;                 (rationalp y)
;;                 (rationalp z))
;;            (integerp (+ (/ x z) (/ y z))))
;;   :rule-classes :forward-chaining
;;   :hints (("Goal" :in-theory (enable equal-of-0-and-mod))))

(defthmd sbvdivdown-rewrite-case-5
  (implies (and (not (equal 0 (bvchop size y)))
                (not (and (sbvle size 0 x)
                          (sbvle size 0 y)))
                (not (and (sbvlt size x 0)
                          (sbvlt size y 0)))
                (not (equal 0 (sbvrem size x y))) ;fixme use bvmod instead?
                (natp x)
                (natp y)
                (posp size))
           (equal (sbvdivdown size x y)
                  (bvplus size -1 (sbvdiv size x y))))
  :hints (("Goal" :in-theory (e/d (sbvdiv
                                   sbvdivdown
                                   LOGEXT-NEGATIVE
                                   LOGEXT-WHEN-NEGATIVE-2
                                   ;;logext logapp bvdiv
                                   sbvlt ;sbvrem
                                   BVCHOP-REDUCE-WHEN-TOP-BIT-KNOWN
                                   bvchop-when-top-bit-not-1
                                   bvchop-of-sum-cases
                                   bvmod
                                   bvuminus
                                   bvminus
                                   bvplus
                                   bvcat logapp
                                   truncate-becomes-floor-other
                                   )
                                  (;disabling these fixed a failure when moving to acl2 5.0:
                                   EQUAL-BVCHOP-BVCHOP-MOVE-MINUS
                                   (:REWRITE BVCHOP-OF-MINUS-1)
                                   (:REWRITE BVCHOP-PLUS-1-SPLIT)
                                   (:REWRITE UNSIGNED-BYTE-P-OF-FLOOR)

                                   EQUAL-OF-0-AND-FLOOR
                                   BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   FLOOR-OF-1-ARG1 ;why?
                                   mod-sum-cases
                                   ;NOT-EQUAL-CONSTANT-WHEN-BOUND-FORBIDS-IT2 ;add syntaxp hyp?
                                   ;anti-bvplus
                                   ;SBVDIV-rewrite
                                   EXPT-HALF-LINEAR
                                   )))))

;need to turn sbvdivdown into STP primitives (sbvdiv may be further turned into bvdiv?)
(defthmd sbvdivdown-rewrite
  (implies (and (posp size)
                (natp x)
                (natp y))
           (equal (sbvdivdown size x y)
                  (if (equal 0 (bvchop size y))
                      0
                    (if (and (sbvle size 0 x)
                             (sbvle size 0 y))
                        ;;both arguments are non-negative, so we can just call bvdiv
                        (bvdiv (+ -1 size) x y)
                      (if (and (sbvlt size x 0)
                               (sbvlt size y 0))
                          (sbvdiv size x y) ;the quotient is non-negative, so sbvdiv rounds the way we want
                        ;;otherwise, to quotient is negative, so sbvdiv rounds up, but we want to round down
                        (if (equal 0 (sbvrem size x y))
                            ;;no rounding, so the sbvdiv result is right
                            (sbvdiv size x y)
                          ;;sbvdiv rounded up, and we want to round down, so subtract 1
                          (bvplus size -1 (sbvdiv size x y))))))))
  :hints (("Goal" :cases ((and (SBVLT SIZE X '0) (SBVLT SIZE Y 0))
                          (and (not (SBVLT SIZE X '0)) (SBVLT SIZE Y 0)))
           :in-theory (e/d (sbvlt
                              sbvdivdown-rewrite-case-1
                              sbvdivdown-rewrite-case-2
                              sbvdivdown-rewrite-case-3
                              sbvdivdown-rewrite-case-4
                              sbvdivdown-rewrite-case-5)
                           (bvdiv)))))

(defthm sbvdivdown-rewrite-gen
  (implies (posp size)
           (equal (sbvdivdown size x y)
                  (if (equal 0 (bvchop size y))
                      0
                      (if (and (sbvle size 0 x) (sbvle size 0 y))
                          (bvdiv (+ -1 size) x y)
                          (if (and (sbvlt size x 0) (sbvlt size y 0))
                              (sbvdiv size x y)
                              (if (equal 0 (sbvrem size x y))
                                  (sbvdiv size x y)
                                  (bvplus size -1 (sbvdiv size x y))))))))
  :hints (("Goal" :use (:instance sbvdivdown-rewrite (x (bvchop size x)) (y (bvchop size y)))
           :in-theory (disable sbvdivdown-rewrite
                               ;;sbvdiv-rewrite
                               sbvrem-rewrite))))

(local
 (defthm bvdiv-lemma
   (implies (and (integerp x)
                 (<= 4 (bvchop 31 x)))
            (equal (bvdiv 31 (+ -4 x) 4)
                   (+ -1 (bvdiv 31 x 4))))
   :hints (("Goal" :in-theory (enable bvdiv
                                      bvchop-of-sum-cases)))))

;drop?
(defthm sbvdivdown-of-bvplus-minus4
  (implies (unsigned-byte-p 31 x) ;gen!
           (equal (sbvdivdown 32 (bvplus 32 4294967292 x) 4)
                  (bvplus 32 -1 (sbvdivdown 32 x 4))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (;sbvdivdown
                                   sbvdiv
                                   bvplus
                                   ;;bvdiv
                                   bvmod
                                   logext-of-plus
                                   bvuminus
                                   sbvlt-rewrite
                                   ;SBVDIVDOWN-REWRITE-CASE-2
                                   bvchop-of-sum-cases
                                   getbit-of-plus
                                   truncate-becomes-floor-gen
                                   )
                                  (BVLT-OF-BVCHOP-ARG2
                                   BVLT-OF-BVCHOP-ARG3)))))
