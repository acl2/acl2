; sbvmoddown
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

(include-book "bvchop")
(include-book "logext")
(include-book "bvmod")
(include-book "bvcat")
(include-book "sbvrem")
(include-book "sbvrem-rules")
(include-book "logext")
(include-book "unsigned-byte-p-forced")
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divides" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/rem" :dir :system))

(local (in-theory (disable BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))

;todo: move?
(defund sbvmoddown (n x y)
  (declare (type integer x y)
           (type (integer 1 *) n)
           (xargs :guard (not (EQUAL (LOGEXT N Y) 0))) ;rephrase in terms of bvchop?
           )
  (bvchop n (mod (logext n x) (logext n y))))

(defthm sbvmoddown-of-1
  (equal (sbvmoddown 32 x 1)
         0)
  :hints (("Goal" :in-theory (enable sbvmoddown))))

(defthmd sbvmoddown-rewrite-case-1
  (implies (and (equal 0 (bvchop size y))
                (posp size))
           (equal (sbvmoddown size x y)
                  (bvchop size x)))
  :hints (("Goal" :in-theory (enable ;sbvrem
                              sbvmoddown logext logapp
                              BVCHOP-WHEN-TOP-BIT-NOT-1 BVCHOP-WHEN-TOP-BIT-1
                              bvchop-of-sum-cases
                              ))))

(defthmd sbvmoddown-rewrite-case-2
  (implies (and (not (equal 0 (bvchop size y)))
                (and (sbvle size 0 x)
                     (sbvle size 0 y))
                (natp x)
                (natp y)
                (posp size))
           (equal (sbvmoddown size x y)
                  (bvmod (+ -1 size) x y)))
  :hints (("Goal" :in-theory (enable sbvmoddown logext logapp bvmod sbvlt))))

(defthmd sbvmoddown-rewrite-case-3
  (implies (and (not (equal 0 (bvchop size y)))
                (and (sbvlt size x 0)
                     (sbvlt size y 0))
                (natp x)
                (natp y)
                (posp size))
           (equal (sbvmoddown size x y)
                  (sbvrem size x y)))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (sbvrem sbvmoddown logext logapp bvmod sbvlt bvplus bvuminus bvminus
                                          bvchop-of-sum-cases
                                          BVCHOP-WHEN-TOP-BIT-NOT-1 BVCHOP-WHEN-TOP-BIT-1 ;BVCHOP-REDUCE-WHEN-TOP-BIT-KNOWN
                                          bvcat
                                          logapp
                                          rem-becomes-mod)
                                  (BVCHOP-UPPER-BOUND ;for speed
                                   ;MOD-BOUNDED-BY-MODULUS
                                   ;BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   ;sbvrem-rewrite
                                   ;;anti-bvplus
                                   )))))

(defthm equal-of-+-of-expt-of-one-less-and-expt-cancel
  (implies (integerp size)
           (equal (EQUAL (+ (EXPT 2 (+ -1 SIZE)) x) (EXPT 2 SIZE))
                  (equal x (EXPT 2 (+ -1 SIZE)))))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthmd sbvmoddown-rewrite-case-4
  (implies (and (not (equal 0 (bvchop size y)))
                (not (and (sbvle size 0 x)
                          (sbvle size 0 y)))
                (not (and (sbvlt size x 0)
                          (sbvlt size y 0)))
                (equal 0 (sbvrem size x y)) ;fixme use bvmod instead?
                (natp x)
                (natp y)
                (posp size))
           (equal (sbvmoddown size x y)
                  (sbvrem size x y)))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (sbvmoddown
                                   sbvrem
                                   LOGEXT-NEGATIVE
                                   LOGEXT-WHEN-NEGATIVE-2
                                   ;;logext logapp bvmod
                                   sbvlt
                                   BVCHOP-REDUCE-WHEN-TOP-BIT-KNOWN
                                   bvchop-when-top-bit-not-1
                                   ;;bvchop-of-sum-cases
                                   bvmod
                                   bvuminus
                                   bvminus
                                   bvplus
                                   bvcat logapp
                                   rem-becomes-mod
;mod-sum-cases
;bvchop-of-sum-cases
                                   ;;mod
                                   ;;expt-of-+
                                   sbvlt-rewrite
                                   )
                                  (;BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   sbvrem-rewrite
                                   ;mod-sum-cases
                                   ;;NOT-EQUAL-CONSTANT-WHEN-BOUND-FORBIDS-IT2 ;add syntaxp hyp?
                                   ;anti-bvplus
                                   ;;SBVREM-BECOMES-BVMOD
                                   sbvlt
                                   bvmod
                                   bvminus
                                   bvuminus

                                   )))))

(defthm equal-of-bvchop-and-bvchop-cancel
  (implies (and (natp size)
                (integerp x)
                (integerp y)
                (integerp z)
                (integerp zk))
           (equal (EQUAL (BVCHOP SIZE (+ Y z x)) (BVCHOP SIZE (+ zk x)))
                  (EQUAL (BVCHOP SIZE (+ Y z)) (BVCHOP SIZE zk)))))

(defthm sbvmoddown-rewrite-case-5-helper
  (implies (and (EQUAL 1 (GETBIT (+ -1 SIZE) Y))
                (posp size)
                (natp y))
           (EQUAL (BVCHOP SIZE (+ Y (EXPT 2 (+ -1 SIZE))))
                  (BVCHOP (+ -1 SIZE) Y)))
  :hints (("Goal" :in-theory (enable bvchop-of-sum-cases bvchop-when-top-bit-1))))

(defthmd sbvmoddown-rewrite-case-5
  (implies (and (not (equal 0 (bvchop size y)))
                (not (and (sbvle size 0 x)
                          (sbvle size 0 y)))
                (not (and (sbvlt size x 0)
                          (sbvlt size y 0)))
                (not (equal 0 (sbvrem size x y))) ;fixme use bvmod instead?
                (natp x)
                (natp y)
                (posp size))
           (equal (sbvmoddown size x y)
                  (bvplus size Y (sbvrem size x y))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (sbvmoddown-rewrite-case-5-helper
                                   sbvrem
                                   sbvmoddown
                                   LOGEXT-NEGATIVE
                                   LOGEXT-WHEN-NEGATIVE-2
;logext logapp bvmod
                                   sbvlt-rewrite
                                   BVCHOP-REDUCE-WHEN-TOP-BIT-KNOWN
                                   bvchop-when-top-bit-not-1
;bvchop-of-sum-cases
                                   bvmod
                                   bvuminus
                                   bvminus
                                   bvplus
                                   bvcat logapp
                                   rem-becomes-mod
                                   )
                                  (SBVREM-REWRITE
                                   bvmod
                                   BVMINUS
                                   BVuMINUS
                                   sbvlt
                                   BVCHOP-UPPER-BOUND ;for speed
                                   ;sbvrem-rewrite
                                   ;BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   mod-sum-cases
                                   ;NOT-EQUAL-CONSTANT-WHEN-BOUND-FORBIDS-IT2 ;add syntaxp hyp?
                                   ;anti-bvplus
;SBVREM-BECOMES-BVMOD
                                   EXPT-HALF-LINEAR
                                   )))))

;simplify the rhs (do we know what sbvrem does in each case?)
(defthm sbvmoddown-rewrite
  (implies (and (posp size)
                (natp x)
                (natp y))
           (equal (sbvmoddown size x y)
                  (if (equal 0 (bvchop size y))
                      (bvchop size x)
                    (if (and (sbvle size 0 x)
                             (sbvle size 0 y))
                        ;;both arguments are non-negative, so we can just call bvmod
                        (bvmod (+ -1 size) x y)
                      (if (and (sbvlt size x 0)
                               (sbvlt size y 0))
                          (sbvrem size x y) ;the quotient is non-negative, so sbvrem rounds the way we want
                        ;;otherwise, to quotient is negative, so sbvrem rounds up, but we want to round down
                        (if (equal 0 (sbvrem size x y))
                            ;;no rounding, so the sbvrem result is right
                            (sbvrem size x y)
                          ;;sbvrem rounded up, and we want to round down
                          (bvplus size Y (sbvrem size x y))))))))
  :otf-flg t
  :hints (("Goal" :cases ((SBVLT SIZE Y 0))
           :in-theory (enable sbvmoddown-rewrite-case-1
                              sbvmoddown-rewrite-case-2
                              sbvmoddown-rewrite-case-3
                              sbvmoddown-rewrite-case-4
                              sbvmoddown-rewrite-case-5
                              sbvlt-rewrite
                              ))))

;gen the 16
(defthm sbvmoddown-of-16
  (implies (and (< 5 size)
                (integerp size))
           (equal (sbvmoddown size x 16)
                  (bvchop 4 x)))
  :hints (("Goal" :in-theory (enable sbvmoddown
                                     mod-of-expt-of-2-constant-version))))
