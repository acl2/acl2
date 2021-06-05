; Rules about sbvdiv
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

(include-book "sbvdiv")
(include-book "bvdiv")
(include-book "bvuminus")
(include-book "sbvlt") ;for sbvle
(include-book "bitnot")
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/divides" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "bvcat"))
(local (include-book "slice-rules"))
(local (include-book "getbit-rules"))
(local (include-book "bvminus-rules"))

;dup in bv/arith
(DEFTHM PLUS-OF-MINUS-AND-TIMES-TWO
  (EQUAL (+ (- X) (* 2 X) Y) (+ X Y)))

;move
(defthm bvuminus-of-1
  (equal (bvuminus 1 x)
         (bvchop 1 x))
  :hints (("Goal" :in-theory (enable bvuminus
                                     bvminus
                                     ))))

(defthm slice-of-bvuminus
  (implies (and (< high size)
                (<= low high)
                (integerp x)
                (integerp size)
                (natp low)
                (natp high))
           (equal (slice high low (bvuminus size x))
                  (if (equal (bvchop low x) 0)
                      (bvuminus (+ 1 high (- low)) (slice high low x))
                    (bvminus (+ 1 high (- low)) (+ -1 (expt 2 (+ 1 high (- low)))) (slice high low x)))))
  :hints (("Goal" :in-theory (e/d (bvuminus bvminus slice-of-sum-cases
                                            bvchop-of-sum-cases
                                            ) (;bvchop-of-*
;BVMULT-OF-2-GEN ;why?
;EQUAL-OF-BVMULT-AND-*-ALT
;EQUAL-OF-BVMULT-AND-*
;bvminus-becomes-bvplus-of-bvuminus
                                               )))))

(defthm getbit-of-bvuminus
  (implies (and (< low size)
                (integerp x)
                (integerp size)
                (natp low))
           (equal (getbit low (bvuminus size x))
                  (if (equal (bvchop low x) 0)
                      (getbit low x)
                    (bitnot (getbit low x)))))
  :hints (("Goal" :use (:instance slice-of-bvuminus (high low))
           :in-theory (disable slice-of-bvuminus))))

(defthm equal-of-bvchop-and-bvchop-same-diff-sizes
  (implies (natp size)
           (equal (equal (bvchop size x) (bvchop (+ -1 size) x))
                  (if (equal size 0)
                      t
                    (equal 0 (getbit (+ -1 size) x)))))
  :hints (("Goal" :cases ((equal 0 size))
           :use (:instance split-bv (y (bvchop size x))
                                  (m (+ -1 size))
                                  (n size)))))

(defthm bound-hack-quotient
  (implies (and (rationalp x)
                (< 0 x)
                (posp k))
           (<= (* x (/ k)) x)))

;(in-theory (disable (:rewrite mod-x-y-=-x . 2)))

;could loop?
(defthmd logext-becomes-bvchop-when-positive
  (implies (<= 0 (logext 32 x))
           (equal (logext 32 x)
                  (bvchop 31 x)))
  :hints (("Goal" :in-theory (enable logext))))

;;(bvuminus 32 (bvdiv 31 (bvuminus 31 x) y))

;could loop?
(defthmd logext-when-positive-gen
  (implies (<= 0 (logext size x))
           (equal (logext size x)
                  (bvchop (+ -1 size) x)))
  :hints (("Goal" :in-theory (enable logext logapp))))

(defthmd sbvdiv-when-both-positive
  (implies (and (integerp x)
                (integerp y)
                (sbvle size 0 x)
                (sbvle size 0 y)
                (natp size)
                )
           (equal (sbvdiv size x y)
                  (bvdiv (+ -1 size) x y)))
  :hints (("Goal"
           :use ((:instance my-FLOOR-upper-BOUND (i (BVCHOP (+ -1 size) X)) (j (BVCHOP (+ -1 size) y)))
                 (:instance SLICE-TOO-HIGH-IS-0 (high (+ -1 size)) (low (+ -1 size)) (x (FLOOR (BVCHOP (+ -1 size) X) (BVCHOP (+ -1 size) Y))))
                 (:instance bound-hack-quotient (x (BVCHOP (+ -1 size) X)) (k (BVCHOP (+ -1 size) Y)))
                 )
           :expand (:with UNSIGNED-BYTE-P (UNSIGNED-BYTE-P (+ -1 size) (FLOOR (BVCHOP (+ -1 size) x) (BVCHOP (+ -1 size) Y))))
           :in-theory (e/d (sbvdiv bvdiv ;bvchop logext logapp getbit slice logtail
                                   FLOOR-OF-SUM
                                   logext-when-positive-gen
                                   ;;bvuminus
                                   sbvlt
                                   bvchop-identity
                                   truncate-becomes-floor
                                   ) ( ;UNSIGNED-BYTE-P-RESOLVER
                                   ;<-Y-*-Y-X
                                   ;MOD-BOUNDED-BY-MODULUS
                                   my-FLOOR-upper-BOUND
                                   ;BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   floor-bound
                                   ;anti-slice
                                   ;MOD-TYPE ;does this overlap with mod-bounded-by-modulus?
                                   )))))

(defthmd sbvdiv-when-both-negative
  (implies (and (integerp x)
                (integerp y)
                (sbvlt size x 0)
                (sbvlt size y 0)
                (posp size)
                )
           (equal (sbvdiv size x y)
                  (bvdiv size (bvuminus size x) (bvuminus size y))))
  :hints (("Goal"
           :expand ((BVCAT 1 1 (+ -1 size) X)
                    (BVCAT 1 1 (+ -1 size) y)
                    (:with logext (LOGEXT size X))
                    (:with logext (LOGEXT size y)))
           :use (:instance floor-of-minus-and-minus
                           (x (+ (expt 2 (+ -1 size)) (- (BVCHOP (+ -1 size) X))))
                           (y (+ (expt 2 (+ -1 size)) (- (BVCHOP (+ -1 size) y)))))
           :in-theory (e/d (sbvdiv bvdiv logapp bvuminus bvminus sbvlt
                                   bvchop-reduce-when-top-bit-known
                                   truncate-becomes-floor-gen)
                           ( floor-of-minus-and-minus
                             ;floor-minus
                             ;PLUS-BVCAT-WITH-0
                             ;bvplus-recollapse
                             ;BVCAT-OF-+-LOW
                             BVCAT-OF-GETBIT-AND-X-ADJACENT
                             ;<-Y-*-Y-X
                             my-FLOOR-upper-BOUND
                             ;BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                             floor-bound)))))

(DEFTHMd BVCHOP-OF-MINUS-lemma
  (EQUAL (BVCHOP SIZE (+ (- x) y))
         (IF (OR (NOT (NATP SIZE))
                 (EQUAL 0 (BVCHOP SIZE (+ x (- y)))))
             0
             (- (EXPT 2 SIZE)
                (BVCHOP SIZE (+ x (- y))))))
  :hints (("Goal" :use (:instance BVCHOP-OF-MINUS
                                  (x (+ x (- y))))
           :in-theory (disable BVCHOP-OF-MINUS))))

(DEFTHM FLOOR-MINUS-ARG1-lemma
  (IMPLIES (AND (RATIONALP X1)
                (RATIONALP X2)
                (RATIONALP Y))
           (EQUAL (FLOOR (+ (- x1) X2) Y)
                  (IF (INTEGERP (* (+ x1 (- x2)) (/ Y)))
                      (- (FLOOR (+ x1 (- x2)) Y))
                      (- (- (FLOOR (+ x1 (- x2)) Y)) 1))))
  :hints (("Goal" :use (:instance floor-minus-arg1
                                  (x (+ x1 (- x2)))))))

(DEFTHM FLOOR-MINUS-ARG2-lemma
  (IMPLIES (AND (FORCE (RATIONALP X))
                (RATIONALP Y1)
                (RATIONALP Y2)
                (NOT (EQUAL '0 (+ Y1 y2))))
           (EQUAL (FLOOR X (+ (- y1) Y2))
                  (IF (INTEGERP (* X (/ (- y1 y2))))
                      (- (FLOOR X (- y1 y2)))
                      (- (- (FLOOR X (- y1 y2))) 1))))
  :hints (("Goal" :use (:instance floor-minus-arg2
                                  (y (+ y1 (- y2)))))))

(defthm /-of-+-of---arg1
  (equal (/ x (+ (- y1) y2))
         (- (/ x (+ y1 (- y2)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (--of-*-push-into-arg2
                            --of-/)
                           (*-of---arg2
                            /-of--)))))

(defthmd sbvdiv-when-x-negative
  (implies (and (integerp x)
                (integerp y)
                (sbvlt size x 0)
                (sbvle size 0 y)
                (posp size))
           (equal (sbvdiv size x y)
                  (bvuminus size (bvdiv size (bvuminus size x) y))))
  :hints (("Goal" :expand ((BVCAT 1 1 (+ -1 size) X)
                           (BVCAT 1 1 (+ -1 size) y)
                           (:with logext (LOGEXT size X))
                           (:with logext (LOGEXT size y)))
           :in-theory (e/d (BVCHOP-OF-MINUS-lemma
                            sbvdiv
                            bvdiv logapp bvuminus bvminus sbvlt BVCHOP-OF-SUM-CASES
                            FLOOR-MINUS-ARG1
                            bvchop-reduce-when-top-bit-known
                            truncate-becomes-floor-other FLOOR-WHEN-INTEGERP-OF-QUOTIENT
                            FLOOR-MINUS-ARG1-lemma)
                           (BVCHOP-UPPER-BOUND
                            floor-of-minus-and-minus
                            BVCAT-OF-GETBIT-AND-X-ADJACENT
                            floor-bound)))))

(defthmd sbvdiv-when-y-negative
  (implies (and (integerp x)
                (integerp y)
                (sbvlt size y 0)
                (sbvle size 0 x)
                (posp size)
                )
           (equal (sbvdiv size x y)
                  (bvuminus size (bvdiv size x (bvuminus size y)))))
  :hints (("Goal" :expand ((BVCAT 1 1 (+ -1 size) X)
                           (BVCAT 1 1 (+ -1 size) y)
                           (:with logext (LOGEXT size X))
                           (:with logext (LOGEXT size y)))
           :in-theory (e/d (sbvdiv bvdiv logapp bvuminus bvminus sbvlt BVCHOP-OF-SUM-CASES
                                   bvchop-reduce-when-top-bit-known
                                   truncate-becomes-floor-other
                                   FLOOR-MINUS-ARG2-lemma)
                           ( floor-of-minus-and-minus
                             FLOOR-MINUS-ARG1
                             BVCAT-OF-GETBIT-AND-X-ADJACENT
                             my-FLOOR-upper-BOUND
                             floor-bound)))))

;can we tighten any of the sizes?
(defthm sbvdiv-rewrite
  (implies (and (integerp x)
                (integerp y)
                (posp size))
           (equal (sbvdiv size x y)
                  (if (sbvle size 0 x)
                      (if (sbvle size 0 y)
                          (bvdiv (+ -1 size) x y)
                        (bvuminus size (bvdiv size x (bvuminus size y))))
                    (if (sbvle size 0 y)
                        (bvuminus size (bvdiv size (bvuminus size x) y))
                      (bvdiv size (bvuminus size x)
                             (bvuminus size y))))))
  :hints (("Goal" :in-theory (enable sbvdiv-when-y-negative
                                     sbvdiv-when-x-negative
                                     sbvdiv-when-both-negative
                                     sbvdiv-when-both-positive))))

;gen!
(defthmd sbvdiv-of-sbvdiv-arg2
  (implies (and (natp size)
                (natp x)
                (unsigned-byte-p (+ -1 size) x)  ; x is non-negative (gen?) ;todo: drop
                (unsigned-byte-p (+ -1 size) y1) ; y1 is non-negative (gen?)
                (unsigned-byte-p (+ -1 size) y2) ; y2 is non-negative (gen?)
                )
           (equal (sbvdiv size (sbvdiv size x y1) y2)
                  (if (unsigned-byte-p (+ -1 size) (* y1 y2)) ; the product is non-negative
                      (sbvdiv size
                              x
                              (* y1 y2) ;(bvchop size (* y1 y2))
                              )
                    ;; divisor is so big we get 0:
                    0)))
  :otf-flg t
  :hints (("Goal" :cases ((equal y1 0))
           :in-theory (e/d (;SBVDIV-WHEN-BOTH-POSITIVE
                            sbvlt
                            bvdiv
                            unsigned-byte-p
                            ;bvuminus
                            bvminus
                            floor-of-sum
                            floor-minus-arg1
                            bvchop-of-sum-cases
                            )
                           ( ;BVCHOP-IDENTITY
                            ;;todo: clean these up:
                            BVCHOP-TIMES-CANCEL-BETTER-ALT
                            BVCHOP-TIMES-CANCEL-BETTER
                            BVCHOP-OF-*-OF-BVCHOP-ARG2
                            BVCHOP-OF-*-OF-BVCHOP
                            ;;slow:
                            USB-PLUS-FROM-BOUNDS
                            getbit-of-0-when-bitp
                            )))))

;gen!
(defthm sbvdiv-of-sbvdiv-arg2-combine-constants
  (implies (and (syntaxp (and (quotep size)
                              (quotep y1)
                              (quotep y2)))
                (unsigned-byte-p (+ -1 size) x) ;todo: drop
                ;; all get computed:
                (natp size)
                (unsigned-byte-p (+ -1 size) y1)
                (unsigned-byte-p (+ -1 size) y2))
           (equal (sbvdiv size (sbvdiv size x y1) y2)
                  (if (unsigned-byte-p (+ -1 size) (* y1 y2)) ;gets computed
                      (sbvdiv size
                              x
                              (* y1 y2) ;(bvchop size (* y1 y2))
                              )
                    0)))
  :hints (("Goal" :in-theory (e/d (sbvdiv-of-sbvdiv-arg2) (sbvdiv-rewrite)))))
