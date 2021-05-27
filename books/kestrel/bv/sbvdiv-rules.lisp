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
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/divides" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "bvcat"))

;dup in bv/arith
(DEFTHM PLUS-OF-MINUS-AND-TIMES-TWO
  (EQUAL (+ (- X) (* 2 X) Y) (+ X Y)))

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

;gen!
(defthmd sbvdiv-of-sbvdiv-arg2
  (implies (and (natp size)
                (unsigned-byte-p (+ -1 size) x) ; x is positive (gen?)
                (unsigned-byte-p (+ -1 size) y1) ; y1 is positive (gen?)
                (unsigned-byte-p (+ -1 size) y2) ; y2 is positive (gen?)
                (unsigned-byte-p (+ -1 size) (* y1 y2)) ; the product is positive (gen?)
                )
           (equal (sbvdiv size (sbvdiv size x y1) y2)
                  (sbvdiv size
                         x
                         (* y1 y2) ;(bvchop size (* y1 y2))
                         )))
  :hints (("Goal" :in-theory (e/d (sbvdiv) ( ;BVCHOP-IDENTITY
                                           ;;todo: clean these up:
                                           BVCHOP-TIMES-CANCEL-BETTER-ALT
                                           BVCHOP-TIMES-CANCEL-BETTER
                                           BVCHOP-OF-*-OF-BVCHOP-ARG2
                                           BVCHOP-TIMES-CANCEL
                                           BVCHOP-N-TIMES-DROP
                                           BVCHOP-OF-*-OF-BVCHOP
                                           )))))

;gen!
(defthm sbvdiv-of-sbvdiv-arg2-combine-constants
  (implies (and (syntaxp (and (quotep size)
                              (quotep y1)
                              (quotep y2)))
                (unsigned-byte-p (+ -1 size) x)
                ;; all get computed:
                (natp size)
                (unsigned-byte-p (+ -1 size) y1)
                (unsigned-byte-p (+ -1 size) y2)
                (unsigned-byte-p (+ -1 size) (* y1 y2)))
           (equal (sbvdiv size (sbvdiv size x y1) y2)
                  (sbvdiv size
                          x
                          (* y1 y2) ;(bvchop size (* y1 y2))
                          )))
  :hints (("Goal" :in-theory (enable sbvdiv-of-sbvdiv-arg2))))
