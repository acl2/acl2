; Theorems about bvsx
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvsx-def")
(include-book "logext-def")
(local (include-book "logapp"))
(local (include-book "unsigned-byte-p"))
(local (include-book "bvcat"))
(local (include-book "bvchop"))
(local (include-book "slice"))
(local (include-book "repeatbit"))
(local (include-book "repeatbit2"))
(local (include-book "logext"))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))

(defthm integerp-of-bvsx
  (integerp (bvsx a b c)))

(defthm natp-of-bvsx
  (natp (bvsx a b c))
  :hints (("Goal" :in-theory (enable bvsx))))

(defthm bvsx-when-not-natp-arg2
  (implies (not (natp old-size))
           (equal (bvsx new-size old-size x)
                  0))
  :hints (("Goal" :in-theory (enable bvsx))))

(defthm bvchop-of-bvsx-low
  (implies (and (<= n old-size)
                (< 0 old-size)
                (<= old-size new-size)
                (natp n)
                (natp new-size)
                (natp old-size))
           (equal (bvchop n (bvsx new-size old-size val))
                  (bvchop n val)))
  :hints (("Goal" :in-theory (enable bvsx))))

(defthm bvchop-of-bvsx
  (implies (and (< old-size n) ; could allow = but we prefer bvchop-of-bvsx-low in that case
                (<= n new-size)
                (< 0 old-size)
                ;; (<= old-size new-size)
                (natp n)
                (natp new-size)
                (natp old-size))
           (equal (bvchop n (bvsx new-size old-size val))
                  (bvsx n old-size val)))
  :hints (("Goal" :in-theory (enable bvsx))))


;gen to any bv
(defthm <-of-bvsx-and-0
  (not (< (bvsx new-size old-size val) 0))
  :hints (("Goal" :in-theory (enable bvsx))))

;drop?
(defthm bvsx-of-bvchop
  (implies (and ;(posp old-size)
                (natp new-size))
           (equal (bvsx new-size old-size (bvchop old-size x))
                  (bvsx new-size old-size x)))
  :hints (("Goal" :in-theory (enable bvsx))))

(defthm bvsx-of-bvchop-gen
  (implies (and (<= old-size size)
                (integerp size)
                (natp new-size))
           (equal (bvsx new-size old-size (bvchop size x))
                  (bvsx new-size old-size x)))
  :hints (("Goal" :in-theory (enable bvsx))))

(defthm bvsx-of-logext
  (implies (and (<= old-size size)
                (integerp size))
           (equal (bvsx new-size old-size (logext size x))
                  (bvsx new-size old-size x)))
  :hints (("Goal" :in-theory (enable bvsx))))

;; May be expensive
(defthm bvsx-when-unsigned-byte-p
  (implies (and (unsigned-byte-p (+ -1 old-size) x)
                (<= old-size new-size)
                (integerp new-size))
           (equal (bvsx new-size old-size x)
                  x))
  :hints (("Goal" :in-theory (enable bvsx))))

;; May be expensive?
(defthm bvsx-when-equal-of-getbit-and-0
  (implies (and (equal (getbit (+ -1 old-size) x) 0)
                (<= old-size new-size)
                (integerp new-size)
                (posp old-size))
           (equal (bvsx new-size old-size x)
                  ;; or could chop down to old-size - 1, but we leave that
                  ;; to a separate rule (for now)
                  (bvchop old-size x)))
  :hints (("Goal" :in-theory (enable bvsx))))

;gen
;rename to bvsx-alt-def
(defthmd bvsx-rewrite
  (implies (and (<= n m)
                (posp n)
                (natp m))
           (equal (bvsx m n x)
                  (bvchop m (logext n x))))
  :hints (("Goal"  :in-theory (e/d (bvsx logext
                                         ;posp
                                         ;repeatbit ;bvplus
                                         slice-alt-def         ;slice
                                         getbit
                                         ;; EXPONENTS-ADD-FOR-NONNEG-EXPONENTS
                                         )
                                   (; BVPLUS-OF-*-ARG2
                                    ;;BVCAT-OF-+-HIGH ;looped



                                    ))
           :cases ((equal (GETBIT (+ -1 n) X) 0) (equal (GETBIT (+ -1 n) X) 1)))))

(defthm unsigned-byte-p-of-bvsx-simple
  (equal (unsigned-byte-p size (bvsx size m x))
         (natp size))
  :hints (("Goal" :cases ((posp m))
           :in-theory (enable bvsx))))

(defthm unsigned-byte-p-of-bvsx
  (implies (and (<= size2 size)
                (integerp size)
                (natp size2))
           (unsigned-byte-p size (bvsx size2 m x)))
  :hints (("Goal" :cases ((posp m))
                      :in-theory (enable bvsx))))

(defthm getbit-of-repeatbit
  (implies (and (< n size)
                (unsigned-byte-p 1 bit) ;drop
                (natp n)
                (natp size))
           (equal (getbit n (repeatbit size bit))
                  bit))
  :hints (("Goal" :in-theory (e/d (repeatbit getbit slice
                                             expt-diff-collect)
                                  (BVCHOP-CHOP-LEADING-CONSTANT)))))

(defthm getbit-of-bvsx
  (implies (and (<= old-size new-size)
                (natp n)
                (natp new-size)
                (posp old-size))
           (equal (getbit n (bvsx new-size old-size val))
                  (if (< n old-size)
                      (getbit n val)
                    (if (< n new-size)
                        (getbit (+ -1 old-size) val)
                      0))))
  :hints (("Goal" :in-theory (enable bvsx))))

;rename
(defthm bvsx-of-0
  (equal (bvsx new-size old-size 0)
         0)
  :hints (("Goal" :in-theory (enable bvsx bvcat))))

(defthm bvsx-of-0-arg1
  (equal (bvsx 0 old-size val)
         0)
  :hints (("Goal" :in-theory (enable bvsx bvcat))))

(defthm bvsx-when-sizes-match
  (implies (and (equal new-size old-size)
                (natp new-size)
                (< 0 new-size))
           (equal (bvsx new-size old-size val)
                  (bvchop new-size val)))
  :hints (("Goal" :in-theory (enable repeatbit bvsx))))

(defthmd bvsx-alt-def-2
  (implies (and; (integerp val)
                (posp old-size)
                (<= old-size new-size)
                (integerp new-size))
           (equal (bvsx new-size old-size val)
                  (if (equal 0 (getbit (+ -1 old-size) val))
                      (bvchop (+ -1 old-size) val)
                    (bvcat (- new-size old-size)
                           (+ -1 (expt 2 (- new-size old-size)))
                           old-size
                           val))))
  :hints (("Goal" :in-theory (e/d (bvsx) (EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT)))))

(defthmd equal-of-bvsx-and-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep new-size)
                              (quotep old-size)))
                (<= old-size new-size)
                (natp new-size)
                (posp old-size))
           (equal (equal k (bvsx new-size old-size x))
                  (and (unsigned-byte-p new-size k)
                       (if (equal (slice (+ -1 new-size) (+ -1 old-size) k) 0) ; gets computed
                           (equal k (bvchop old-size x))
                         (if (equal (slice (+ -1 new-size) (+ -1 old-size) k) (+ -1 (expt 2 (+ 1 (- new-size old-size))))) ; gets computed
                             (equal (bvchop old-size k) (bvchop old-size x))
                           nil)))))
  :hints (("Goal"
           :in-theory (e/d (bvsx-alt-def-2
                            unsigned-byte-p-of-bvchop-one-more
                            getbit-when-slice-is-known-to-be-all-ones
                            slice-low-cases)
                           ( ;GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT
                            ;;EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT
                            ;;BVCAT-EQUAL-REWRITE-ALT
                            ;;BVCAT-EQUAL-REWRITE
                            )))))

(defthm equal-of-bvsx-and-bvsx
  (implies (and (< lowsize n)
                (posp lowsize)
                (integerp n))
           (equal (equal (bvsx n lowsize x) (bvsx n lowsize y))
                  (equal (bvchop lowsize x)
                         (bvchop lowsize y))))
  :hints (("Goal" :in-theory (enable bvsx))))

(defthm bvsx-same
  (equal (bvsx new-size new-size x)
         (bvchop new-size x))
  :hints (("Goal" :in-theory (enable bvsx))))

(defthm bvsx-too-high
  (implies (and (unsigned-byte-p (+ -1 old-size) x)
                (<= old-size new-size))
           (equal (bvsx new-size old-size x)
                  x))
  :hints (("Goal" :in-theory (enable natp bvsx getbit-too-high))))

(defthm bvsx-of-bvsx
  (implies (and (<= old-size new-size)
                (<= new-size big-size)
                (posp old-size) ;must have at least 1 bit to sign-extend..
                (integerp new-size)
                (integerp big-size))
           (equal (bvsx big-size new-size (bvsx new-size old-size x))
                  (bvsx big-size old-size x)))
  :hints (("Goal" :in-theory (enable bvsx))))

(defthm unsigned-byte-p-of-bvsx-alt
  (implies (and (< size new-size) ;this case
                (<= old-size size) ;this case
                (natp size)
                (natp new-size)
                (posp old-size))
           (equal (unsigned-byte-p size (bvsx new-size old-size x))
                  (equal 0 (getbit (+ -1 old-size) x))))
  :hints (("Goal" :in-theory (e/d (bvsx) (REPEATBIT-OF-1-ARG2)))))

(defthm equal-of-0-and-bvsx
  (implies (and (natp size)
                (posp old-size)
                (<= old-size size))
           (equal (equal 0 (bvsx size old-size x))
                  (equal 0 (bvchop old-size x))))
  :hints (("Goal" :in-theory (enable bvsx getbit-when-equal-of-constant-and-bvchop))))

;gen
(defthm bvcat-of-if-becomes-bvsx-64-64
  (equal (bvcat 64 (if (equal 1 (getbit 63 x)) 18446744073709551615 0) 64 x)
         (bvsx 128 64 x))
  :hints (("Goal" :in-theory (enable
                              bvsx ;todo
                              ))))

;rename
(defthm high-slice-of-logext
  (implies (and (<= (+ -1 n) low)
                (posp n)
                (natp low)
                (integerp high))
           (equal (slice high low (logext n x))
                  (bvsx (+ 1 high (- low))
                        1
                        (getbit (+ -1 n) x))))
  :hints (("Goal" :in-theory (e/d (slice logext repeatbit bvsx) (BVCHOP-OF-LOGTAIL)))))

(defthm bvchop-of-logext-becomes-bvsx
  (implies (and (< size2 size)
                (natp size)
                (posp size2))
           (equal (bvchop size (logext size2 x))
                  (bvsx size size2 x)))
  :hints (("Goal" :in-theory (e/d (bvsx logtail-of-bvchop-becomes-slice) (logext)))))

;add -becomes-bvsx to name
(defthm slice-of-logext-middle
  (implies (and (< low n)
                (<= n high)
                (posp n)
                (natp low)
                (integerp high))
           (equal (slice high low (logext n x))
                  (bvsx (+ 1 high (- low))
                        (- n low)
                        (slice (+ -1 n) low x))))
  :hints (("Goal" :in-theory (e/d (slice logext repeatbit bvsx LOGTAIL-OF-BVCHOP)
                                  (BVCHOP-OF-LOGTAIL)))))

;add -becomes-bvsx to name
(defthm slice-of-logext-gen
  (implies (and (posp n)
                (natp low)
                (integerp high))
           (equal (slice high low (logext n x))
                  (if (< high n)
                      (slice high low x)
                    (if (< low n)
                        (bvsx (+ 1 high (- low))
                              (- n low)
                              (slice (+ -1 n) low x))
                      (bvsx (+ 1 high (- low))
                            1
                            (getbit (+ -1 n) x)))))))
