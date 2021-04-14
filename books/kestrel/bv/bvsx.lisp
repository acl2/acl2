; Theorems about bvsx
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvsx-def")
(include-book "ihs/basic-definitions" :dir :system) ;for logext
;(local (include-book "arith")) ;for expt-diff-collect
(local (include-book "unsigned-byte-p"))
(local (include-book "bvcat"))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))

(defthm integerp-of-bvsx
  (integerp (bvsx a b c)))

(defthm natp-of-bvsx
  (natp (bvsx a b c))
  :hints (("Goal" :in-theory (enable bvsx))))

(defthm bvchop-of-bvsx2
  (implies (and (< n old-size)
                (< 0 old-size)
                (<= old-size new-size)
                (natp n)
                (natp new-size)
                (natp old-size))
           (equal (bvchop n (bvsx new-size old-size val))
                  (bvchop n val)))
  :hints (("Goal" :in-theory (enable bvsx))))

;gen to any bv
(defthm <-of-bvsx-and-0
  (not (< (bvsx new-size old-size val) 0))
  :hints (("Goal" :in-theory (enable bvsx))))

(defthm bvsx-of-bvchop
  (implies (and (posp old-size)
                (natp new-size))
           (equal (bvsx new-size old-size (bvchop old-size x))
                  (bvsx new-size old-size x)))
  :hints (("Goal" :in-theory (enable bvsx))))

;; May be expensive
(defthm bvsx-when-unsigned-byte-p
  (implies (and (unsigned-byte-p (+ -1 old-size) x)
                (<= old-size new-size)
                (integerp new-size)
                (integerp old-size))
           (equal (bvsx new-size old-size x)
                  x))
  :hints (("Goal" :in-theory (enable bvsx))))

;gen
(defthmd bvsx-rewrite
  (implies (and (posp n)
;                (equal n 8)
                (natp m)
                (<= n m))
           (equal (bvsx m n x)
                  (bvchop m (logext n x))))
  :hints (("Goal"  :in-theory (e/d (bvsx logext posp repeatbit ;bvplus
                                         slice
;                                         EXPONENTS-ADD-FOR-NONNEG-EXPONENTS
                                         )
                                   (;|+-BECOMES-BVPLUS-HACK| BVPLUS-OF-*-ARG2 ;anti-bvplus
                                    ;BVCAT-OF-+-HIGH ;looped
                                    BVCHOP-OF-LOGTAIL-BECOMES-SLICE
 ;                                   EXPONENTS-ADD
;                                  EXPONENTS-ADD-FOR-NONNEG-EXPONENTS
                                    expt
                                    ))
           :cases ((equal (GETBIT (+ -1 n) X) 0) (equal (GETBIT (+ -1 n) X) 1)))))

(defthm unsigned-byte-p-of-bvsx-simple
  (implies (natp size)
           (unsigned-byte-p size (bvsx size m x)))
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
                                  (BVCHOP-CHOP-LEADING-CONSTANT
                                    BVCHOP-1-BECOMES-GETBIT SLICE-BECOMES-GETBIT BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

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

(defthm bvsx-of-0
  (equal (bvsx new-size old-size 0)
         0)
  :hints (("Goal" :in-theory (e/d (bvsx bvcat)
                                  ()))))
