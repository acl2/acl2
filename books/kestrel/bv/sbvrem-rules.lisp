; Rules about sbvrem
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "sbvrem")
(include-book "bvuminus")
(include-book "sbvlt")
(include-book "sbvlt-rules") ; for sbvlt-rewrite
(include-book "bvcat") ; for BVCHOP-WHEN-TOP-BIT-1
(include-book "slice-rules")
(local (include-book "logapp"))
(local (include-book "logext"))
(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
(local (include-book "kestrel/arithmetic-light/rem" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

(local (in-theory (disable ;bound-from-natp-fact
                           bvchop-upper-bound-linear-strong)))

;TODO: really it's "non-negative"
;See also sbvrem-rewrite.
(defthmd sbvrem-when-positive
  (implies (and (sbvle size 0 x)
                (sbvle size 0 y)
                (posp size))
           (equal (sbvrem size x y)
                  (bvmod (+ -1 size) x y)))
  :hints (("Goal" :in-theory (e/d (sbvrem bvmod SBVLT-REWRITE rem-becomes-mod)
                                  (;LOGEXT-WHEN-NON-NEGATIVE-BECOMES-BVCHOP
                                   )))))

;; (defthm sbvrem-when-positive
;;   (implies (and (sbvle size 0 x)
;;                 (sbvle size 0 y)
;;                 (posp size)
;;                 (integerp x)
;;                 (integerp y)
;;                 )
;;            (equal (sbvrem size x y)
;;                   (if (equal 0 (bvchop (+ -1 size) y))
;;                       (bvchop (+ -1 size) x)
;;                     (bvmod (+ -1 size) x y))))
;;   :hints (("Goal" :in-theory (enable sbvrem bvmod sbvlt ;bvchop
;;                                      ))))

(local (in-theory (disable sbvlt)))
(local (in-theory (enable sbvlt-rewrite)))

;drop?
(defthm bvlt-helper
  (implies (posp size)
           (equal (bvlt (+ -1 size) (+ -1 (expt 2 size)) x)
                  (bvlt (+ -1 size) -1 x)))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm mod-of-minus-of-expt-and-bvchop
  (implies (and (rationalp x)
                (rationalp y))
           (equal (mod x (+ (- (expt 2 size)) (bvchop size y)))
                  (- (mod (- x) (- (expt 2 size) (bvchop size y))))))
  :hints (("Goal" :in-theory (disable mod-of-minus-arg2
                                      mod-of-minus-arg1 ;for speed
                                      )
           :use (:instance mod-of-minus-arg2 (y (- (expt 2 size) (bvchop size y)))))))

(defthmd sbvrem-when-both-negative
  (implies (and (sbvlt size x 0)
                (sbvlt size y 0)
                (posp size))
           (equal (sbvrem size x y)
                  (bvuminus size (bvmod size (bvuminus size x) (bvuminus size y)))))
  :hints (("Goal" :in-theory (e/d (bvuminus bvminus slice-of-sum-cases
                                            sbvrem bvmod sbvlt
                                            logext logapp
                                            bvchop-of-sum-cases
                                            bvchop-when-top-bit-1
                                            rem-becomes-mod
                                            )
                                  (;bvminus-becomes-bvplus-of-bvuminus
                                   )))))

;; (thm
;;  (implies (posp size)
;;           (not (EQUAL (EXPT 2 SIZE)
;;                         (BVCHOP (+ -1 SIZE) X))
;;                  )))

(defthm mod-of-minus-of-expt-and-bvchop-arg1
  (implies (and (rationalp x)
                (rationalp y))
           (equal (mod (+ (- (expt 2 size)) (bvchop size x)) y)
                  (if (equal 0 (mod (+ (expt 2 size) (- (bvchop size x)))
                                    y))
                      0 (- y (mod (+ (expt 2 size) (- (bvchop size x))) y)))
                  ))
  :hints (("Goal" :in-theory (disable mod-of-minus-arg2 ;for speed?
                                      mod-of-minus-arg1
                                      )
           :use (:instance mod-of-minus-arg1 (x (+ (expt 2 size) (- (bvchop size x))))))))

(defthmd sbvrem-when-x-negative
  (implies (and (sbvlt size x 0)
                (sbvle size 0 y)
                (posp size))
           (equal (sbvrem size x y)
                  (bvuminus size (bvmod size (bvuminus size x) y))))
  :hints (("Goal" :in-theory (e/d (bvuminus bvminus
                                            ;;slice-of-sum-cases
                                            sbvrem bvmod sbvlt
                                            logext logapp
                                            ;;bvchop-of-sum-cases
                                            bvchop-when-top-bit-1
                                            bvchop-when-top-bit-not-1
                                            rem-becomes-mod
                                            unsigned-byte-p)
                                  (;bvminus-becomes-bvplus-of-bvuminus
                                   ;mod-type ;led to forcing
                                   )))))

(defthmd sbvrem-when-y-negative
  (implies (and (sbvlt size y 0)
                (sbvle size 0 x)
                (posp size)
                (integerp x)
                (integerp y)
                )
           (equal (sbvrem size x y)
                  (bvmod size x (bvuminus size y))))
  :hints (("Goal" :in-theory (e/d (bvuminus bvminus
                                            ;;slice-of-sum-cases
                                            sbvrem bvmod sbvlt
                                            logext logapp
                                            ;;bvchop-of-sum-cases
                                            bvchop-when-top-bit-1
                                            bvchop-when-top-bit-not-1
                                            equal-of-0-and-mod
                                            rem-becomes-mod)
                                  (;bvminus-becomes-bvplus-of-bvuminus
                                   )))))

(defthm sbvrem-rewrite
  (implies (and (posp size)
                (integerp x)
                (integerp y)
                )
           (equal (sbvrem size x y)
                  (if (sbvle size 0 x)
                      (if (sbvle size 0 y)
                          (bvmod (+ -1 size) x y)
                        (bvmod size x (bvuminus size y)))
                    (if (sbvle size 0 y)
                        (bvuminus size (bvmod size (bvuminus size x) y))
                      (bvuminus size (bvmod size (bvuminus size x) (bvuminus size y)))))))
  :hints (("Goal" :in-theory (enable sbvrem-when-positive
                                     sbvrem-when-y-negative
                                     sbvrem-when-x-negative
                                     sbvrem-when-both-negative))))

;gen
(defthm unsigned-byte-p-8-of-sbvrem
  (implies (and (posp size)
                (equal size 32) ;gen!
                (sbvle size 0 x))
           (unsigned-byte-p 8 (sbvrem size x 256)))
  :hints (("Goal" :cases ((< 8 size))
           :in-theory (enable sbvrem-when-positive))))
