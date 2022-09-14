; Mixed rules
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvchop")
(include-book "slice")
(include-book "bvplus")
(include-book "bvuminus")
(include-book "unsigned-byte-p-forced")
(include-book "bv-syntax") ; for bind-var-to-bv-term-size
(local (include-book "rules")) ;for logtail-of-minus
(local (include-book "bvcat")) ;for bvchop-32-split-hack
(local (include-book "logtail"))
(local (include-book "unsigned-byte-p"))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor2" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/divide" :dir :system))

;drop or move hyps?
;expensive?
(defthm mod-equal-impossible-value
  (implies (and (<= j k) ; unusual
                (natp i)
                (natp j))
           (equal (equal k (mod i j))
                  (if (equal 0 j)
                      (equal k i)
                    nil))))

(defthm floor-of-sum-of-minus-expt-and-bvchop
  (implies (rationalp y)
           (equal (FLOOR (+ (- (EXPT 2 SIZE)) (BVCHOP SIZE X)) y)
                  (if (integerp (* (+ (- (EXPT 2 SIZE)) (BVCHOP SIZE X)) (/ y)))
                      (- (floor (- (+ (- (EXPT 2 SIZE)) (BVCHOP SIZE X))) y))
                    (+ -1 (- (floor (- (+ (- (EXPT 2 SIZE)) (BVCHOP SIZE X))) y))))))
  :hints (("Goal" :use (:instance floor-of---arg1 (j y) (i (- (+ (- (EXPT 2 SIZE)) (BVCHOP SIZE X)))))
           :in-theory (disable floor-of---arg1))))

(defthm floor-of-sum-of-minus-expt-and-bvchop-arg2
  (implies (rationalp x)
           (equal (FLOOR x (+ (- (EXPT 2 SIZE)) (BVCHOP SIZE y)))
                  (IF (INTEGERP (* X (/ (+ (EXPT 2 SIZE) (- (BVCHOP SIZE y))))))
                      (- (FLOOR X (+ (EXPT 2 SIZE) (- (BVCHOP SIZE y)))))
                      (- (- (FLOOR X (+ (EXPT 2 SIZE) (- (BVCHOP SIZE y))))) 1))))
  :hints (("Goal" :use (:instance floor-minus-arg2 (y (- (+ (- (EXPT 2 SIZE)) (BVCHOP SIZE y)))))
           :in-theory (disable floor-minus-arg2))))

(defthm integerp-of-times-of-/-of-expt-and-minus-of-bvchop
  (implies (rationalp x)
           (equal (INTEGERP (* x (/ (+ (EXPT 2 SIZE) (- (BVCHOP SIZE Y))))))
                  (INTEGERP (* x (/ (+ (- (EXPT 2 SIZE)) (BVCHOP SIZE Y)))))))
  :hints (("Goal" :use (:instance INTEGERP-OF--(x (* x (/ (+ (- (EXPT 2 SIZE)) (BVCHOP SIZE Y))))))
           :do-not '(preprocess)
           :in-theory (e/d (--of-*-push-into-arg2 --of-/)
                           (/-of--
                            INTEGERP-OF--
                            ;;FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-right
                            *-OF---ARG2
                            )))))

;move or drop
(defthm slice-31-2-minus-4-alt
  (implies (natp x)
           (equal (slice 31 2 (bvplus 32 4294967292 x))
                  (if (< x 4)
                      1073741823
                    (bvplus 30 -1 (slice 31 2 x)))))
  :hints
  (("Goal" :in-theory (e/d (slice logtail-of-bvchop bvplus)
                           (BVCHOP-OF-LOGTAIL-BECOMES-SLICE
                            ;;anti-slice
                            bvchop-of-logtail
                                       ;BVLT-OF-BVCHOP-ARG2
                                       ;BVLT-OF-BVCHOP-ARG3
                                       )))))

;i think we may need this to split into cases - but maybe delay that?
(defthm bvuminus-when-smaller-bind-free
  (implies (and (bind-free (bind-var-to-bv-term-size 'free x))
                (< free size)
                (natp size)
                (force (unsigned-byte-p-forced free x)))
           (equal (bvuminus size x)
                  (if (equal 0 x)
                      0
                    (bvplus size (- (expt 2 size) (expt 2 free)) (bvuminus free x)))))
  :hints (("Goal" :use (:instance bvuminus-when-smaller)
           :in-theory (e/d (UNSIGNED-BYTE-P-FORCED) ( bvuminus-when-smaller)))))
