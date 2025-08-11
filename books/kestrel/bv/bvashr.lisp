; Arithmetic (sign-preserving) right shift
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvashr-def")
(local (include-book "bvsx"))
(local (include-book "bvshr"))
(local (include-book "bvcat"))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "repeatbit2"))

(defthm integerp-of-bvashr
  (integerp (bvashr width x shift-amount)))

(defthm natp-of-bvashr
  (natp (bvashr width x shift-amount)))

;; See also bvchop-of-bvashr-both below.
(defthm bvchop-of-bvashr
  (implies (and (<= (+ n shift-amount) width)
                (natp shift-amount)
                (natp width)
                (natp n))
           (equal (bvchop n (bvashr width x shift-amount))
                  (slice (+ -1 n shift-amount)
                         shift-amount
                         x)))
  :hints (("Goal" :in-theory (enable bvashr bvsx))))

;; Avoids creating the call to slice if the indices won't be constants
;; TODO: Make a safe version of bvchop-of-bvashr-both?
(defthm bvchop-of-bvashr-safe
  (implies (and (syntaxp (and (quotep shift-amount)
                              (quotep n)))
                (<= (+ n shift-amount) width)
                (natp shift-amount)
                (natp width)
                (natp n))
           (equal (bvchop n (bvashr width x shift-amount))
                  (slice (+ -1 n shift-amount)
                         shift-amount
                         x))))

;todo: get rid of bvchop-of-bvashr?
(defthm bvchop-of-bvashr-both
  (implies (and (integerp width)
                (<= shift-amount width)
                (natp shift-amount)
                (<= n width) ;gen?
                )
           (equal (bvchop n (bvashr width x shift-amount))
                  (if (natp n)
                      (if (<= n (- width shift-amount))
                          (slice (+ -1 n shift-amount) shift-amount x)
                        (bvsx n
                              (+ width (- shift-amount))
                              (slice (+ -1 width) shift-amount x)))
                    0)))
  :hints (("Goal" :in-theory (enable bvashr
                                     bvshr
                                     BVSX ;todo: instead prove bvchop of bvsx
                                     posp
                                     ))))

(defthmd bvashr-rewrite-for-constant-shift-amount
  (implies (and (syntaxp (quotep shift-amount))
                (syntaxp (quotep width)) ; will usually be true
                )
           (equal (bvashr width x shift-amount)
                  (bvsx width (- width shift-amount)
                        (bvshr width x shift-amount))))
  :hints (("Goal" :in-theory (enable bvashr))))

(defthm bvashr-of-0-arg1
  (equal (bvashr 0 x shift-amount)
         0)
  :hints (("Goal" :in-theory (enable bvashr))))

(defthm bvashr-of-0-arg2
  (equal (bvashr width 0 shift-amount)
         0)
  :hints (("Goal" :in-theory (enable bvashr))))

(defthm bvashr-of-0-arg3
  (implies (integerp width)
           (equal (bvashr width x 0)
                  (bvchop width x)))
  :hints (("Goal" :in-theory (enable bvashr))))

(defthm unsigned-byte-p-of-bvashr
  (equal (unsigned-byte-p size (bvashr size x amt))
         (natp size))
  :hints (("Goal" :in-theory (enable bvashr bvshr))))

(defthm unsigned-byte-p-of-bvashr-gen
  (implies (and (<= size size2)
                (integerp size2)
                (natp size))
           (unsigned-byte-p size2 (bvashr size x amt)))
  :hints (("Goal" :in-theory (enable bvashr bvshr))))

(defthm bvashr-of-bvchop
  (equal (bvashr width (bvchop width x) shift-amount)
         (bvashr width x shift-amount))
  :hints (("Goal" :cases ((equal 0 width))
           :in-theory (enable bvashr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvashr-cases-term-fn-aux (i width)
  (declare (xargs :guard (integerp width)
                  :measure (nfix (+ 1 i))))
  (if (not (posp i))
      `((otherwise (bvashr ,width x 0))) ; covers 0 and all other cases: ensures that a number is always returned
    (cons `(,i (bvashr ,width x ,i))
          (bvashr-cases-term-fn-aux (+ -1 i) width))))

(defund bvashr-cases-term-fn (width)
  (declare (xargs :guard (natp width)))
  `(case shift-amount
     ,@(bvashr-cases-term-fn-aux width width)))

(defmacro bvashr-cases-term (width)
  (bvashr-cases-term-fn width))

;pretty gross
(defthmd bvashr-16-cases
  (implies (and (syntaxp (not (quotep shift-amount)))
                (natp shift-amount)
                (<= shift-amount 16))
           (equal (bvashr 16 x shift-amount)
                  (bvashr-cases-term 16)))
  :hints (("Goal" :in-theory (enable bvashr))))

;pretty gross
(defthmd bvashr-32-cases
  (implies (and (syntaxp (not (quotep shift-amount)))
                (natp shift-amount)
                (<= shift-amount 32))
           (equal (bvashr 32 x shift-amount)
                  (bvashr-cases-term 32)))
  :hints (("Goal" :in-theory (enable bvashr))))

;pretty gross
(defthmd bvashr-64-cases
  (implies (and (syntaxp (not (quotep shift-amount)))
                (natp shift-amount)
                (<= shift-amount 64))
           (equal (bvashr 64 x shift-amount)
                  (bvashr-cases-term 64)))
  :hints (("Goal" :in-theory (enable bvashr))))

;; bvshr seems simpler
(defthm getbit-of-bvashr-becomes-getbit-of-bvshr
  (implies (and (< n (- width amt))
                (natp n)
                (natp width)
                (natp amt))
           (equal (getbit n (bvashr width x amt))
                  (getbit n (bvshr width x amt))))
  :hints (("Goal" :in-theory (enable bvashr bvshr))))
