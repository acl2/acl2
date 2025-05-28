; Bit-vector Right shift
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvshr-def")
(local (include-book "slice"))
(local (include-book "unsigned-byte-p"))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

(defthm integerp-of-bvshr
  (integerp (bvshr width x shift-amount)))

(defthm natp-of-bvshr
  (natp (bvshr width x shift-amount))
  :rule-classes (:rewrite :type-prescription))

(defthm bvshr-of-0-arg1
  (implies (natp amt) ;drop?
           (equal (bvshr 0 x amt)
                  0))
  :hints (("Goal" :in-theory (enable bvshr))))

(defthm bvshr-of-0-arg2
  (equal (bvshr size 0 amt)
         0)
  :hints (("Goal" :in-theory (enable bvshr))))

(defthm bvshr-of-0-arg3
  (implies (integerp width)
           (equal (bvshr width x 0)
                  (bvchop width x)))
  :hints (("Goal" :in-theory (enable bvshr))))

(defthm unsigned-byte-p-of-bvshr
  (implies (natp size)
           (unsigned-byte-p size (bvshr size x amt)))
  :hints (("Goal"
           :in-theory (enable bvshr
                              slice-when-low-is-not-an-integer))))

(defthm unsigned-byte-p-of-bvshr-gen
  (implies (and (<= size size2)
                (natp size2)
                ;(integerp size)
                )
           (unsigned-byte-p size2 (bvshr size x amt)))
  :hints (("Goal" :in-theory (enable bvshr))))

(defthm bvshr-upper-bound-linear-strong
  (implies (natp size)
           (<= (bvshr size x amt) (+ -1 (expt 2 size))))
  :rule-classes :linear
  :hints (("Goal" :use unsigned-byte-p-of-bvshr
           :in-theory (e/d (unsigned-byte-p)
                           (unsigned-byte-p-of-bvshr
                            unsigned-byte-p-of-bvshr-gen)))))

(defthm bvchop-of-bvshr-same
  (implies (and (natp width)
                (natp shift-amount))
           (equal (bvchop width (bvshr width x shift-amount))
                  (bvshr width x shift-amount)))
  :hints (("Goal" :in-theory (enable bvshr))))

(defthm bvchop-of-bvshr-becomes-slice
  (implies (and (natp width)
                (natp shift-amount)
                )
           (equal (bvchop n (bvshr width x shift-amount))
                  (if (natp n)
                      (if (<= n (- width shift-amount))
                          (slice (+ -1 n shift-amount) shift-amount x)
                          (slice (+ -1 width) shift-amount x))
                    0)))
  :hints (("Goal" :in-theory (enable bvshr))))

(defthm bvchop-of-bvshr-becomes-slice-safe
  (implies (and (syntaxp (and (quotep shift-amount) ; not always true
                              (quotep width)
                              (quotep n)))
                (natp width)
                (natp shift-amount))
           (equal (bvchop n (bvshr width x shift-amount))
                  (if (natp n)
                      (if (<= n (- width shift-amount))
                          (slice (+ -1 n shift-amount) shift-amount x)
                          (slice (+ -1 width) shift-amount x))
                    0)))
  :hints (("Goal" :in-theory (enable bvshr))))

;yuck?
;changes the width depending on the shift amount
(defthmd bvchop-of-bvshr-new
  (implies (and (< size1 size2)
                (natp size1)
                (natp size2)
                (natp amt))
           (equal (bvchop size1 (bvshr size2 x amt))
                  (if (<= size1 (- size2 amt))
                      (bvshr (+ size1 amt) x amt)
                    (bvshr size2 x amt))))
  :hints (("Goal" :in-theory (enable bvshr))))

(defthmd bvshr-rewrite-for-constant-shift-amount
  (implies (syntaxp (and (quotep shift-amount)
                         (quotep width)) ; will usually be true
                    )
           (equal (bvshr width x shift-amount)
                  (slice (+ -1 (nfix width)) (nfix shift-amount) x)))
  :hints (("Goal" :in-theory (enable bvshr))))

(defthm bvshr-same
  (implies (natp width)
           (equal (bvshr width x width)
                  0))
  :hints (("Goal" :in-theory (enable bvshr))))

(defthm bvshr-of-bvchop
  (equal (bvshr width (bvchop width x) shift-amount)
         (bvshr width x shift-amount))
  :hints (("Goal" :cases ((equal 0 width))
           :in-theory (enable bvshr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvshr-cases-term-fn-aux (i width)
  (declare (xargs :guard (integerp width)
                  :measure (nfix (+ 1 i))))
  (if (not (posp i))
      `((otherwise (bvshr ,width x 0))) ; covers 0 and all other cases: ensures that a number is always returned
    (cons `(,i (bvshr ,width x ,i))
          (bvshr-cases-term-fn-aux (+ -1 i) width))))

(defund bvshr-cases-term-fn (width)
  (declare (xargs :guard (natp width)))
  `(case shift-amount
     ,@(bvshr-cases-term-fn-aux width width)))

(defmacro bvshr-cases-term (width)
  (bvshr-cases-term-fn width))

;pretty gross
(defthmd bvshr-16-cases
  (implies (and (syntaxp (not (quotep shift-amount)))
                (natp shift-amount)
                (<= shift-amount 16))
           (equal (bvshr 16 x shift-amount)
                  (bvshr-cases-term 16)))
  :hints (("Goal" :in-theory (enable bvshr))))

;pretty gross
(defthmd bvshr-32-cases
  (implies (and (syntaxp (not (quotep shift-amount)))
                (natp shift-amount)
                (<= shift-amount 32))
           (equal (bvshr 32 x shift-amount)
                  (bvshr-cases-term 32)))
  :hints (("Goal" :in-theory (enable bvshr))))

;pretty gross
(defthmd bvshr-64-cases
  (implies (and (syntaxp (not (quotep shift-amount)))
                (natp shift-amount)
                (<= shift-amount 64))
           (equal (bvshr 64 x shift-amount)
                  (bvshr-cases-term 64)))
  :hints (("Goal" :in-theory (enable bvshr))))
