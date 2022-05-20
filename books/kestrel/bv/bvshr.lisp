; Right shift
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvshr-def")
(local (include-book "slice"))

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

;; TODO: gen
(defthm unsigned-byte-p-of-bvshr
  (implies (and (natp amt)
                (<= amt size)
                (integerp size))
           (unsigned-byte-p size (bvshr size x amt)))
  :hints (("Goal" :in-theory (enable bvshr))))

(defthm bvchop-of-bvshr
  (implies (and (integerp width)
                (integerp shift-amount))
           (equal (bvchop n (bvshr width x shift-amount))
                  (if (natp n)
                      (if (<= n (- width shift-amount))
                          (slice (+ -1 n shift-amount) shift-amount x)
                          (slice (+ -1 width) shift-amount x))
                    0)))
  :hints (("Goal" :in-theory (enable bvshr))))

(defthmd bvshr-rewrite-for-constant-shift-amount
  (implies (syntaxp (and (quotep shift-amount)
                         (quotep width)) ; will usually be true
                    )
           (equal (bvshr width x shift-amount)
                  (slice (+ -1 width) shift-amount x)))
  :hints (("Goal" :in-theory (enable bvshr))))

(defthm bvshr-same
  (implies (natp width)
           (equal (bvshr width x width)
                  0))
  :hints (("Goal" :in-theory (enable bvshr))))

(defthm bvshr-of-bvchop
  (implies (and (natp width)
                (natp shift-amount))
           (equal (bvshr width (bvchop width x) shift-amount)
                  (bvshr width x shift-amount)))
  :hints (("Goal" :cases ((equal 0 width))
           :in-theory (enable bvshr))))

