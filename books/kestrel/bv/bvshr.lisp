; Right shift
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "slice-def")
(local (include-book "slice"))

;shift-amount must be non-negative
;width must be positive (allow zero?). it's the width of x (to start out)
;fills with 0's at the top
;so if shift-amount is positive this will be a shorter bit-vector
;in no case will the result be longer than width bits
;hmmm. do we plan to enable or disable this?
;perhaps this should be called zshr (zero-extending shift)
(defund bvshr (width x shift-amount)
  (declare (type (integer 0 *) shift-amount)
           (type integer x)
           (type integer width)
           (xargs :guard (<= shift-amount width)) ;what happens if they're equal? i guess we get 0
           )
  (slice (+ -1 width) shift-amount x))

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

;FIXME gen
(defthm unsigned-byte-p-of-bvshr
  (implies (and (natp amt)
                (<= amt 32))
           (unsigned-byte-p 32 (bvshr 32 x amt)))
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
  (implies (and (syntaxp (quotep shift-amount))
                (syntaxp (quotep width)) ; will usually be true
                )
           (equal (bvshr width x shift-amount)
                  (slice (+ -1 width) shift-amount x)))
  :hints (("Goal" :in-theory (enable bvshr))))
