; A lightweight book about the built-in function truncate
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "floor"))

(in-theory (disable truncate))

(defthmd truncate-becomes-floor
  (implies (and ;(rationalp i)
                (<= 0 i)
                (rationalp j)
                (<= 0 j))
           (equal (truncate i j)
                  (floor i j)))
  :hints (("Goal" :in-theory (enable floor truncate)
           :do-not '(generalize eliminate-destructors))))

(local (include-book "nonnegative-integer-quotient"))

(defthm <=-of-truncate-and-0-when-nonnegative-and-nonnegative-type
  (implies (and (<= 0 i)
                (<= 0 j)
                (rationalp i))
           (<= 0 (truncate i j)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable truncate))))

(defthm <=-of-truncate-and-0-when-nonnegative-and-nonpositive-type
  (implies (and (<= 0 i)
                (<= j 0)
                (rationalp i))
           (<= (truncate i j) 0))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable truncate))))

(defthm <=-of-truncate-and-0-when-nonpositive-and-nonnegative-type
  (implies (and (<= i 0)
                (<= 0 j)
                (rationalp i))
           (<= (truncate i j) 0))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable truncate))))

(defthm <=-of-truncate-and-0-when-nonpositive-and-nonpositive-type
  (implies (and (<= i 0)
                (<= j 0)
                (rationalp i))
           (<= 0 (truncate i j)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable truncate))))

(defthm <=-of-truncate-same-linear
  (implies (and (rationalp i)
                (<= 0 i)
                (integerp j) ;excludes things like 1/2
                )
           (<= (truncate i j) i))
  :rule-classes :linear
  :hints (("Goal" :cases ((< j 0))
           :in-theory (enable truncate-becomes-floor))))
