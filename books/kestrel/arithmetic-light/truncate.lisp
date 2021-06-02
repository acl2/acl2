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
(local (include-book "numerator"))
(local (include-book "times"))
(local (include-book "plus"))

(in-theory (disable truncate))

(defthm truncate-of-0-arg1
  (equal (truncate 0 y)
         0)
  :hints (("Goal" :in-theory (enable truncate))))

(defthm truncate-of-0-arg2
  (equal (truncate i 0)
         0)
  :hints (("Goal" :in-theory (enable truncate))))

(defthm truncate-of-1-when-integerp-arg2
  (implies (integerp i)
           (equal (truncate i 1)
                  i))
  :hints (("Goal" :in-theory (enable truncate))))

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

;; in this case, the quotient is positive
(defthmd truncate-becomes-floor-gen1
  (implies (and (or (and (<= 0 i) (<= 0 j))
                    (and (< i 0) (< j 0)))
                (rationalp i)
                (rationalp j))
           (equal (truncate i j)
                  (floor i j)))
  :hints (("Goal" :in-theory (enable floor truncate))))

;; in this case, the quotient is negative
(defthmd truncate-becomes-floor-gen2
  (implies (and (or (and (<= i 0) (<= 0 j))
                    (and (<= 0 i) (<= j 0)))
                (not (integerp (/ i j)))
                (rationalp i)
                (rationalp j)
                )
           (equal (truncate i j)
                  (+ 1 (floor i j))))
  :hints (("Goal" :in-theory (enable floor truncate))))

(defthmd truncate-becomes-floor-gen3
  (implies (and (integerp (/ i j))
                (rationalp i)
                (rationalp j))
           (equal (truncate i j)
                  (floor i j)))
  :hints (("Goal" :in-theory (enable floor truncate))))

;better in some cases
(defthmd truncate-becomes-floor-other
  (implies (and (rationalp i)
                (rationalp j))
           (equal (truncate i j)
                  (if (integerp (/ i j))
                      (floor i j)
                    (if (or (and (<= 0 i) (<= 0 j))
                            (and (< i 0) (< j 0)))
                        (floor i j)
                      (+ 1 (floor i j))))))
  :hints (("Goal" :in-theory (enable floor truncate))))

(defthmd truncate-becomes-floor-gen
  (implies (and (rationalp i)
                (rationalp j))
           (equal (truncate i j)
                  (if (equal (floor i j) (/ i j))
                      (floor i j)
                      (if (or (and (<= 0 i) (<= 0 j))
                              (and (< i 0) (< j 0)))
                          (floor i j)
                          (+ 1 (floor i j))))))
  :hints (("Goal" :in-theory (enable truncate-becomes-floor-gen1
                                     truncate-becomes-floor-gen2
                                     truncate-becomes-floor-gen3))))

(defthm equal-of-truncate-same
  (implies (and (natp i) ;gen
                (integerp j)
                (< 1 j))
           (equal (equal (truncate i j) i)
                  (equal i 0)))
  :hints (("Goal" :in-theory (enable truncate-becomes-floor-gen))))

(defthm truncate-of--1
  (implies (integerp i)
           (equal (truncate i -1)
                  (- i)))
  :hints (("Goal" :in-theory (enable truncate))))

(defthm truncate-of-truncate
  (implies (and (rationalp i)
                (<= 0 i) ;gen?
                (natp j1)
                (natp j2))
           (equal (truncate (truncate i j1) j2)
                  (truncate i (* j1 j2))))
  :hints (("Goal" :in-theory (enable truncate-becomes-floor-gen))))

;; (thm
;;  (implies (and (signed-byte-p size x)
;;                (signed-byte-p size y))
;;           (equal (signed-byte-p size (truncate x y))
;;                  (not (and (equal x (- (expt 2 (+ -1 size))))
;;                            (equal y -1)))))
;;  :hints (("Goal" :cases ((< x 0))
;;           :in-theory (enable truncate-becomes-floor-gen))))
