; Signed bit-vector remainder
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvchop")
(include-book "logext")
(include-book "bvmod")
(include-book "unsigned-byte-p-forced")
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divides" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

;fixme make sure this is what i want and that it matches what java does
(defund sbvrem (n x y)
  (declare (type integer x y)
           (type (integer 1 *) n)
           (xargs :guard (not (equal (bvchop n y) 0))))
  (bvchop n (rem (logext n x) (logext n y)))
;  (bvchop n (- x (* (truncate (logext n x) (logext n y)) y)))
  )

(defthm unsigned-byte-p-of-sbvrem
  (implies (<= size size2)
           (equal (unsigned-byte-p size2 (sbvrem size x y))
                  (natp size2)))
  :hints (("Goal" :in-theory (enable sbvrem))))

(defthm natp-of-sbvrem
  (natp (sbvrem size x y)))

(defthm integerp-of-sbvrem
  (integerp (sbvrem size x y)))

;destructor elim happens
;or just rely on (:rewrite sbvrem-when-positive)?
;fixme gen!
(defthm equal-of-0-and-sbvrem-when-small
  (implies (and (equal width 32) ;fixme
                (natp x)
                (unsigned-byte-p (+ -1 width) n)
                (< x n)
                (posp width)
                )
           (equal (equal 0 (sbvrem width x n))
                  (equal 0 x)))
  :hints (("Goal" :in-theory (enable ;logext logapp
                                     sbvrem
                                     bvchop-of-sum-cases
                                     truncate-becomes-floor-gen))))

;do not remove (helps justify the translation to STP)
(defthm sbvrem-of-bvchop-arg2
  (implies (and (<= size size1)
                (posp size)
                (integerp size1))
           (equal (sbvrem size (bvchop size1 x) y)
                  (sbvrem size x y)))
  :hints (("Goal" :in-theory (enable sbvrem))))

;do not remove (helps justify the translation to STP)
(defthm sbvrem-of-bvchop-arg3
  (implies (and (<= size size1)
                (posp size)
                (integerp size1))
           (equal (sbvrem size y (bvchop size1 x))
                  (sbvrem size y x)))
  :hints (("Goal" :in-theory (enable sbvrem))))

(defthm unsigned-byte-p-forced-of-sbvrem
  (equal (unsigned-byte-p-forced size (sbvrem size x y))
         (natp size))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced natp sbvrem))))

;todo: move?
(defund sbvmoddown (n x y)
  (declare (type integer x y)
           (type (integer 1 *) n)
           (xargs :guard (not (EQUAL (LOGEXT N Y) 0))) ;rephrase in terms of bvchop?
           )
  (bvchop n (mod (logext n x) (logext n y))))

(defthm sbvrem-of-0-arg1
  (equal (sbvrem 0 x y)
         0)
  :hints (("Goal" :in-theory (enable sbvrem))))

(defthm sbvrem-of-0-arg2
  (equal (sbvrem size 0 y)
         0)
  :hints (("Goal" :in-theory (enable sbvrem truncate))))

;do not remove.  this helps justify the translation to STP.
(defthm sbvrem-of-0-arg3
  (equal (sbvrem size x 0)
         (bvchop size x))
  :hints (("Goal" :in-theory (enable sbvrem))))

(defthm sbvrem-of-1-arg3
  (equal (sbvrem size x 1)
         0)
  :hints (("Goal" :cases ((posp size))
           :in-theory (enable sbvrem))))
