; Signed bit-vector division
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "unsigned-byte-p-forced")
(include-book "bvchop")
(include-book "logext")

;fixme make sure this is right
;this is like java's idiv
;takes and returns USBs
(defund sbvdiv (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y)
           (xargs :guard (not (equal 0 (bvchop n y)))))
  (bvchop n (truncate (logext n x) (logext n y))))

(defthm unsigned-byte-p-of-sbvdiv
  (implies (<= size size2)
           (equal (unsigned-byte-p size2 (sbvdiv size x y))
                  (natp size2)))
  :hints (("Goal" :in-theory (enable sbvdiv))))

(defthm natp-of-sbvdiv
  (natp (sbvdiv size x y)))

(defthm integerp-of-sbvdiv
  (integerp (sbvdiv size x y)))

;do not remove (helps justify the translation to STP)
(defthm sbvdiv-of-bvchop-arg2
  (implies (and (<= size size1)
                (posp size)
                (integerp size1))
           (equal (sbvdiv size (bvchop size1 x) y)
                  (sbvdiv size x y)))
  :hints (("Goal" :in-theory (enable sbvdiv))))

;do not remove (helps justify the translation to STP)
(defthm sbvdiv-of-bvchop-arg3
  (implies (and (<= size size1)
                (posp size)
                (integerp size1))
           (equal (sbvdiv size y (bvchop size1 x))
                  (sbvdiv size y x)))
  :hints (("Goal" :in-theory (enable sbvdiv))))

; a totalized version of sbvdiv, where division by 0 yields 0
;logically this is equal to sbvdiv (see theorem sbvdiv-total-becomes-sbvdiv)
(defund sbvdiv-total (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y))
  (if (equal 0 (logext n y))
      (logext n 0)
    (sbvdiv n x y)))

(defthm sbvdiv-total-becomes-sbvdiv
  (equal (sbvdiv-total n x y)
         (sbvdiv n x y))
  :hints (("Goal" :in-theory (enable SBVDIV sbvdiv-total truncate))))

(defthm truncate-of-0
  (equal (truncate i 0)
         0)
  :hints (("Goal" :in-theory (enable truncate))))

;do not remove (helps justify the translation to STP)
(defthm sbvdiv-of-0-arg1
  (equal (sbvdiv 0 x y)
         0)
  :hints (("Goal" :in-theory (enable sbvdiv))))

(defthm sbvdiv-of-0-arg2
  (equal (sbvdiv size 0 x)
         0)
  :hints (("Goal" :in-theory (enable sbvdiv))))

;do not remove (helps justify the translation to STP)
(defthm sbvdiv-of-0-arg3
  (equal (sbvdiv size x 0)
         0)
  :hints (("Goal" :in-theory (enable sbvdiv))))

(defthm sbvdiv-total-of-0
  (equal (sbvdiv-total n x 0)
         0))

(defthm unsigned-byte-p-forced-of-sbvdiv
  (equal (unsigned-byte-p-forced size (sbvdiv size x y))
         (natp size))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced natp sbvdiv))))

;todo move?
;fixme could call this sbvfloor
;this one rounds toward negative infinity
(defund sbvdivdown (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y)
           (xargs :guard (not (equal 0 (logext n y))) ;simplify!
                  ))
  (bvchop n (floor (logext n x) (logext n y))))

;x div x is usually 1
(defthm sbvdiv-same
  (implies (posp size)
           (equal (sbvdiv size x x)
                  (if (equal 0 (bvchop size x))
                      0
                    1)))
  :hints (("Goal" :in-theory (enable sbvdiv))))
