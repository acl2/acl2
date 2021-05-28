; Bit-vector division
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv/bvchop" :dir :system)
(include-book "kestrel/bv/unsigned-byte-p" :dir :system)
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

;(local (in-theory (disable floor-bounded-by-/))) ;causes forcing

;divide and round toward 0
;fixme what should this do if y is 0?
(defun bvdiv (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y)
           (xargs :guard (not (equal 0 (bvchop n y)))))
  ;;drop the outer bvchop?
  (bvchop n (floor (bvchop n x) (bvchop n y))))

(defthm integerp-of-bvdiv
  (integerp (bvdiv size x y)))

(defthm natp-of-bvdiv
  (natp (bvdiv size x y)))

(defthm bvdiv-of-0-arg1
  (equal (bvdiv 0 x y)
         0)
  :hints (("Goal" :in-theory (enable bvdiv))))

(defthm bvdiv-of-0-arg2
  (equal (bvdiv size 0 x)
         0)
  :hints (("Goal" :in-theory (enable bvdiv))))

;do not remove.  this helps justify the translation to STP.
(defthm bvdiv-of-0-arg3
  (equal (bvdiv size x 0)
         0)
  :hints (("Goal" :in-theory (enable bvdiv))))

(defthm bvdiv-when-size-is-not-positive
  (implies (<= size 0)
           (equal (bvdiv size x y)
                  0))
  :hints (("Goal" :in-theory (e/d (bvdiv) nil))))

(defthm bvdiv-of-bvchop-arg2
  (implies (and (<= size size1)
                (natp size)
                (integerp size1))
           (equal (bvdiv size (bvchop size1 x) y)
                  (bvdiv size x y)))
  :hints (("Goal" :in-theory (enable bvdiv))))

;do not remove (helps justify the translation to STP)
(defthm bvdiv-of-bvchop-arg2-same
  (equal (bvdiv size (bvchop size x) y)
         (bvdiv size x y))
  :hints (("Goal" :in-theory (enable bvdiv))))

(defthm bvdiv-of-bvchop-arg3
  (implies (and (<= size size1)
                (natp size)
                (integerp size1))
           (equal (bvdiv size y (bvchop size1 x))
                  (bvdiv size y x)))
  :hints (("Goal" :in-theory (enable bvdiv))))

;do not remove (helps justify the translation to STP)
(defthm bvdiv-of-bvchop-arg3-same
  (equal (bvdiv size y (bvchop size x))
         (bvdiv size y x))
  :hints (("Goal" :in-theory (enable bvdiv))))

(defthm unsigned-byte-p-of-bvdiv
  (implies (<= (ifix size2) size)
           (equal (unsigned-byte-p size (bvdiv size2 x y))
                  (natp size)))
  :hints (("Goal" :in-theory (enable bvdiv))))

(defthm bvchop-of-bvdiv
  (implies (and (<= size size2)
                (natp size)
                (natp size2))
           (equal (bvchop size2 (bvdiv size x y))
                  (bvdiv size x y))))

;x div x is usually 1
(defthm bvdiv-same
  (implies (posp size)
           (equal (bvdiv size x x)
                  (if (equal 0 (bvchop size x))
                      0
                    1)))
  :hints (("Goal" :in-theory (enable bvdiv))))

;; x/1 becomes x (roughly)
(defthm bvdiv-of-1-arg3
  (equal (bvdiv size x 1)
         (bvchop size x)))

(defthm <-of-bvdiv-self
  (implies (and (unsigned-byte-p size x) ;gen?
                (< 1 (bvchop size y)))
           (equal (< (bvdiv size x y) x)
                  (not (equal 0 (bvchop size x)))))
  :hints (("Goal" :in-theory (enable bvdiv))))

;; dividing x by y (usually) makes it smaller
(defthm <-of-bvdiv-linear
  (implies (and (<= 0 x)
                (< 1 (bvchop size y))
                (not (equal 0 (bvchop size x)))
                (natp size))
           (< (bvdiv size x y) x))
  :rule-classes :linear
  :hints (("Goal" :use (:instance <-of-bvdiv-self
                                  (x (bvchop size x))))))

(defthm <=-of-bvdiv-linear
  (implies (<= 0 x)
           (<= (bvdiv size x y) x))
  :rule-classes :linear)
