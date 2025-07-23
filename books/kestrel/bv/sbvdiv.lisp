; Signed bit-vector division
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "unsigned-byte-p-forced")
(include-book "bvchop")
(include-book "logext-def")
(local (include-book "getbit"))
(local (include-book "logext"))
(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))

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
                (natp size)
                (integerp size1))
           (equal (sbvdiv size (bvchop size1 x) y)
                  (sbvdiv size x y)))
  :hints (("Goal" :cases ((equal 0 size))
           :in-theory (enable sbvdiv))))

;do not remove (helps justify the translation to STP)
(defthm sbvdiv-of-bvchop-arg3
  (implies (and (<= size size1)
                (natp size)
                (integerp size1))
           (equal (sbvdiv size y (bvchop size1 x))
                  (sbvdiv size y x)))
  :hints (("Goal" :cases ((equal 0 size))
           :in-theory (enable sbvdiv))))

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


;x div x is usually 1
(defthm sbvdiv-same
  (implies (posp size)
           (equal (sbvdiv size x x)
                  (if (equal 0 (bvchop size x))
                      0
                    1)))
  :hints (("Goal" :in-theory (enable sbvdiv unsigned-byte-p))))

(defthm sbvdiv-of-1-arg3
  (implies (and (<= 1 size) ; doesn't work for size=1
                (integerp size))
           (equal (sbvdiv size x 1)
                  (bvchop size x)))
  :hints (("Goal" :cases ((equal 1 size))
           :in-theory (e/d (sbvdiv) (truncate)))))
