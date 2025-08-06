; Rules that deal with both bvsx and other operations
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvcat-rules")
(include-book "bvsx")
(include-book "bvand")
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "repeatbit2"))
(local (include-book "unsigned-byte-p"))

(defthm bvand-of-bvsx-low-arg2
  (implies (and (<= size old-size)
                (<= old-size new-size)
                (natp size)
                (integerp new-size)
                (natp old-size))
           (equal (bvand size (bvsx new-size old-size x) y)
                  (bvand size x y)))
  :hints (("Goal" :in-theory (enable bvsx))))

(defthm bvand-of-bvsx-low-arg3
  (implies (and (<= size old-size)
                (<= old-size new-size)
                (natp size)
                (integerp new-size)
                (natp old-size))
           (equal (bvand size x (bvsx new-size old-size y))
                  (bvand size x y)))
  :hints (("Goal" :in-theory (enable bvsx))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvor-of-bvsx-low-arg2
  (implies (and (<= size old-size)
                (<= old-size new-size)
                (natp size)
                (integerp new-size)
                (natp old-size))
           (equal (bvor size (bvsx new-size old-size x) y)
                  (bvor size x y)))
  :hints (("Goal" :in-theory (enable bvsx))))

(defthm bvor-of-bvsx-low-arg3
  (implies (and (<= size old-size)
                (<= old-size new-size)
                (natp size)
                (integerp new-size)
                (natp old-size))
           (equal (bvor size x (bvsx new-size old-size y))
                  (bvor size x y)))
  :hints (("Goal" :in-theory (enable bvsx))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvxor-of-bvsx-low-arg2
  (implies (and (<= size old-size)
                (<= old-size new-size)
                (natp size)
                (integerp new-size)
                (natp old-size))
           (equal (bvxor size (bvsx new-size old-size x) y)
                  (bvxor size x y)))
  :hints (("Goal" :in-theory (enable bvsx))))

(defthm bvxor-of-bvsx-low-arg3
  (implies (and (<= size old-size)
                (<= old-size new-size)
                (natp size)
                (integerp new-size)
                (natp old-size))
           (equal (bvxor size x (bvsx new-size old-size y))
                  (bvxor size x y)))
  :hints (("Goal" :in-theory (enable bvsx))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bitand-of-bvsx-low-arg1
  (implies (and (posp old-size)
                (posp new-size))
           (equal (bitand (bvsx new-size old-size y) x)
                  (bitand y x)))
  :hints (("Goal"
           :cases ((equal 1 old-size))
           :in-theory (enable bvsx))))

(defthm bitand-of-bvsx-low-arg2
  (implies (and (posp old-size)
                (posp new-size))
           (equal (bitand x (bvsx new-size old-size y))
                  (bitand x y)))
  :hints (("Goal"
           :cases ((equal 1 old-size))
           :in-theory (enable bvsx))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bitor-of-bvsx-low-arg1
  (implies (and (posp old-size)
                (posp new-size))
           (equal (bitor (bvsx new-size old-size y) x)
                  (bitor y x)))
  :hints (("Goal"
           :cases ((equal 1 old-size))
           :in-theory (enable bvsx))))

(defthm bitor-of-bvsx-low-arg2
  (implies (and (posp old-size)
                (posp new-size))
           (equal (bitor x (bvsx new-size old-size y))
                  (bitor x y)))
  :hints (("Goal"
           :cases ((equal 1 old-size))
           :in-theory (enable bvsx))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bitxor-of-bvsx-low-arg1
  (implies (and (posp old-size)
                (posp new-size))
           (equal (bitxor (bvsx new-size old-size y) x)
                  (bitxor y x)))
  :hints (("Goal"
           :cases ((equal 1 old-size))
           :in-theory (enable bvsx))))

(defthm bitxor-of-bvsx-low-arg2
  (implies (and (posp old-size)
                (posp new-size))
           (equal (bitxor x (bvsx new-size old-size y))
                  (bitxor x y)))
  :hints (("Goal"
           :cases ((equal 1 old-size))
           :in-theory (enable bvsx))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvplus-of-bvsx-low-arg2
  (implies (and (<= size old-size)
                (<= old-size new-size)
                (natp size)
                (integerp new-size)
                (natp old-size))
           (equal (bvplus size (bvsx new-size old-size x) y)
                  (bvplus size x y)))
  :hints (("Goal" :in-theory (enable bvsx))))

(defthm bvplus-of-bvsx-low-arg3
  (implies (and (<= size old-size)
                (<= old-size new-size)
                (natp size)
                (integerp new-size)
                (natp old-size))
           (equal (bvplus size x (bvsx new-size old-size y))
                  (bvplus size x y)))
  :hints (("Goal" :in-theory (enable bvsx))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvminus-of-bvsx-low-arg2
  (implies (and (<= size old-size)
                (<= old-size new-size)
                (natp size)
                (integerp new-size)
                (natp old-size))
           (equal (bvminus size (bvsx new-size old-size x) y)
                  (bvminus size x y)))
  :hints (("Goal" :in-theory (enable bvsx))))

(defthm bvminus-of-bvsx-low-arg3
  (implies (and (<= size old-size)
                (<= old-size new-size)
                (natp size)
                (integerp new-size)
                (natp old-size))
           (equal (bvminus size x (bvsx new-size old-size y))
                  (bvminus size x y)))
  :hints (("Goal" :in-theory (enable bvsx))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvmult-of-bvsx-low-arg2
  (implies (and (<= size old-size)
                (<= old-size new-size)
                (natp size)
                (natp old-size)
                (integerp new-size))
           (equal (bvmult size (bvsx new-size old-size x) y)
                  (bvmult size x y)))
  :hints (("Goal" :in-theory (enable bvsx))))

(defthm bvmult-of-bvsx-low-arg3
  (implies (and (<= size old-size)
                (<= old-size new-size)
                (natp size)
                (natp old-size)
                (integerp new-size))
           (equal (bvmult size x (bvsx new-size old-size y))
                  (bvmult size x y)))
  :hints (("Goal" :in-theory (enable bvsx))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvuminus-of-bvsx-low
  (implies (and (<= size old-size)
                (<= old-size new-size)
                (natp size)
                (integerp new-size)
                (natp old-size))
           (equal (bvuminus size (bvsx new-size old-size x))
                  (bvuminus size x)))
  :hints (("Goal" :in-theory (enable bvsx))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvif-of-bvsx-low-arg3
  (implies (and (<= size old-size)
                (<= old-size new-size)
                (natp size)
                (integerp new-size)
                (natp old-size))
           (equal (bvif size test (bvsx new-size old-size x) y)
                  (bvif size test x y)))
  :hints (("Goal" :in-theory (enable bvsx))))

(defthm bvif-of-bvsx-low-arg4
  (implies (and (<= size old-size)
                (<= old-size new-size)
                (natp size)
                (integerp new-size)
                (natp old-size))
           (equal (bvif size test x (bvsx new-size old-size y))
                  (bvif size test x y)))
  :hints (("Goal" :in-theory (enable bvsx))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: make a "both" rule
(defthm slice-of-bvsx
  (implies (and (< low old-size) ;this case (there must be at least one bit to sign-extend?)
                ;(< high new-size)
                (<= old-size new-size)
                (<= low high)
                (natp high)
                (natp low)
                (posp old-size)
                (natp new-size))
           (equal (slice high low (bvsx new-size old-size x))
                  (bvsx (+ (min new-size (+ 1 high)) (- low))
                        (- old-size low)
                        (slice high low x))))
  :hints (("Goal" :in-theory (enable bvsx natp))))

(defthm slice-of-bvsx-high
  (implies (and (<= old-size low) ;this case
                ;(< high new-size)
                (<= old-size new-size)
                (<= low high)
                (natp high)
                (natp low)
                (posp old-size)
                (natp new-size))
           (equal (slice high low (bvsx new-size old-size x))
                  (repeatbit (+ (min (+ 1 high) new-size)
                                (- low))
                             (getbit (+ -1 old-size) x))))
  :hints (("Goal" :in-theory (enable bvsx natp))))
