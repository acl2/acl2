; A lightweight book about the built-in function signed-byte-p
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

(in-theory (disable signed-byte-p))

(defthm signed-byte-p-cases
  (equal (signed-byte-p 1 x)
         (or (equal 0 x)
             (equal -1 x)))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

(defthm signed-byte-when-not-integerp-cheap
  (implies (not (integerp bits))
           (not (signed-byte-p bits x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

(defthm signed-byte-when-<=-of-0-cheap
  (implies (<= bits 0)
           (not (signed-byte-p bits x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

;; As long as x is smaller than some signed-byte, adding 1 can't overflow.
(defthm signed-byte-p-of-+-of-1
  (implies (and (signed-byte-p size x)
                (< x free)
                (signed-byte-p size free)
                (posp size))
           (signed-byte-p size (+ 1 x)))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

(defthm signed-byte-p-when-signed-byte-p
  (implies (and (signed-byte-p freesize x)
                (<= freesize size)
                (posp size))
           (signed-byte-p size x))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

(defthmd signed-byte-p-when-unsigned-byte-p-one-less
  (implies (and (unsigned-byte-p (+ -1 size) x)
                (posp size))
           (signed-byte-p size x))
  :hints (("Goal" :in-theory (enable signed-byte-p unsigned-byte-p))))

(defthm signed-byte-p-when-unsigned-byte-p-smaller-free
  (implies (and (unsigned-byte-p freesize x)
                (< freesize size)
                (integerp size))
           (signed-byte-p size x))
  :hints (("Goal" :in-theory (enable signed-byte-p unsigned-byte-p))))

(defthm signed-byte-p-when-unsigned-byte-p
  (implies (and (unsigned-byte-p size x)
                (posp size))
           (equal (signed-byte-p size x)
                  (unsigned-byte-p (+ -1 size) x)))
  :hints (("Goal" :in-theory (enable signed-byte-p unsigned-byte-p))))

(defthm signed-byte-p-longer
  (implies (and (signed-byte-p free i)
                (<= free size)
                (integerp size)
                (natp free))
           (signed-byte-p size i))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

(defthm sbp-32-when-non-neg
  (implies (<= 0 x)
           (equal (signed-byte-p 32 x)
                  (unsigned-byte-p 31 x)))
  :hints (("Goal" :in-theory (enable signed-byte-p unsigned-byte-p))))

(defthm sbp-ubp-hack
  (implies (unsigned-byte-p 31 x)
           (signed-byte-p 32 (+ -1 x)))
  :hints (("Goal" :in-theory (enable signed-byte-p unsigned-byte-p))))

(defthm signed-byte-p-of-plus-constant
  (implies (and (syntaxp (quotep k))
                (natp k)
                (< x (- 2147483648 k))
                (signed-byte-p 32 x))
           (signed-byte-p 32 (+ k x)))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

(defthm signed-byte-p-forward-arg1
  (implies (signed-byte-p size y)
           (and (integerp size)
                (< 0 size)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable signed-byte-p))))

(defthm signed-byte-p-of-+
  (implies (and (signed-byte-p (+ -1 size) x)
                (signed-byte-p (+ -1 size) y))
           (equal (signed-byte-p size (+ x y))
                  (posp size)))
  :hints (("Goal" :in-theory (enable signed-byte-p expt-of-+))))

(defthmd signed-byte-p-in-terms-of-floor
  (equal (signed-byte-p size x)
         (and (integerp x)
              (posp size)
              (equal (floor x (expt 2 (+ -1 size)))
                     (if (< x 0)
                         -1
                       0))))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

(defthmd signed-byte-p-in-terms-of-floor-when-negative
  (implies (< x 0)
           (equal (signed-byte-p size x)
                  (and (integerp x)
                       (posp size)
                       (equal (floor x (expt 2 (+ -1 size)))
                              -1))))
  :hints (("Goal" :in-theory (enable SIGNED-BYTE-P))))

(defthm floor-of-expt-2-of-one-less-when-signed-byte-p
  (implies (signed-byte-p size x)
           (equal (floor x (expt 2 (+ -1 size)))
                  (if (< x 0)
                      -1
                    0)))
  :hints (("Goal" :in-theory (enable signed-byte-p))))
