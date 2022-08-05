; A lightweight book about the built-in function signed-byte-p
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/arithmetic-light/expt2" :dir :system)) ;drop

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
