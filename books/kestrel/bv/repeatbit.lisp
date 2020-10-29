; Creating BVs of all ones or all zeros
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))

;we expect bit to be 0 or 1
;bozo this should probably be changed to chop bit down to a one bit quantity first
(defund repeatbit (n bit)
  (declare (type integer n)
           (type (integer 0 *) bit)) ;tighten to only allow 0 or 1?
  (if (not (natp n))
      0
    (if (= 0 bit)
        0
      (+ -1 (expt 2 n)))))

(defthm repeatbit-of-0
  (equal (repeatbit n 0)
         0)
  :hints (("Goal" :in-theory (enable repeatbit))))

(defthm repeatbit-of-0-arg1
  (equal (repeatbit 0 n)
         0)
  :hints (("Goal" :in-theory (enable repeatbit))))

(defthm integerp-of-repeatbit
  (integerp (repeatbit n x))
  :hints (("Goal" :in-theory (enable repeatbit))))

(defthm natp-of-repeatbit
  (natp (repeatbit n bit))
  :hints (("Goal" :in-theory (enable REPEATBIT))))

;bozo gen
(defthm unsigned-byte-p-of-repeatbit
  (implies (natp n)
           (unsigned-byte-p n (repeatbit n bit)))
  :hints (("Goal" :in-theory (enable repeatbit))))

(defthm equal-of-repeatbit-and-repeatbit
  (implies (and (unsigned-byte-p 1 x)
                (unsigned-byte-p 1 y)
                )
           (equal (equal (repeatbit n x)
                         (repeatbit n y))
                  (or (not (posp n))
                      (equal x y))))
  :hints (("Goal" :in-theory (enable repeatbit))))

(defthm repeatbit-of-1-arg2
  (equal (repeatbit size 1)
         (+ -1 (expt 2 (nfix size))))
  :hints (("Goal" :in-theory (enable repeatbit))))

(defthm repeatbit-of-1
  (implies (unsigned-byte-p 1 x)
           (equal (repeatbit 1 x)
                  x))
  :hints (("Goal" :in-theory (enable repeatbit))))

(defthm repeatbit-equal-0-rewrite-2
  (implies (and (< 0 n)
                (integerp n))
           (equal (equal (repeatbit n bit) 0)
                  (equal 0 bit)))
  :hints (("Goal" :in-theory (enable repeatbit))))

(defthm repeatbit-equal-0-rewrite
  (implies (posp n)
           (equal (equal (repeatbit n bit) 0)
                  (equal bit 0)))
  :hints (("Goal" :in-theory (enable repeatbit))))

(defthm repeatbit-equal-0-rewrite-1
  (implies (and (< 0 n)
                (integerp n))
           (equal (equal 0 (repeatbit n bit))
                  (equal 0 bit)))
  :hints (("Goal" :in-theory (enable repeatbit))))

(defthm repeatbit-base
  (implies (zp n)
           (equal (repeatbit n bit)
                  0))
  :hints (("Goal" :in-theory (enable repeatbit))))
