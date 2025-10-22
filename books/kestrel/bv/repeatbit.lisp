; Creating BVs of all ones or all zeros
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also repeatbit2.lisp

(include-book "repeatbit-def") ; brings in repeatbit
(local (include-book "bvchop"))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))

(defthm repeatbit-of-0-arg2
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
  :hints (("Goal" :in-theory (enable repeatbit unsigned-byte-p))))

(defthm equal-of-repeatbit-and-repeatbit
  (equal (equal (repeatbit n x)
                (repeatbit n y))
         (or (not (posp n))
             (equal (bvchop 1 x)
                    (bvchop 1 y))))
  :hints (("Goal" :in-theory (enable repeatbit))))

;; disabled to prevent introducing expt (when size is constant the whole thing
;; gets evaluated)
(defthmd repeatbit-of-1-arg2
  (equal (repeatbit size 1)
         (+ -1 (expt 2 (nfix size))))
  :hints (("Goal" :in-theory (enable repeatbit))))

(defthm repeatbit-of-1-arg1
  (equal (repeatbit 1 x)
         (bvchop 1 x))
  :hints (("Goal" :in-theory (enable repeatbit))))

(defthm repeatbit-equal-0-rewrite-2
  (implies (and (< 0 n)
                (integerp n))
           (equal (equal (repeatbit n bit) 0)
                  (equal 0 (bvchop 1 bit))))
  :hints (("Goal" :in-theory (enable repeatbit))))

(defthm repeatbit-equal-0-rewrite
  (implies (posp n)
           (equal (equal (repeatbit n bit) 0)
                  (equal (bvchop 1 bit) 0)))
  :hints (("Goal" :in-theory (enable repeatbit))))

(defthm repeatbit-equal-0-rewrite-1
  (implies (and (< 0 n)
                (integerp n))
           (equal (equal 0 (repeatbit n bit))
                  (equal 0 (bvchop 1 bit))))
  :hints (("Goal" :in-theory (enable repeatbit))))

(defthm repeatbit-base
  (implies (zp n)
           (equal (repeatbit n bit)
                  0))
  :hints (("Goal" :in-theory (enable repeatbit))))

(defthm equal-of-repeatbit-and-constant
  (implies (syntaxp (quotep k))
           (equal (equal k (repeatbit n bit))
                  (if (not (posp n))
                      (equal k 0)
                    (if (equal k 0)
                        (equal (bvchop 1 bit) 0)
                      (if (equal k (+ -1 (expt 2 n)))
                          (not (equal (bvchop 1 bit) 0))
                        nil)))))
  :hints (("Goal" :in-theory (enable repeatbit))))

;; restrict to constant k?
(defthm <-of-repeatbit-small
  (implies (and (<= k (+ -1 (expt 2 n)))
                (posp k)
                (natp n))
           (equal (< (repeatbit n bit) k)
                  (equal (bvchop 1 bit) 0)))
  :hints (("Goal" :in-theory (enable repeatbit))))

(defthm <-of-0-and-repeatbit
  (equal (< 0 (repeatbit n bit))
         (and (posp n)
              (not (equal 0 (bvchop 1 bit)))))
  :hints (("Goal" :in-theory (enable repeatbit))))

(defthm unsigned-byte-p-of-repeatbit-of-1-arg2
  (implies (natp n)
           (equal (unsigned-byte-p size (repeatbit n 1))
                  (and (<= n size)
                       (natp size))))
  :hints (("Goal" :in-theory (enable repeatbit-of-1-arg2))))
