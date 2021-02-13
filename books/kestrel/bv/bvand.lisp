; Bitwise and
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "logand2")
(include-book "bvchop")
(include-book "getbit")
(include-book "ihs/basic-definitions" :dir :system) ;for logmaskp
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "unsigned-byte-p"))

(defund bvand (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (logand (bvchop size x)
          (bvchop size y)))

(defthm bvand-type
  (and (integerp (bvand size x y))
       (<= 0 (bvand size x y)))
  :rule-classes :type-prescription)

(in-theory (disable (:type-prescription bvand))) ; bvand-type is at least as good

;disable?
(defthm bvand-commutative
  (equal (bvand size x y)
         (bvand size y x))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-associative
  (equal (bvand size (bvand size x y) z)
         (bvand size x (bvand size y z)))
  :hints (("Goal" :in-theory (enable bvand natp))))

(defthm bvand-commutative-2
  (equal (bvand size y (bvand size x z))
         (bvand size x (bvand size y z)))
  :hints (("Goal" :in-theory (disable bvand-associative)
           :use ((:instance bvand-associative)
                 (:instance bvand-associative (x y) (y x))))))

(defthm bvand-same
  (equal (bvand size x x)
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-same-2
  (equal (bvand size x (bvand size x y))
         (bvand size x y))
  :hints (("Goal" :cases ((and (natp size) (integerp b) (integerp a))
                          (and (natp size) (integerp b) (not (integerp a)))
                          (and (natp size) (not (integerp b)) (integerp a))
                          (and (natp size) (not (integerp b)) (not (integerp a))))
           :in-theory (enable bvand))))

(defthm bvand-of-0-arg2
  (equal (bvand size 0 x)
         0)
  :hints (("Goal" :in-theory (enable bvand))))

;in case we don't have commutativity - drop, since we'll always commute??
(defthmd bvand-of-0-arg3
  (equal (bvand size x 0)
         0)
  :hints (("Goal" :in-theory (enable))))

(defthm bvand-combine-constants
  (implies (syntaxp (and (quotep y) ;tested first to fail fast
                         (quotep x)
                         (quotep size)))
           (equal (bvand size x (bvand size y z))
                  (bvand size (bvand size x y) z)))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-when-size-is-not-positive
  (implies (<= size 0)
           (equal (bvand size x y)
                  0))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-when-size-is-0
  (equal (bvand 0 x y)
         0)
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-when-x-is-not-an-integer
  (implies (not (integerp x))
           (equal (bvand size x y)
                  0))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-when-y-is-not-an-integer
  (implies (not (integerp y))
           (equal (bvand size x y)
                  0))
  :hints (("Goal" :in-theory (enable bvand))))

(defthmd unsigned-byte-p-of-bvand-simple
  (implies (natp size)
           (unsigned-byte-p size (bvand size x y)))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm unsigned-byte-p-of-bvand
  (implies (and (<= size n)
                (natp size)
                (natp n))
           (unsigned-byte-p n (bvand size x y)))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-bvand-simple)
           :in-theory (disable unsigned-byte-p-of-bvand-simple))))

(defthm bvchop-of-bvand
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2))
           (equal (bvchop size1 (bvand size2 x y))
                  (bvand size1 x y)))
  :hints (("Goal" :in-theory (enable bvand))))

;use trim?
(defthm bvand-of-constant
   (implies (and (syntaxp (and (quotep k)
                               (quotep size)))
                 (not (unsigned-byte-p size k)))
            (equal (bvand size k x)
                   (bvand size (bvchop size k) x)))
   :hints (("Goal" :in-theory (enable bvand))))

;; ;improve?
;; ;drop?
;; (defthm bvand-of-bvchop-tighten
;;   (implies (and (< size1 size2)
;;                 (natp size1)
;;                 (natp size2))
;;            (equal (BVAND size1 x (BVCHOP size2 y))
;;                   (BVAND size1 x (BVCHOP size1 y))))
;;   :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-of-bvchop-1
  (implies (and (<= size size2)
                (integerp size2))
           (equal (bvand size (bvchop size2 x) y)
                  (bvand size x y)))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-of-bvchop-arg1-same
  (equal (bvand size (bvchop size x) y)
         (bvand size x y))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-of-bvchop-2
  (implies (and (<= size size2)
                (integerp size2))
           (equal (bvand size x (bvchop size2 y))
                  (bvand size x y)))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-of-bvchop-arg2-same
  (equal (bvand size x (bvchop size y))
         (bvand size x y))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-with-mask-basic
  (equal (bvand size (+ -1 (expt 2 size)) x)
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-with-mask-basic-alt
  (equal (bvand size x (+ -1 (expt 2 size)))
         (bvchop size x))
  :hints (("Goal" :use (:instance bvand-with-mask-basic)
           :in-theory (disable bvand-with-mask-basic))))

;requires the number of 1's in k to be size
(defthm bvand-with-mask
  (implies (and (syntaxp (quotep k)) ;new
                (equal k (+ -1 (expt 2 size)))
                (natp size))
           (equal (bvand size k x)
                  (bvchop size x))))

(defthm bvand-with-mask-better
  (implies (and (logmaskp mask)
                (equal size (integer-length mask)) ;acl2 can bind size here...
                (<= size size2)
                (natp size)
                (integerp size2))
           (equal (bvand size2 mask i)
                  (bvchop size i)))
  :hints (("Goal" :in-theory (enable bvand))))

;doesn't bind any free vars
;add syntaxp hyp - does compute integer-length several times..
(defthm bvand-with-mask-better-eric
  (implies (and (syntaxp (quotep mask)) ;new
                (logmaskp mask)
                (<= (integer-length mask) size2)
                (natp size2))
           (equal (bvand size2 mask i)
                  (bvchop (integer-length mask) i))))

;don't need if we are commuting constants
(defthm bvand-with-mask-better-eric-alt
  (implies (and (syntaxp (quotep mask)) ;new
                (logmaskp mask)
                (<= (integer-length mask) size2)
                (natp size2))
           (equal (bvand size2 i mask)
                  (bvchop (integer-length mask) i)))
  :hints (("Goal" :use (:instance bvand-with-mask-better-eric)
           :in-theory (disable bvand-with-mask-better-eric
                               bvand-with-mask-better))))

(defthm bvand-when-size-is-not-integerp
  (implies (not (integerp size))
           (equal (bvand size x y) 0))
  :hints (("Goal" :in-theory (enable bvand))))

(defthmd bvand-commute-constant
  (implies (syntaxp (and (quotep y)
                         (not (quotep x))))
           (equal (bvand size x y)
                  (bvand size y x))))

(defthm unsigned-byte-p-of-bvand-2
  (implies (or (unsigned-byte-p size i)
               (unsigned-byte-p size j))
           (equal (unsigned-byte-p size (bvand n i j))
                  (natp size)))
  :hints (("Goal" :cases ((<= n size))
           :in-theory (enable bvand))))
