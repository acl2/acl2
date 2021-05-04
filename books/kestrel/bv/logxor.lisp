; BV Library: logxor
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "../arithmetic-light/minus"))
(local (include-book "../arithmetic-light/floor"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "../arithmetic-light/plus"))
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/expt"))
(local (include-book "../arithmetic-light/expt2"))
(local (include-book "lognot"))
(local (include-book "logand"))
(local (include-book "logior"))
(local (include-book "logorc1"))
(local (include-book "logeqv"))

(in-theory (disable binary-logxor))

;todo rename
(defthm logxor-commutative-no-clash
  (equal (logxor i j)
         (logxor j i))
  :hints (("Goal" :in-theory (e/d (logxor)
                                  (lognot-of-logeqv)))))

(defthm logxor-of-0
  (equal (logxor 0 j)
         (ifix j))
  :hints (("Goal" :in-theory (enable logxor))))

(defthm logxor-of--1
  (equal (logxor -1 j)
         (lognot j))
  :hints (("Goal" :in-theory (enable logxor))))

(defthm logxor-when-not-integerp-arg1
  (implies (not (integerp i))
           (equal (logxor i j)
                  (ifix j)))
  :hints (("Goal" :in-theory (enable logxor))))

(defthm logxor-when-not-integerp-arg2
  (implies (not (integerp j))
           (equal (logxor i j)
                  (ifix i)))
  :hints (("Goal" :in-theory (enable logxor))))

(defthm logxor-associative
  (equal (logxor (logxor i j) k)
         (logxor i (logxor j k)))
  :hints (("Goal" :in-theory (enable logxor))))

(defthm mod-of-logxor-and-expt
  (implies (and (natp n)
                (integerp i)
                (integerp j))
           (equal (mod (logxor i j) (expt 2 n))
                  (logxor (mod i (expt 2 n))
                          (mod j (expt 2 n)))))
  :hints (("Goal" :in-theory (enable logxor logeqv logorc1))))

(defthm mod-of-logxor-by-2
  (implies (and (integerp i)
                (integerp j))
           (equal (mod (logxor i j) 2)
                  (logxor (mod i 2) (mod j 2))))
  :hints (("Goal" :use (:instance mod-of-logxor-and-expt
                                  (n 1))
           :in-theory (disable mod-of-logxor-and-expt))))

(defthm logxor-same
  (equal (logxor i i)
         0)
  :hints (("goal" :in-theory (e/d (logxor) (lognot logeqv)))))

(defthm logxor-commutative-2
  (equal (logxor j i k)
         (logxor i j k))
  :hints (("Goal" :use ((:instance logxor-associative)
                        (:instance logxor-associative (i j) (j i)))
           :in-theory (disable logxor-associative))))

(defthm logxor-same-2
  (equal (logxor i i j)
         (ifix j))
  :hints (("Goal"
           :use (:instance logxor-associative (i i) (j i) (k j))
           :in-theory (disable logxor-associative))))

(defthm logxor-combine-constants
  (implies (syntaxp (and (quotep i)
                         (quotep j)))
           (equal (logxor i (logxor j k))
                  (logxor (logxor i j) k))))

(defthm floor-of-logxor-by-2
  (implies (and (integerp i)
                (integerp j))
           (equal (floor (logxor i j) 2)
                  (logxor (floor i 2) (floor j 2))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable logxor logeqv logorc1 floor-of-lognot-and-2))))

(defthmd floor-of-logxor-by-2-back
  (implies (and (integerp i)
                (integerp j))
           (equal (logxor (floor i 2) (floor j 2))
                  (floor (logxor i j) 2))))

(defthm floor-of-logxor-and-expt
  (implies (and (integerp i)
                (integerp j)
                (natp n))
           (equal (floor (logxor i j) (expt 2 n))
                  (logxor (floor i (expt 2 n))
                          (floor j (expt 2 n)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (logxor logeqv logorc1 expt floor-of-logxor-by-2-back)
                           (floor-of-logxor-by-2 expt-hack)))))

(defthm logxor-cancel
  (implies (and (integerp i)
                (integerp j)
                (integerp k))
           (equal (equal (logxor i j) (logxor i k))
                  (equal j k)))
  :hints (("Goal" :use ((:instance logxor-same-2 (i i) (j j))
                        (:instance logxor-same-2 (i i) (j k)))
           :in-theory (disable logxor-same-2))))

(defthm logxor-non-negative
  (implies (and (<= 0 i)
                (<= 0 j))
           (<= 0 (logxor i j)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("goal" :in-theory (enable logxor logeqv logorc1))))

(defthm unsigned-byte-p-of-logxor
  (implies (and (unsigned-byte-p n i)
                (unsigned-byte-p n j))
           (unsigned-byte-p n (logxor i j)))
  :hints (("Goal" :in-theory (enable logxor logeqv logorc1))))
