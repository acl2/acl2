; BV Library: rules about unsigned-byte-p-forced
;
; Copyright (C) 2024-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "unsigned-byte-p-forced")
(include-book "bvshr-def")
(include-book "bvshl-def")
(include-book "bool-to-bit-def")
(include-book "defs")
(local (include-book "bvshr"))
(local (include-book "bvshl"))
(local (include-book "bvchop"))
(local (include-book "bvand"))
(local (include-book "bvor"))
(local (include-book "bvxor"))
(local (include-book "bvnot"))
(local (include-book "bvplus"))
(local (include-book "bvmult"))
(local (include-book "bvmod"))
(local (include-book "bvcat"))
(local (include-book "bvlt"))
(include-book "leftrotate32") ; pull out the def?
(include-book "rightrotate32") ; pull out the def?
(local (include-book "bvsx"))
(local (include-book "repeatbit"))
(local (include-book "unsigned-byte-p"))

(local (in-theory (disable unsigned-byte-p)))

(defthm unsigned-byte-p-forced-of-bvchop
  (equal (unsigned-byte-p-forced size (bvchop size x))
         (natp size))
  :hints (("Goal"
           :in-theory (enable unsigned-byte-p-forced bvchop-when-i-is-not-an-integer natp)
           :cases ((integerp size)))))

(defthm unsigned-byte-p-forced-of-bvand
  (equal (unsigned-byte-p-forced size (bvand size x y))
         (natp size))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-bvor
  (equal (unsigned-byte-p-forced size (bvor size x y))
         (natp size))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-bvxor
  (equal (unsigned-byte-p-forced size (bvxor size x y))
         (natp size))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-bvnot
  (equal (unsigned-byte-p-forced size (bvnot size x))
         (natp size))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-bvplus
  (equal (unsigned-byte-p-forced size (bvplus size x y))
         (natp size))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-bvmult
  (equal (unsigned-byte-p-forced size (bvmult size x y))
         (natp size))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-bvdiv
  (equal (unsigned-byte-p-forced size (bvdiv size x y))
         (natp size))
  :hints (("Goal" :in-theory (enable bvdiv unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-bvmod
  (equal (unsigned-byte-p-forced size (bvmod size x y))
         (natp size))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-bvminus
  (equal (unsigned-byte-p-forced size (bvminus size x y))
         (natp size))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-bvuminus
  (equal (unsigned-byte-p-forced size (bvuminus size x))
         (natp size))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-bvif
  (equal (unsigned-byte-p-forced size (bvif size test x y))
         (natp size))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced bvif))))

(defthm unsigned-byte-p-forced-of-if
  (equal (unsigned-byte-p-forced size (if test x y))
         (if test
             (unsigned-byte-p-forced size x)
           (unsigned-byte-p-forced size y))))

(defthm unsigned-byte-p-forced-of-slice
  (implies (and (equal size (+ 1 high (- low)))
                (integerp low)
                (integerp high))
           (equal (unsigned-byte-p-forced size (slice high low x))
                  (natp size)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-bvcat
  (implies (and (equal size (+ highsize lowsize))
                (natp lowsize)
                (natp highsize))
           (unsigned-byte-p-forced size (bvcat highsize highval lowsize lowval)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

;will we really be trimming a 1-bit quantitiy down to 0 bits? maybe the trim rule can be simplified and sped up. fixme
(defthm unsigned-byte-p-forced-of-getbit
  (unsigned-byte-p-forced 1 (getbit n x))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-bitnot
  (unsigned-byte-p-forced 1 (bitnot x))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-bitor
  (unsigned-byte-p-forced 1 (bitor x y))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-bitxor
  (unsigned-byte-p-forced 1 (bitxor x y))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-bitand
  (unsigned-byte-p-forced 1 (bitand x y))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-leftrotate
  (implies (natp width)
           (unsigned-byte-p-forced width (leftrotate width amt val)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-rightrotate
  (implies (natp width)
           (unsigned-byte-p-forced width (rightrotate width amt val)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-leftrotate32
  (unsigned-byte-p-forced 32 (leftrotate32 amt val))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-rightrotate32
  (unsigned-byte-p-forced 32 (rightrotate32 amt val))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-bvsx
  (implies (and (posp oldsize) ;gen?
                (<= oldsize size)
                (natp size))
           (unsigned-byte-p-forced size (bvsx size oldsize x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-repeatbit
  (implies (natp n)
           (unsigned-byte-p-forced n (repeatbit n bit)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-bool-to-bit
  (unsigned-byte-p-forced 1 (bool-to-bit x))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-bvshr
  (implies (natp size)
           (unsigned-byte-p-forced size (bvshr size x amt)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

(defthm unsigned-byte-p-forced-of-bvshl
  (implies (natp size)
           (unsigned-byte-p-forced size (bvshl size x amt)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))
