; Rules about ash and the BV functions
;
; Copyright (C) 2017-2021 Kestrel Technology, LLC
; Copyright (C) 2022-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book mixes ASH with BV functions.  For other theorems about ASH, see
;; ../arithmetic-light/ash.lisp

(include-book "bv-syntax")
(include-book "slice-def")
(include-book "bvcat-def")
(include-book "bvshr-def")
(local (include-book "bvcat"))
(local (include-book "slice"))
(local (include-book "unsigned-byte-p"))
(local (include-book "rules")) ; todo, for logtail-becomes-slice-bind-free
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/divide" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/ash" :dir :system))

;move
(defthm unsigned-byte-p-shift-lemma
  (implies (and (natp n)
                (unsigned-byte-p xsize x)
                (<= n xsize))
           (unsigned-byte-p (- xsize n) (floor (* x (expt 2 (- n))) 1)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm slice-of-ash
  (implies (and (<= n low)
                (integerp low)
                (integerp high)
                (natp n))
           (equal (slice high low (ash x n))
                  (slice (- high n) (- low n) x)))
  :hints (("Goal" :in-theory (enable ash slice logtail ;floor
                                     expt-of-+))))

;can't just turn ash into slice because we don't know what the top bit is, so
;we need the overarching slice.
(defthm slice-of-ash-right
  (implies (and (< n 0)
                (natp low)
                (natp high)
                (integerp n))
           (equal (slice high low (ash x n))
                  (slice (+ high (- n)) (+ low (- n)) x)))
  :hints (("Goal" :in-theory (enable ash slice logtail ;floor
                                     ifix
                                     expt-of-+))))

(defthm slice-of-ash-same
  (implies (and (natp high)
                (natp low))
           (equal (slice high low (ash x low))
                  (bvchop (+ 1 (- high low)) x)))
  :hints (("Goal" :cases ((<= n 0)))))

(defthmd logtail-becomes-ash
  (implies (natp n)
           (equal (logtail n x)
                  (ash x (- n))))
  :hints (("Goal" :in-theory (enable logtail ash))))

(defthmd ash-becomes-logtail
  (implies (and (<= n 0)
                (integerp n))
           (equal (ash x n)
                  (logtail (- n) x)))
  :hints (("Goal" :use (:instance logtail-becomes-ash (n (- n))))))

(theory-invariant (incompatible (:rewrite ash-becomes-logtail)
                                (:rewrite logtail-becomes-ash)))

(local
  (defthm ash-negative-becomes-slice-helper
    (implies (and (< n 0)
                  (bind-free (bind-var-to-bv-term-size 'xsize x))
                  (unsigned-byte-p xsize x)
                  (<= (- n) xsize) ; dropped below
                  (integerp n))
             (equal (ash x n)
                    (slice (+ -1 xsize) (- n) x)))
    :hints (("Goal" :use (:instance unsigned-byte-p-shift-lemma (n (- n)))
             :in-theory (enable ash-becomes-logtail slice logtail unsigned-byte-p)))))

(defthmd ash-negative-becomes-slice
  (implies (and (< n 0)
                (bind-free (bind-var-to-bv-term-size 'xsize x))
                (unsigned-byte-p xsize x)
                (integerp n))
           (equal (ash x n)
                  (slice (+ -1 xsize) (- n) x)))
  :hints (("Goal" :in-theory (disable ash-negative-becomes-slice-helper
                                      ;<-of-*-and-0
                                      ash)
           :use ash-negative-becomes-slice-helper)))

(defthm ash-becomes-bvcat
  (implies (and (bind-free (bind-var-to-bv-term-size 'xsize x)) ;only works for constant size?
                (force (unsigned-byte-p xsize x))
                (natp amt))
           (equal (ash x amt)
                  (bvcat (+ xsize amt) x amt 0)))
  :hints (("Goal" :in-theory (enable bvcat ash))))

;rename
(defthm bvchop-of-ash
  (implies (and (natp size)
                (natp n))
           (equal (bvchop size (ash x n))
                  (bvcat (- size n) x n 0)))
  :hints (("Goal" :in-theory (enable ash slice logtail))))

(defthm bvchop-of-ash-when-negative-becomes-bvshr
  (implies (and (< c 0)
                (integerp c)
                (natp places))
           (equal (bvchop places (ash i c))
                  (bvshr (- places c) i (- c))))
  :hints (("Goal" :in-theory (e/d (ash bvshr slice logtail ifix)
                                  (acl2::bvchop-of-logtail-becomes-slice acl2::floor-of-2-becomes-logtail-of-1)))))

(defthm bvchop-of-ash-right-shift
  (implies (and (< n 0)
                (natp size)
                (integerp n))
           (equal (bvchop size (ash x n))
                  (slice (+ -1 size (- n)) (- n) x)))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (e/d (ash slice logtail ifix)
                           (acl2::bvchop-of-logtail-becomes-slice)))))

(defthm ash-of-if
  (equal (ash (if test i1 i2) c)
         (if test
             (ash i1 c)
           (ash i2 c))))

;gen the -1
(defthm ash-of-bvchop-32-and-minus1
  (equal (ash (bvchop 32 x) -1)
         (slice 31 1 x))
  :hints (("Goal" :in-theory (enable ash logtail-becomes-slice-bind-free floor-of-2-becomes-logtail-of-1))))

(defthm ash-of-ones
  (implies (and (natp n)
                (natp low))
           (equal (ASH (+ -1 (EXPT 2 n)) LOW)
                  (bvcat n (+ -1 (EXPT 2 n))
                               low 0)))
  :hints (("Goal" :in-theory (e/d (bvcat ash BVUMINUS BVMINUS)
                                  (;BVPLUS-OF-UNARY-MINUS-ARG2
                                   BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

(defthm ash-of-bvcat
  (implies (and (natp lowsize)
                (natp highsize)
                (natp amt))
           (equal (ash (bvcat highsize highval lowsize lowval) amt)
                  (bvcat (+ lowsize highsize)
                         (bvcat highsize highval lowsize lowval)
                         amt
                         0)))
  :hints (("Goal" :cases ((and (equal 0 lowsize) (equal 0 highsize))
                          (and (not (equal 0 lowsize)) (equal 0 highsize))
                          (and (equal 0 lowsize) (not (equal 0 highsize))))
           :in-theory (enable ash))))
