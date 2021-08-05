; Rules that deal with both bvcat and other operations
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvcat")
(include-book "bvxor")
(include-book "bvor")
(include-book "bvand")
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))

(defthm bvxor-of-bvcat-low-arg2
  (implies (and (<= size lowsize)
                (natp size)
                (natp lowsize))
           (equal (bvxor size (bvcat highsize highval lowsize lowval) x)
                  (bvxor size lowval x))))

(defthm bvxor-of-bvcat-low-arg3
  (implies (and (<= size lowsize)
                (natp size)
                (natp lowsize))
           (equal (bvxor size x (bvcat highsize highval lowsize lowval))
                  (bvxor size x lowval))))

(defthmd bvxor-of-bvcat
  (implies (and (equal size (+ lowsize highsize)) ;gen?
                (natp size)
                (natp lowsize)
                (natp highsize))
           (equal (bvxor size x (bvcat highsize highval lowsize lowval))
                  (bvcat highsize
                         (bvxor highsize (slice (+ -1 size) lowsize x) highval)
                         lowsize
                         (bvxor lowsize (bvchop lowsize x) lowval))))
  :hints (("Goal" :in-theory (e/d (bvcat bvxor LOGTAIL-OF-BVCHOP-BECOMES-SLICE)
                                  ()))))

(defthmd bvxor-of-bvcat-alt
  (implies (and (equal size (+ lowsize highsize))
                (natp lowsize)
                (natp highsize))
           (equal (bvxor size (bvcat highsize highval lowsize lowval) x)
                  (bvcat highsize
                         (bvxor highsize (slice (+ -1 size) lowsize x) highval)
                         lowsize
                         (bvxor lowsize (bvchop lowsize x) lowval))))
  :hints (("Goal" :use (:instance bvxor-of-bvcat)
           :in-theory (disable bvxor-of-bvcat))))

(defthm bvor-of-bvcat-low-arg2
  (implies (and (<= size lowsize)
                (natp size)
                (natp lowsize))
           (equal (bvor size (bvcat highsize highval lowsize lowval) x)
                  (bvor size lowval x)))
  :hints (("Goal" :in-theory (e/d (bvor) ()))))

(defthm bvor-of-bvcat-low-arg3
  (implies (and (<= size lowsize)
                (natp size)
                (natp lowsize))
           (equal (bvor size x (bvcat highsize highval lowsize lowval))
                  (bvor size x lowval)))
  :hints (("Goal" :in-theory (e/d (bvor) ()))))

(defthmd bvor-of-bvcat-arg3
  (implies (and (equal size (+ lowsize highsize)) ;gen?
                (natp size)
                (natp lowsize)
                (natp highsize))
           (equal (bvor size x (bvcat highsize highval lowsize lowval))
                  (bvcat highsize
                         (bvor highsize (slice (+ -1 size) lowsize x) highval)
                         lowsize
                         (bvor lowsize (bvchop lowsize x) lowval))))
  :hints (("Goal" :in-theory (e/d (bvcat bvor logtail-of-bvchop-becomes-slice) ()))))

(defthmd bvor-of-bvcat-arg2
  (implies (and (equal size (+ lowsize highsize)) ;gen?
                (natp size)
                (natp lowsize)
                (natp highsize))
           (equal (bvor size (bvcat highsize highval lowsize lowval) x)
                  (bvcat highsize
                         (bvor highsize (slice (+ -1 size) lowsize x) highval)
                         lowsize
                         (bvor lowsize (bvchop lowsize x) lowval))))
  :hints (("Goal" :use (:instance bvor-of-bvcat-arg3)
           :in-theory (disable bvor-of-bvcat-arg3))))

(defthm bvand-of-bvcat-low-arg2
  (implies (and (<= size lowsize)
                (natp size)
                (natp lowsize))
           (equal (bvand size (bvcat highsize highval lowsize lowval) x)
                  (bvand size lowval x)))
  :hints (("Goal" :in-theory (e/d (bvand) ()))))

(defthm bvand-of-bvcat-low-arg3
  (implies (and (<= size lowsize)
                (natp size)
                (natp lowsize))
           (equal (bvand size x (bvcat highsize highval lowsize lowval))
                  (bvand size x lowval)))
  :hints (("Goal" :in-theory (e/d (bvand) ()))))

(defthmd bvand-of-bvcat-arg3
  (implies (and (equal size (+ lowsize highsize)) ;gen?
                (natp size)
                (natp lowsize)
                (natp highsize))
           (equal (bvand size x (bvcat highsize highval lowsize lowval))
                  (bvcat highsize
                         (bvand highsize (slice (+ -1 size) lowsize x) highval)
                         lowsize
                         (bvand lowsize (bvchop lowsize x) lowval))))
  :hints (("Goal" :in-theory (e/d (bvcat bvand logtail-of-bvchop-becomes-slice) ()))))

(defthmd bvand-of-bvcat-arg2
  (implies (and (equal size (+ lowsize highsize)) ;gen?
                (natp size)
                (natp lowsize)
                (natp highsize))
           (equal (bvand size (bvcat highsize highval lowsize lowval) x)
                  (bvcat highsize
                         (bvand highsize (slice (+ -1 size) lowsize x) highval)
                         lowsize
                         (bvand lowsize (bvchop lowsize x) lowval))))
  :hints (("Goal" :use (:instance bvand-of-bvcat-arg3)
           :in-theory (disable bvand-of-bvcat-arg3))))

(defthm bvand-of-bvcat-gen
  (implies (and (< 0 size2)
                (<= (+ -1 size2) size)
                (< lowsize size2)
                (< 0 lowsize)
                (natp lowsize)
                (integerp x)
                (integerp y)
                (integerp z)
                (natp size)
                (natp size2)
                )
           (equal (bvand size2 (bvcat size y lowsize x) z)
                  (bvcat (- size2 lowsize)
                         (bvand (- size2 lowsize) y (slice (+ -1 size2) lowsize z))
                         lowsize
                         (bvand lowsize x z))))
  :hints (("Goal" :in-theory (enable bvand))))
