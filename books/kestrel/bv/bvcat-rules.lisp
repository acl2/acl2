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
(include-book "bitand")
(include-book "bitor")
(include-book "bitxor")
(include-book "bvplus")
(include-book "bvmult")
(include-book "bvminus")
(include-book "bvuminus")
(include-book "bvif")
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))

(defthm bvand-of-bvcat-low-arg2
  (implies (and (<= size lowsize)
                (natp size)
                (natp lowsize))
           (equal (bvand size (bvcat highsize highval lowsize lowval) x)
                  (bvand size lowval x)))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-of-bvcat-low-arg3
  (implies (and (<= size lowsize)
                (natp size)
                (natp lowsize))
           (equal (bvand size x (bvcat highsize highval lowsize lowval))
                  (bvand size x lowval)))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-of-bvcat-tighten-arg2
  (implies (and (< size (+ lowsize highsize))
                (< lowsize size) ; allow = ?
                (natp size)
                (natp lowsize)
                (natp highsize))
           (equal (bvand size (bvcat highsize highval lowsize lowval) y)
                  (bvand size (bvcat (- size lowsize) highval lowsize lowval) y)))
  :hints (("Goal" :in-theory (e/d (bvand bvcat bvchop-of-logapp-bigger ;bvchop-bvchop
                                         bvchop-of-logapp-bigger)
                                  ()))))

(defthm bvand-of-bvcat-tighten-arg3
  (implies (and (< size (+ lowsize highsize))
                (< lowsize size) ; allow = ?
                (natp size)
                (natp lowsize)
                (natp highsize))
           (equal (bvand size x (bvcat highsize highval lowsize lowval))
                  (bvand size x (bvcat (- size lowsize) highval lowsize lowval))))
  :hints (("Goal" :in-theory (e/d (bvand bvcat bvchop-of-logapp-bigger ;bvchop-bvchop
                                         bvchop-of-logapp-bigger)
                                  ()))))

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
  :hints (("Goal" :in-theory (enable bvcat bvand logtail-of-bvchop-becomes-slice))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvor-of-bvcat-low-arg2
  (implies (and (<= size lowsize)
                (natp size)
                (natp lowsize))
           (equal (bvor size (bvcat highsize highval lowsize lowval) x)
                  (bvor size lowval x)))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-of-bvcat-low-arg3
  (implies (and (<= size lowsize)
                (natp size)
                (natp lowsize))
           (equal (bvor size x (bvcat highsize highval lowsize lowval))
                  (bvor size x lowval)))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-of-bvcat-tighten-arg2
  (implies (and (< size (+ lowsize highsize))
                (< lowsize size)
                (natp size)
                (natp lowsize)
                (natp highsize))
           (equal (bvor size (bvcat highsize highval lowsize lowval) y)
                  (bvor size (bvcat (- size lowsize) highval lowsize lowval) y)))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-of-bvcat-tighten-arg3
  (implies (and (< size (+ lowsize highsize))
                (< lowsize size)
                (natp size)
                (natp lowsize)
                (natp highsize))
           (equal (bvor size x (bvcat highsize highval lowsize lowval))
                  (bvor size x (bvcat (- size lowsize) highval lowsize lowval))))
  :hints (("Goal" :in-theory (enable bvor))))

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
  :hints (("Goal" :in-theory (enable bvcat bvor logtail-of-bvchop-becomes-slice))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(defthm bvxor-of-bvcat-tighten-arg2
  (implies (and (< size (+ lowsize highsize))
                (< lowsize size)
                (natp size)
                (natp lowsize)
                (natp highsize))
           (equal (bvxor size (bvcat highsize highval lowsize lowval) y)
                  (bvxor size (bvcat (- size lowsize) highval lowsize lowval) y)))
  :hints (("Goal" :in-theory (enable bvxor))))

(defthm bvxor-of-bvcat-tighten-arg3
  (implies (and (< size (+ lowsize highsize))
                (< lowsize size)
                (natp size)
                (natp lowsize)
                (natp highsize))
           (equal (bvxor size x (bvcat highsize highval lowsize lowval))
                  (bvxor size x (bvcat (- size lowsize) highval lowsize lowval))))
  :hints (("Goal" :in-theory (enable bvxor))))

;; (defthmd bvxor-of-bvcat-arg2
;;   (implies (and (equal size (+ lowsize highsize))
;;                 (natp lowsize)
;;                 (natp highsize))
;;            (equal (bvxor size (bvcat highsize highval lowsize lowval) x)
;;                   (bvcat highsize
;;                          (bvxor highsize (slice (+ -1 size) lowsize x) highval)
;;                          lowsize
;;                          (bvxor lowsize x lowval)))))

;; Do we want this enabled?
(defthm bvxor-of-bvcat-arg2
  (implies (and (<= size (+ highsize lowsize))
                (<= lowsize size)
                (natp highsize)
                (natp size)
                (natp lowsize))
           (equal (bvxor size (bvcat highsize highval lowsize lowval) y)
                  (bvcat (- size lowsize)
                         (bvxor (- size lowsize) highval (slice (+ -1 size) lowsize y))
                         lowsize
                         (bvxor lowsize lowval y)))))

(defthmd bvxor-of-bvcat-arg3
  (implies (and (equal size (+ lowsize highsize)) ;gen?
                (natp size)
                (natp lowsize)
                (natp highsize))
           (equal (bvxor size x (bvcat highsize highval lowsize lowval))
                  (bvcat highsize
                         (bvxor highsize (slice (+ -1 size) lowsize x) highval)
                         lowsize
                         (bvxor lowsize (bvchop lowsize x) lowval)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bitand-of-bvcat-low-arg1
  (implies (and (< 0 lowsize)
                (integerp lowsize)
                (natp highsize))
           (equal (bitand (bvcat highsize highval lowsize lowval) x)
                  (bitand lowval x)))
  :hints (("Goal" :in-theory (e/d (bitand bvand) (bvand-1-becomes-bitand)))))

(defthm bitand-of-bvcat-low-arg2
  (implies (and (< 0 lowsize)
                (integerp lowsize)
                (natp highsize))
           (equal (bitand x (bvcat highsize highval lowsize lowval))
                  (bitand x lowval)))
  :hints (("Goal" :in-theory (e/d (bitand bvand) (bvand-1-becomes-bitand)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bitor-of-bvcat-low-arg1
  (implies (and (< 0 lowsize)
                (integerp lowsize)
                (natp highsize))
           (equal (bitor (bvcat highsize highval lowsize lowval) x)
                  (bitor lowval x)))
  :hints (("Goal" :in-theory (enable bitor))))

(defthm bitor-of-bvcat-low-arg2
  (implies (and (< 0 lowsize)
                (integerp lowsize)
                (natp highsize))
           (equal (bitor x (bvcat highsize highval lowsize lowval))
                  (bitor x lowval)))
  :hints (("Goal" :in-theory (enable bitor))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bitxor-of-bvcat-low-arg1
  (implies (posp lowsize)
           (equal (bitxor (bvcat highsize highval lowsize lowval) x)
                  (bitxor lowval x))))

(defthm bitxor-of-bvcat-low-arg2
  (implies (posp lowsize)
           (equal (bitxor x (bvcat highsize highval lowsize lowval))
                  (bitxor x lowval))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvplus-of-bvcat-low-arg2
  (implies (and (<= size2 size)
                (natp size2)
                (integerp size))
           (equal (bvplus size2 (bvcat n z size y) x)
                  (bvplus size2 y x)))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm bvplus-of-bvcat-low-arg3
  (implies (and (<= size2 size)
                (natp size2)
                (integerp size))
           (equal (bvplus size2 x (bvcat n z size y))
                  (bvplus size2 x y)))
  :hints (("Goal" :in-theory (enable bvplus))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvmult-of-bvcat-low-arg3
  (implies (and (<= size2 size)
                (natp size2)
                (integerp size)
                (natp n)
                )
           (equal (bvmult size2 x (bvcat n z size y))
                  (bvmult size2 x y)))
  :hints (("Goal"
           :use ((:instance BVMULT-OF-BVCHOP-arg2
                            (size size2)
                            (x (bvcat n z size y))
                            (y x))
                 (:instance BVMULT-OF-BVCHOP-arg2
                            (size size2)
                            (x y)
                            (y x)))
           :in-theory (e/d ( ;bvmult
                            ) (BVMULT-OF-BVCHOP-arg2
                            BVMULT-OF-BVCHOP-arg3
                            )))))

(defthm bvmult-of-bvcat-low-arg2
  (implies (and (<= size2 size)
                (natp size2)
                (natp n)
                (integerp size))
           (equal (bvmult size2 (bvcat n z size y) x)
                  (bvmult size2 y x)))
  :hints (("Goal"
           :use (:instance bvmult-of-bvcat-low-arg3)
           :in-theory (disable bvmult-of-bvcat-low-arg3))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvminus-of-bvcat-low-arg2
  (implies (and (<= size2 size)
                (natp size2)
                (integerp size))
           (equal (bvminus size2 (bvcat n z size y) x)
                  (bvminus size2 y x)))
  :hints (("Goal" :in-theory (enable bvminus bvplus bvchop-when-i-is-not-an-integer))))

(defthm bvminus-of-bvcat-low-arg3
   (implies (and (<= size2 size)
                 (natp size2)
                 (integerp size))
            (equal (bvminus size2 x (bvcat n z size y))
                   (bvminus size2 x y)))
   :hints (("Goal"
            :use ((:instance bvchop-of-minus-of-bvchop
                            (size size2)
                            (x (bvcat n z size (ifix y))))
                  (:instance bvchop-of-minus-of-bvchop
                            (size size2)
                            (x y)))
            :in-theory (e/d (bvminus bvplus bvchop-when-i-is-not-an-integer) (bvchop-of-minus-of-bvchop
                                                                              ;;bvchop-of-minus-of-bvchop-gen
                                                                              )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvuminus-of-bvcat-low
  (implies (and (<= size lowsize)
                (natp size)
                (integerp lowsize))
           (equal (bvuminus size (bvcat highsize highval lowsize lowval))
                  (bvuminus size lowval)))
  :hints (("Goal" :in-theory (enable bvuminus))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvif-of-bvcat-low-arg3
  (implies (and (<= size lowsize)
                (natp size)
                (natp lowsize))
           (equal (bvif size test (bvcat highsize highval lowsize lowval) y)
                  (bvif size test lowval y)))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm bvif-of-bvcat-low-arg4
  (implies (and (<= size lowsize)
                (natp size)
                (natp lowsize))
           (equal (bvif size test x (bvcat highsize highval lowsize lowval))
                  (bvif size test x lowval)))
  :hints (("Goal" :in-theory (enable bvif myif))))
