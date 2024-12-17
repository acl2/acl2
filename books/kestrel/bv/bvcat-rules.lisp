; Rules that deal with both bvcat and other operations
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvcat")
(include-book "bvxor")
(include-book "bvor")
(include-book "bitnot")
(include-book "bvand")
(include-book "bitand")
(include-book "bitor")
(include-book "bitxor")
(include-book "bvplus")
(include-book "bvmult")
(include-book "bvminus")
(include-book "bvuminus")
(include-book "bvif")
(local (include-book "logapp"))
(local (include-book "logand-b"))
(local (include-book "logior-b"))
(local (include-book "logxor-b"))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

;; rules about bitnot/bvnot and bvcat:

;why didn't the trim rule work?
(defthm bvnot-of-bvcat-trim
  (implies (natp low)
           (equal (bvnot low (bvcat width x low y))
                  (bvnot low y)))
  :hints (("Goal"
           :use ((:instance bvchop-lognot-bvchop
                            (n low)
                            (x (bvcat width x low y)))
                 (:instance bvchop-lognot-bvchop
                            (n low)
                            (x y)))
           :in-theory (e/d (bvnot) (bvchop-lognot-bvchop ; are these 2 the same?
                                    bvchop-of-lognot-of-bvchop)))))

(defthmd bvcat-of-bitnot-and-bitnot
  (equal (bvcat 1 (bitnot x) 1 (bitnot y))
         (bvnot 2 (bvcat 1 x 1 y))))

(defthmd bvcat-of-bvnot-and-bitnot
  (implies (natp size)
           (equal (bvcat size (bvnot size x) 1 (bitnot y))
                  (bvnot (+ 1 size) (bvcat size x 1 y))))
  :hints (("Goal" :cases ((equal 0 size)))))

(defthmd bvcat-of-bitnot-and-bvnot
  (implies (natp size)
           (equal (bvcat 1 (bitnot x) size (bvnot size y))
                  (bvnot (+ 1 size) (bvcat 1 x size y)))))

(defthmd bvcat-of-bvnot-and-bvnot
  (implies (and (posp highsize) ;why not 0?
                (posp lowsize) ;why not 0?
                )
           (equal (bvcat highsize (bvnot highsize highval) lowsize (bvnot lowsize lowval))
                  (bvnot (+ highsize lowsize) (bvcat highsize highval lowsize lowval)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
  :hints (("Goal" :in-theory (enable bvand bvcat bvchop-of-logapp-bigger ;bvchop-bvchop
                                     bvchop-of-logapp-bigger))))

(defthm bvand-of-bvcat-tighten-arg3
  (implies (and (< size (+ lowsize highsize))
                (< lowsize size) ; allow = ?
                (natp size)
                (natp lowsize)
                (natp highsize))
           (equal (bvand size x (bvcat highsize highval lowsize lowval))
                  (bvand size x (bvcat (- size lowsize) highval lowsize lowval))))
  :hints (("Goal" :in-theory (enable bvand bvcat bvchop-of-logapp-bigger ;bvchop-bvchop
                                     bvchop-of-logapp-bigger))))

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
  :hints (("Goal" :use bvand-of-bvcat-arg3
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
  :hints (("Goal" :use bvor-of-bvcat-arg3
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
           :use bvmult-of-bvcat-low-arg3
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;rename
;bozo gen
;strength reduction from bvmult to shift, so i guess this is a win? unless we are in an arithmetic context?
(defthmd bvmult-of-2
  (implies (natp n)
           (equal (bvmult n 2 x)
                  (bvcat (+ -1 n) x 1 0)))
  :hints (("Goal" :in-theory (e/d (bvmult slice getbit bvcat)
                                  ()))))


;; TODO: organize this stuff:

(defthm bvcat-getbit-slice-same
  (implies (and (equal lowindex (+ 1 bitindex))
                (equal size2 (+ 1 highindex (- lowindex) highsize))
                (<= lowindex highindex) ;bozo
                (natp bitindex)
                (natp highindex)
                (natp lowindex)
                (integerp highval)
                (natp highsize)
                (< 0 highsize)
                (integerp b))
           (equal (bvcat size2 (bvcat highsize highval (+ 1 highindex (- lowindex)) (slice highindex lowindex b)) 1 (getbit bitindex b))
                  (bvcat highsize highval (+ 2 highindex (- lowindex)) (slice highindex bitindex b)))))

(defthm bvcat-slice-getbit-same
  (implies (and (equal (+ 1 highindex) bitindex)
                (equal size2 (+ 1 highindex (- lowindex)))
                (<= lowindex highindex) ;bozo
                (natp bitindex)
                (natp highindex)
                (natp lowindex)
                (integerp highval)
                (natp highsize)
                (< 0 highsize)
                (integerp b))
           (equal (bvcat (+ 1 highsize) (bvcat highsize highval 1 (getbit bitindex b)) size2 (slice highindex lowindex b))
                  (bvcat highsize highval (+ 1 bitindex (- lowindex)) (slice bitindex lowindex b)))))

(defthm bvcat-slice-slice-same
  (implies (and (equal (+ -1 lowindex2) highindex1)
                (equal size1 (+ 1 highindex1 (- lowindex1)))
                (equal size2 (+ 1 highindex2 (- lowindex2)))
                (equal size3 (+ size2 highsize))
                (<= lowindex2 highindex2) ;bozo
                (<= lowindex1 highindex1) ;bozo
                (natp highindex1)
                (natp lowindex1)
                (natp highindex2)
                (natp lowindex2)
                (integerp highval)
                (natp highsize)
                (< 0 highsize)
                (integerp b))
           (equal (bvcat size3 (bvcat highsize highval size2 (slice highindex2 lowindex2 b)) size1 (slice highindex1 lowindex1 b))
                  (bvcat highsize highval (+ 1 highindex2 (- lowindex1)) (slice highindex2 lowindex1 b))
                  )))

;; tightens the upper size
;use a more general rule?
(defthm bvcat-tighten
  (implies (and (< (+ lowsize highsize) size)
                (< 0 highsize) ;bozo
                (natp size)
                (natp lowsize)
                (natp highsize)
                (natp lowsize2)
                ;;(integerp x)
                ;;(integerp y)
                ;;(integerp z)
                )
           (equal (bvcat size (bvcat highsize x lowsize z) lowsize2 y)
                  (bvcat (+ lowsize highsize) (bvcat highsize x lowsize z) lowsize2 y)))
  :hints (("Goal" :cases ((and (integerp z) (integerp y))
                          (and (integerp z) (not (integerp y)))
                          (and (not (integerp z)) (integerp y)))
           :in-theory (e/d (bvcat) ()))))

;move
(DEFTHM BVCAT-SLICE-SLICE-SAME-2
  (IMPLIES (AND (EQUAL LOWINDEX2 size1)
                (EQUAL SIZE2 (+ 1 HIGHINDEX2 (- LOWINDEX2)))
                (EQUAL SIZE3 (+ SIZE2 HIGHSIZE))
                (<= LOWINDEX2 HIGHINDEX2)
                (natp size1)
                (NATP HIGHINDEX2)
                (NATP LOWINDEX2)
                (INTEGERP HIGHVAL)
                (NATP HIGHSIZE)
                (< 0 HIGHSIZE)
                (INTEGERP B))
           (EQUAL (bvcat
                   SIZE3
                   (bvcat
                    HIGHSIZE HIGHVAL SIZE2 (SLICE HIGHINDEX2 LOWINDEX2 B)) SIZE1 B)
                  (bvcat
                   HIGHSIZE HIGHVAL (+ 1 HIGHINDEX2 0)
                   (SLICE HIGHINDEX2 0 B))))
  :hints (("Goal" :use (:instance BVCAT-SLICE-SLICE-SAME (lowindex1 0) (highindex1 (+ -1 size1)))
           :in-theory (disable BVCAT-SLICE-SLICE-SAME))))

(defthm bvcat-of-slice-tighten
  (implies (and (<= highsize (- high low))
                ;; (<= low high)
                (natp highsize)
                (natp low)
                (natp high))
           (equal (bvcat highsize (slice high low x) lowsize lowval)
                  (bvcat highsize (slice (+ -1 low highsize) low x) lowsize lowval))))
