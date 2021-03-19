; Mixed theorems about bit-vectors
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Organize these

(include-book "bv-syntax")
(include-book "bvmult")
(include-book "logext")
(include-book "rules") ;for anti-slice
(include-book "unsigned-byte-p") ;for unsigned-byte-p-forced
(local (include-book "kestrel/library-wrappers/arithmetic-inequalities" :dir :system))
(local (include-book "arith"))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
(local (include-book "kestrel/library-wrappers/ihs-quotient-remainder-lemmas" :dir :system)) ;drop
(local (include-book "kestrel/library-wrappers/ihs-logops-lemmas" :dir :system)) ;drop

(defthm bvmult-tighten
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'xsize x))
                (bind-free (bind-var-to-unsigned-term-size 'ysize y))
                (< (+ xsize ysize) size)
                (natp size)
                (force (unsigned-byte-p-forced xsize x))
                (force (unsigned-byte-p-forced ysize y))
                )
           (equal (bvmult size x y)
                  (bvmult (+ xsize ysize) x y)))
  :hints (("Goal" :in-theory (enable UNSIGNED-BYTE-P-FORCED bvmult))))

(defthmd floor-when-usb-bind-free
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'xsize x) (xsize))
                (natp n)
                (unsigned-byte-p-forced xsize x))
           (equal (floor x (expt 2 n))
                  (slice (+ -1 xsize) n x)))
  :hints
  (("Goal" :expand ((slice (+ -1 xsize) n x))
    :in-theory (e/d (unsigned-byte-p-forced
                     natp slice
                     logtail unsigned-byte-p ;floor-bounded-by-/
                     )
                    (anti-slice bvchop-of-floor-of-expt-of-2)))))

;bozo do stuff like this better?
(defthm logapp-of-bvif
  (implies (and (integerp size)
                (integerp a)
                (integerp b)
                (< 0 size))
           (equal (logapp lowsize lowval (bvif size test a b))
                  (BVCAT SIZE (BVIF SIZE TEST A B)
                         LOWSIZE LOWVAL)))
  :hints (("Goal" :in-theory (e/d (bvcat bvif) ()))))

;; (thm
;;  (implies (natp n)
;;           (equal (MOD (EXPT 2 N) 2)
;;                  (if (equal 0 n)
;;                      1
;;                    0)))
;;  :hints (("Goal" :in-theory (enable expt))))

;compare to logand-of-minus-of-expt
(defthmd logand-of-minus-of-expt2
  (implies (and (integerp a)
                (natp n))
           (equal (logand (- (expt 2 n)) a)
                  (* (expt 2 n) (floor a (expt 2 n)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand (logand a (- (expt 2 n)))
           :in-theory (e/d (logand* logcdr ;fl
                                    expt-of-+ mod-expt-split)
                           (MOD-OF-EXPT-OF-2-CONSTANT-VERSION ;why?
                            ))
           :induct (sub1-logcdr-induction-1 n a))))

;drop these special cases:
(defthm logand-minus-128-hack
  (implies (integerp a)
           (equal (logand -128 a)
                  (logapp 7 0 (logtail 7 a))))
  :hints (("Goal" :use (:instance logand-of-minus-of-expt2 (n 7))
           :in-theory (e/d (logtail)( logand-of-minus-of-expt2)))))

(defthm logand-minus-64-hack
  (implies (integerp a)
           (equal (logand -64 a)
                  (logapp 6 0 (logtail 6 a))))
  :hints (("Goal" :use (:instance logand-of-minus-of-expt2 (n 6))
           :in-theory (e/d (logtail)( logand-of-minus-of-expt2)))))

(defthm logand-minus-32-hack
  (implies (integerp a)
           (equal (logand -32 a)
                  (logapp 5 0 (logtail 5 a))))
  :hints (("Goal" :use (:instance logand-of-minus-of-expt2 (n 5))
           :in-theory (e/d (logtail)( logand-of-minus-of-expt2)))))

;move
;rename?
(defthm bvxor-of-negative-constant
  (implies (and (syntaxp (and (quotep size)
                              (quotep x)
                              (not (unsigned-byte-p (unquote size) (unquote x)))))
                (integerp size)
                (< 0 size)
                (integerp x)
                (integerp y)
                )
           (equal (BVXOR size x y)
                  (bvxor size (bvchop size x) y)))
  :hints (("Goal" :in-theory (enable bvxor))))

;use trim?
(defthm bvand-logapp-lemma
  (implies (and (< lowsize size1) ;bozo gen
                (< size1 (+ lowsize highsize))
                (natp size1)
                (natp lowsize)
                (natp highsize)
                (integerp x)
                (integerp y)
                (integerp z))
           (equal (bvand size1 x (bvcat highsize z lowsize y))
                  (bvand size1 x (bvcat (- size1 lowsize) z lowsize y))))
  :hints (("Goal" :in-theory (e/d (bvand bvcat bvchop-of-logapp-bigger ;bvchop-bvchop
                                         BVCHOP-OF-LOGAPP-BIGGER)
                                  ( )))))

(defthm bvcat-of-bvxor-tighten-2
  (implies (and (< size1 size2)
                (natp size1)
                (natp size2)
                (integerp x)
                (integerp z)
                (integerp y))
           (equal (bvcat size1 (bvxor size2 z y) lowsize x)
                  (bvcat size1 (bvxor size1 z y) lowsize x)))
  :hints (("Goal" :in-theory (e/d (bvcat) ()))))

(defthm bvxor-of-slice-tighten
  (implies (and (<= size (- high low))
                (natp size)
                (< 0 size)
                (natp low)
                (natp high)
                )
           (equal (bvxor size x (slice high low y))
                  (bvxor size x (slice (+ low size -1) low y))))
  :hints (("Goal" :in-theory (e/d (bvxor) (logxor-bvchop-bvchop)))))

(defthm bvxor-of-slice-tighten-alt
  (implies (and (<= size (- high low))
                (natp size)
                (< 0 size)
                (natp low)
                (natp high)
;                (integerp x)
 ;               (integerp y)
                )
           (equal (bvxor size (slice high low y) x)
                  (bvxor size (slice (+ low size -1) low y) x)))
  :hints (("Goal" :in-theory (e/d (bvxor) (logxor-bvchop-bvchop)))))

(in-theory (disable bvxor-trim-arg2 bvxor-trim-arg1)) ;bozo

(defthm bvxor-of-bvcat-gen
  (implies (and (<= (+ -1 size2) size)
                (< lowsize size2)
                (< 0 lowsize)
                (integerp x)
                (integerp y)
                (integerp z)
                (natp size)
                (natp size2)
                (natp lowsize)
                )
           (equal (bvxor size2 (bvcat size y lowsize x) z)
                  (bvcat (- size2 lowsize)
                         (bvxor (- size2 lowsize) y (slice (+ -1 size2) lowsize z))
                         lowsize
                         (bvxor lowsize x z)))))

(defthm bvxor-of-bvchop-tighten-2
   (implies (and (< size1 size2)
                 (natp size1)
                 (natp size2)
                 (integerp y)
                 (integerp x))
            (equal (Bvxor size1 x (BVCHOP size2 y))
                   (Bvxor size1 x (BVCHOP size1 y))))
   :hints (("Goal" :in-theory (e/d (bvxor ;bvchop-bvchop
                                    ) (LOGXOR-BVCHOP-BVCHOP)))))

(defthm bvxor-of-bvchop-tighten-1
   (implies (and (< size1 size2)
                 (natp size1)
                 (natp size2)
                 (integerp y)
                 (integerp x))
            (equal (Bvxor size1 (BVCHOP size2 y) x)
                   (Bvxor size1 (BVCHOP size1 y) x)))
   :hints (("Goal" :in-theory (e/d (bvxor ;bvchop-bvchop
                                    ) (LOGXOR-BVCHOP-BVCHOP)))))

;; ;use trim
;; (defthm bvxor-of-bvcat-tighten-low
;;   (implies (and (<= size lowsize)
;;                 (natp size)
;;                 (natp lowsize)
;;                 (natp highsize)
;;                 (integerp x)
;;                 (integerp y)
;;                 (integerp z))
;;            (equal (bvxor size (bvcat highsize y lowsize x) z)
;;                   (bvxor size x z)))
;;   :hints (("Goal" :in-theory (e/d (bvxor)
;;                                   (logxor-bvchop-bvchop)))))

;; ;use trim
;; (defthm bvxor-of-bvcat-tighten-low-alt
;;   (implies (and (<= size lowsize)
;;                 (natp size)
;;                 (natp lowsize)
;;                 (natp highsize)
;;                 (integerp x)
;;                 (integerp y)
;;                 (integerp z))
;;            (equal (bvxor size z (bvcat highsize y lowsize x))
;;                   (bvxor size z x)))
;;   :hints (("Goal" :in-theory (e/d (bvxor)
;;                                   (logxor-bvchop-bvchop)))))

;do we trim logexts?
(defthm bvxor-of-logext
  (implies (and (<= size1 size2)
                (< 0 size2)
                (natp size1)
                (natp size2)
                ;(integerp x)
                ;(integerp y)
                )
           (equal (bvxor size1 (logext size2 x) y)
                  (bvxor size1 x y)))
  :hints (("Goal" :in-theory (e/d (bvxor) (logxor-bvchop-bvchop)))))

(defthm bvxor-of-logext-alt
  (implies (and (<= size1 size2)
                (< 0 size2)
                (natp size1)
                (natp size2)
;                (integerp x)
;                (integerp y)
                )
           (equal (bvxor size1 y (logext size2 x))
                  (bvxor size1 x y)))
  :hints (("Goal" :in-theory (e/d (bvxor) (logxor-bvchop-bvchop)))))

;bozo gen or change the name
;move
(defthm logapp-when-size-is-negative
  (implies (and (< size 0)
                (integerp x))
           (equal (logapp size x 0)
                  0))
  :hints (("Goal" :in-theory (enable logapp))))

(defthm bvand-of-slice-tighten-2
  (implies (and (< size (+ 1 high (- low)))
                (< 0 size)
                (natp size)
                (natp low)
                (natp high)
                (integerp x)
                (integerp y)
                )
           (equal (BVAND size y (SLICE high low x))
                  (BVAND size y (SLICE (+ low size -1) low x))))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-of-slice-tighten-1
  (implies (and (< size (+ 1 high (- low)))
                (< 0 size)
                (natp size)
                (natp low)
                (natp high)
                (integerp x)
                (integerp y)
                )
           (equal (BVAND size (SLICE high low x) y)
                  (BVAND size (SLICE (+ low size -1) low x) y)))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvxor-of-slice-tighten-2
  (implies (and (< size (+ 1 high (- low)))
                (< 0 size)
                (natp size)
                (natp low)
                (natp high)
                (integerp x)
                (integerp y)
                )
           (equal (BVXOR size y (SLICE high low x))
                  (BVXOR size y (SLICE (+ low size -1) low x))))
  :hints (("Goal" :in-theory (e/d (bvxor) (LOGXOR-BVCHOP-BVCHOP)))))

(defthm bvxor-of-slice-tighten-1
  (implies (and (< size (+ 1 high (- low)))
                (< 0 size)
                (natp size)
                (natp low)
                (natp high)
                (integerp x)
                (integerp y)
                )
           (equal (BVXOR size (SLICE high low x) y)
                  (BVXOR size (SLICE (+ low size -1) low x) y)))
  :hints (("Goal" :in-theory (e/d (bvxor) (LOGXOR-BVCHOP-BVCHOP)))))

(in-theory (disable integer-length))




(defthm getbit-of-bvmult-tighten
  (implies (and (< (+ 1 SIZE1) SIZE2)
                (< 0 size2)
                (natp size1)
                (natp size2)
                (integerp x)
                (integerp y)
                )
           (equal (GETBIT size1 (BVMULT size2 x y))
                  (GETBIT size1 (BVMULT (+ 1 size1) x y))))
  :hints (("Goal" :in-theory (e/d (getbit) (SLICE-BECOMES-GETBIT BVCHOP-1-BECOMES-GETBIT)))))

;; (defthm mod-by-1
;;  (implies (integerp x)
;;           (equal (mod x 1)
;;                  )))

(defthm getbit-of-bvmult-single-bit
  (implies (and (< n size)
                (< 0 n)
                (natp n)
                (natp size)
                (unsigned-byte-p 1 x)
                (integerp k))
           (equal (getbit n (bvmult size k x))
                  (bvand n (getbit n k) x)))
  :hints (("Goal" :in-theory (disable ;add-bvchop-around-equal ;bozo
                                      )
           :cases ((equal x 0)))))

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

;; (thm
;;  (IMPLIES (AND (<= SIZE SIZE2)
;;                (natp SIZE)
;;                (natp SIZE2)
;;                (INTEGERP X))
;;           (EQUAL (MOD (LOGEXT SIZE2 X) (EXPT 2 SIZE))
;;                  (MOD X (EXPT 2 SIZE))))
;;  :hints (("Goal" :in-theory (enable logext LOGAPP))))

(defthm logapp-of-logext-low
  (implies (and (<= size size2)
                (natp size)
                (natp size2)
                (integerp x)
                (integerp y))
           (equal (logapp size (logext size2 x) y)
                  (logapp size x y)))
  :hints (("Goal" :in-theory (enable logapp))))

(defthmd bvchop-of-logxor-back
  (implies (and (natp n) (natp a) (natp b)) ;used to have integerp hyps
           (equal (logxor (bvchop n a) (bvchop n b))
                  (bvchop n (logxor a b))))
  :hints (("Goal" :in-theory (enable))))

(theory-invariant (incompatible (:rewrite bvchop-of-logxor) (:rewrite bvchop-of-logxor-back)))

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

;use trim?
(defthm bvxor-of-bvor-tighten
  (implies (and (< size size2)
                (natp size)
                (natp size2))
           (equal (bvxor size (bvor size2 x y) z)
                  (bvxor size (bvor size x y) z)))
 :hints (("Goal" :in-theory (e/d (bvxor) (LOGXOR-BVCHOP-BVCHOP BVCHOP-1-BECOMES-GETBIT)))))

;bozo more like this (all combinations!)
;how about a macro to prove all combinations of a given theorem.  you put in a placeholder a bunch of substitutions
;and it does the product...
;use trim?
(defthm bvxor-of-bvor-tighten-2
  (implies (and (< size size2)
                (natp size)
                (natp size2))
           (equal (bvxor size z (bvor size2 x y))
                  (bvxor size z (bvor size x y))))
 :hints (("Goal" :in-theory (e/d (bvxor) (LOGXOR-BVCHOP-BVCHOP BVCHOP-1-BECOMES-GETBIT)))))

(DEFTHM BVAND-OF-BVCAT-TIGHTEN-LOW
  (IMPLIES (AND (<= SIZE LOWSIZE)
                (NATP SIZE)
                (NATP LOWSIZE)
                (NATP HIGHSIZE)
                (INTEGERP X)
                (INTEGERP Y)
                (INTEGERP Z))
           (EQUAL (BVAND SIZE (bvcat HIGHSIZE Y LOWSIZE X)
                         Z)
                  (BVAND SIZE X Z)))
  :HINTS (("Goal" :IN-THEORY (E/D (BVAND)
                                  (LOGAND-OF-BVCHOP)))))

(DEFTHM BVAND-OF-BVCAT-TIGHTEN-LOW-ALT
  (IMPLIES (AND (<= SIZE LOWSIZE)
                (NATP SIZE)
                (NATP LOWSIZE)
                (NATP HIGHSIZE)
                (INTEGERP X)
                (INTEGERP Y)
                (INTEGERP Z))
           (EQUAL (BVAND SIZE Z (bvcat HIGHSIZE Y LOWSIZE X))
                  (BVAND SIZE Z X)))
  :hints (("Goal" :use (:instance BVAND-OF-BVCAT-TIGHTEN-LOW)
           :in-theory (disable BVAND-OF-BVCAT-TIGHTEN-LOW))))
;; (thm
;;  (implies (and (natp size)
;;                (integerp x)
;;                (integerp y)
;;                (integerp z))
;;           (equal (BVAND size x (BVXOR size y z))
;;                  (BVXOR size (bvand size x y) (bvand size x z))))
;;  )

(defthm bvcat-of-logext-high
  (implies (and (<= highsize size2)
                (natp highsize)
                (natp size2)
                (natp lowsize)
                ;(integerp lowval)
                ;(integerp highval)
                )
           (equal (bvcat highsize (logext size2 highval) lowsize lowval)
                  (bvcat highsize highval lowsize lowval)))
  :hints (("Goal" :in-theory (e/d (bvcat) ()))))

;mixes theories?
(defthmd logtail-of-bvxor
  (implies (and (natp size)
                (natp n))
           (equal (logtail n (bvxor size x y))
                  (slice (+ -1 size) n (bvxor size x y))))
  :hints (("Goal"
           :use (:instance LOGTAIL-BECOMES-SLICE-BIND-FREE (x (bvxor size x y))
                           (newsize size))
           :in-theory (e/d ( ) (LOGTAIL-BECOMES-SLICE-BIND-FREE)))))

;here we tighten the call to size...
(defthm slice-of-bvxor-tighten2
  (implies (and (<= n high)
                (<= low n)
                (natp high)
                (natp low)
                (natp n))
           (equal (slice high low (bvxor n x y))
                  (slice (+ -1 n) low (bvxor n x y))))
  :hints (("Goal" :in-theory (e/d (slice) (slice-becomes-bvchop
                                           logtail-becomes-slice-bind-free
                                           logtail-of-bvchop-becomes-slice
                                           bvchop-of-logtail-becomes-slice)))))

(defthm bvor-of-bvcat-tighten-alt
  (implies (and (< size (+ lowsize highsize))
                (< lowsize size)
                (natp size)
                (natp lowsize)
                (natp highsize)
                ;;(integerp x)
                ;;(integerp y)
                ;;(integerp z)
                )
           (equal (bvor size z (bvcat highsize y lowsize x))
                  (bvor size z
                           (bvcat (- size lowsize)
                                    y lowsize x))))
  :hints (("Goal" :in-theory (enable bvor))))

;use trim
(defthm bvor-of-bvcat-tighten
  (implies (and (< size (+ lowsize highsize))
                (< lowsize size)
                (natp size)
                (natp lowsize)
                (natp highsize))
           (equal (bvor size (bvcat highsize y lowsize x)
                           z)
                  (bvor size
                           (bvcat (- size lowsize) y lowsize x)
                           z)))
  :hints (("Goal" :in-theory (enable bvor))))

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
           :in-theory (e/d (bvcat) (bvchop-of-* ;fixme
                                    logtail-of-bvchop-becomes-slice)))))

;(bvmult 4 (bvxor 4 12 10) 6)
;(bvxor 4 (bvmult 4 12 6) (bvmult 4 10 6))

(defthm bvxor-of-bvif-tighten-1
  (implies (and (< size1 size2)
                (< 0 size1) ;bozo
                (natp size1)
                (natp size2)
                (integerp y)
                (integerp z)
                (integerp x))
           (equal (bvxor size1 (bvif size2 test y z) x)
                  (bvxor size1 (bvif size1 test y z) x)))
  :hints (("Goal" :in-theory (e/d (bvxor ;bvchop-bvchop
                                   )
                                  (logxor-bvchop-bvchop)))))

(defthm bvxor-of-bvif-tighten-2
  (implies (and (< size1 size2)
                (< 0 size1) ;bozo
                (natp size1)
                (natp size2)
                (integerp y)
                (integerp z)
                (integerp x))
           (equal (bvxor size1 x (bvif size2 test y z))
                  (bvxor size1 x (bvif size1 test y z))))
  :hints (("Goal" :in-theory (e/d (bvxor ;bvchop-bvchop
                                   )
                                  (logxor-bvchop-bvchop)))))

(defthm slice-too-high-of-bvmult-with-usb1
  (implies (and (syntaxp (equal 1 (unsigned-term-size x)))
                (unsigned-byte-p low k)
                (unsigned-byte-p 1 x)
                (natp size)
                (integerp k)
                (natp low)
                (natp high))
           (equal (slice high low (bvmult size k x)) 0))
  :hints (("Goal" :in-theory (e/d (getbit-too-high)
                                  (;add-bvchop-around-equal
                                   ))
           :cases ((equal 0 x)))))

;bozo handle this even though the sizes don't match (BVXOR 8 x (bvcat 6 z 1 y))

(defthm bvmult-with-usb1
  (implies (and (syntaxp (equal 1 (unsigned-term-size x)))
;                (unsigned-byte-p n k)
                (unsigned-byte-p 1 x)
                (natp size)
                (integerp k))
           (equal (bvmult size k x)
                  (bvand size k (repeatbit size x))))
  :hints (("Goal" :in-theory (enable repeatbit)
           :use ((:instance usb1-cases)))))

;; ;bozo why did this arise?
;; (IMPLIES (SIGNED-BYTE-P 32 X)
;;          (UNSIGNED-BYTE-P 7 (SLICE 31 24 X)))

(defthmd bvand-open-to-logapp-special-case-for-bvmult
  (implies (and (syntaxp (quotep x)) ;bozo restrcit to when x is sparse (lots of zeros)
                (natp size)
                (< 1 size)
                (integerp x)
                (integerp y))
           (equal (bvmult size2 k (bvand size x y))
                  (bvmult size2 k (bvcat
                           1 (bvand 1 (getbit (+ -1 size) x) (getbit (+ -1 size) y)) (+ -1 size) (bvand (+ -1 size)  x y)))))
  :hints (("Goal" :in-theory (enable bvand-open-to-logapp))))

(defun count-ones (size x)
  (if (zp size)
      0
    (if (equal (getbit (+ -1 size) x) 1)
        (+ 1 (count-ones (+ -1 size) x))
      (count-ones (+ -1 size) x))))

;bozo think more about this
(defun sparse-bit-vector (size x)
  (<= (count-ones size x) (/ size 4)))

(defthmd bvand-open-to-logapp-when-sparse-constant
  (implies (and (syntaxp (and (quotep size)
                              (quotep x)
                              (sparse-bit-vector (unquote size) (unquote x))
                              ))
                (natp size)
                (< 1 size)
                (integerp x)
                (integerp y))
           (equal (bvand size x y)
                  (bvcat 1 (bvand 1 (getbit (+ -1 size) x) (getbit (+ -1 size) y)) (+ -1 size) (bvand (+ -1 size) x y)))))

;; (thm
;;  (implies (and (< high n)
;;                (<= low high)
;;                (natp low)
;;                (natp high)
;;                (natp n))
;;           (equal (SLICE high low (REPEATBIT n bit))
;;                  (repeatbit (+ 1 high (- low)) bit)))
;;  )

;gen the bvand to any op?
(defthm slice-of-bvand-tighten-high-index
  (implies (and (<= size high)
                (<= low size) ;bozo
                (< 0 size)
                (natp high)
                (natp size)
                (natp low))
           (equal (slice high low (bvand size x y))
                  (slice (+ -1 size) low (bvand size x y))))
  :hints (("Goal" :in-theory (enable bvand))))

;We prefer, for example:
;(bvxor x (bvchop 8 (foo x)) (slice 7 0 y))
;to
;(bvxor x (foo x) (slice 7 0 y))
;even though the bvchop can be dropped, because foo might be big (say, of size 32) and the latter would give a length mismatch in stp
;trying this - more like this?
(in-theory (disable bvxor-of-bvchop-1 bvxor-of-bvchop-2))
;(in-theory (enable add-bvchop-to-bvxor-1 add-bvchop-to-bvxor-2)) ;BOZO what about trimming constants?
(in-theory (disable bvchop-identity))
;bozo this is too bad
;(theory-invariant (incompatible (:rewrite add-bvchop-to-bvxor-1) (:rewrite bvchop-identity)))
;(theory-invariant (incompatible (:rewrite add-bvchop-to-bvxor-2) (:rewrite bvchop-identity)))

(in-theory (enable bvxor-trim-arg1 bvxor-trim-arg2))

(defthmd bvmult-pad-arg1
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize x) (newsize))
                (< newsize size)
                (natp size)
                (natp newsize)
                (force (unsigned-byte-p newsize x))
                (integerp y)
                )
           (equal (bvmult size x y)
                  (bvmult size (bvcat (- size newsize) 0 newsize x) y)))
  :hints (("Goal" :in-theory (e/d (bvcat-of-0 bvchop-identity)
                                  ( ;add-bvchop-to-bvxor-1
                                   ;add-bvchop-to-bvxor-2
                                   )))))

;bozo do one like this for every operator?
(defthmd bvmult-pad-arg2
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize y) (newsize))
                (< newsize size)
                (natp size)
                (natp newsize)
                (force (unsigned-byte-p newsize y))
                (integerp y)
                )
           (equal (BVMULT size x y)
                  (bvmult size x (bvcat (- size newsize) 0 newsize y))))
  :hints (("Goal" :in-theory (e/d (BVCAT-OF-0 bvchop-identity)
                                  ( ;ADD-BVCHOP-TO-BVXOR-1
                                   ;ADD-BVCHOP-TO-BVXOR-2
                                   )))))

(theory-invariant (incompatible (:rewrite bvmult-pad-arg1) (:rewrite BVCAT-OF-0)))
(theory-invariant (incompatible (:rewrite bvmult-pad-arg2) (:rewrite BVCAT-OF-0)))

;bozo more like this for other ops (some may exist and need to be turned on)
(defthm bvmult-trim-arg1
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize x) (newsize))
                (< size newsize)
                (natp size)
                (integerp newsize))
           (equal (bvmult size x y)
                  (bvmult size (bvchop size x) y)))
  :hints (("Goal" :in-theory (e/d (bvcat-of-0)
                                  (bvmult-pad-arg1
                                   bvmult-pad-arg2)))))

(defthm bvmult-trim-arg2
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize y) (newsize))
                (< size newsize)
                (natp size)
                (integerp newsize))
           (equal (BVMULT size x y)
                  (bvmult size x (bvchop size y))))
  :hints (("Goal" :in-theory (e/d (BVCAT-OF-0) (bvmult-pad-arg1
                                                bvmult-pad-arg2)))))



;add theory invars?
(in-theory (disable BVCAT-OF-BVCHOP-HIGH BVCAT-OF-BVCHOP-low))

(in-theory (disable slice-too-high-is-0
                    bvcat-when-highval-is-not-an-integer
                    bvcat-when-lowval-is-not-an-integer
                    bvchop-when-i-is-not-an-integer))

;after this fires, the associativity rule should fire too
;bozo make a high version
(defthmd bvcat-pad-low
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize lowval) (newsize))
                (unsigned-byte-p newsize lowval)
                (< newsize lowsize)
                (natp lowsize)
                (natp newsize)
                (integerp highval)
                (integerp lowval)
                )
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat
                           highsize highval lowsize (bvcat (- lowsize newsize) 0 newsize lowval))))
  :hints (("Goal" :in-theory (e/d (bvcat-of-0
                                   bvchop-identity
                                   bvcat-of-bvchop-low)
                                  (bvmult-pad-arg1
                                   bvmult-pad-arg2
                                   )))))

(defthmd bvcat-pad-high
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize highval) (newsize))
                (unsigned-byte-p newsize highval)
                (< newsize highsize)
                (natp highsize)
                (natp newsize)
                (integerp highval)
                (integerp lowval)
                )
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize (bvcat (- highsize newsize) 0 newsize highval) lowsize lowval)))
  :hints (("Goal" :in-theory (e/d (bvcat-of-0
                                   bvchop-identity
                                   bvcat-of-bvchop-low) (bvmult-pad-arg1 bvmult-pad-arg2)))))





(defthmd bvif-pad-arg-1-with-zeros
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize x) (newsize))
                (< newsize size)
                (unsigned-byte-p newsize x)
                (integerp x)
                (integerp y)
                (natp newsize)
                (natp size))
           (equal (bvif size test x y)
                  (bvif size test (bvcat (- size newsize) 0 newsize x) y)))
  :hints (("Goal" :in-theory (e/d (bvcat-of-0 bvchop-identity)
                                  (bvmult-pad-arg1
                                   bvmult-pad-arg2)))))

(defthmd bvif-pad-arg-2-with-zeros
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize y) (newsize))
                (< newsize size)
                (unsigned-byte-p newsize y)
                (integerp x)
                (integerp y)
                (natp newsize)
                (natp size))
           (equal (BVIF size test x y)
                  (bvif size test x (bvcat (- size newsize) 0 newsize y))))
  :hints (("Goal" :in-theory (e/d (BVCAT-OF-0 bvchop-identity)
                                  (BVMULT-PAD-ARG1
                                   BVMULT-PAD-ARG2)))))

(defthm collect-constants-<-/
  (implies (and (syntaxp (and (quotep a)
                              (quotep b)))
                (< 0 b)
                (rationalp a)
                (rationalp b)
                (rationalp x)
                )
           (equal (< a (* b x))
                  (< (/ a b) x))))

(defthm collect-constants-<-/-two
  (implies (and (syntaxp (and (quotep a)
                              (quotep b)))
                (< 0 b)
                (rationalp a)
                (rationalp b)
                (rationalp x)
                )
           (equal (< (* b x) a)
                  (< x (/ a b)))))

;move
(defthm my-non-integerp-<-integerp
  (implies (and (syntaxp (quotep k))
                (not (integerp k))
                (rationalp k)
                (integerp n)
;                (case-split (rationalp k))
                )
           (equal (< k n)
                  (< (floor k 1) n))))
;fixme drop?
(defthm <-of-non-integerp-and-integerp
  (implies (and (syntaxp (quotep k))
                (not (integerp k))
                (integerp n)
                (rationalp k))
           (equal (< k n)
                  (< (floor k 1) n)))
  :hints (("Goal" :in-theory (disable my-non-integerp-<-integerp)
           :use (:instance my-non-integerp-<-integerp (k k)))))

;move
(defthm my-integerp-<-non-integerp
  (implies (and (syntaxp (quotep k))
                (not (integerp k))
                (rationalp k)
                (integerp n)
                ;(case-split (rationalp k))
                )
           (equal (< n k)
                  ;phrase this as a < ?
                  (<= n (floor k 1)))))

(in-theory (enable bvchop-identity))
(in-theory (enable bvxor-of-bvchop-1
                             bvxor-of-bvchop-2
                             bvcat-of-bvchop-low
                             bvcat-of-bvchop-high
                             bvxor-1-of-getbit-arg1
                             bvxor-1-of-getbit-arg2
                             bvand-1-of-getbit-arg1
                             bvand-1-of-getbit-arg2
                             bvif-of-getbit-arg1
                             bvif-of-getbit-arg2
))

(defthm logext-trim-arg
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize x) (newsize))
                (< size newsize)
                (natp size)
                (< 0 size)
                (natp newsize)
                (integerp x))
           (equal (logext size x)
                  (logext size (bvchop size x)))))

(defthmd bvxor-pad-arg1
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize x) (newsize))
                (< newsize size)
                (natp size)
                (natp newsize)
                (force (unsigned-byte-p newsize x))
                (integerp y)
                )
           (equal (bvxor size x y)
                  (bvxor size (bvcat (- size newsize) 0 newsize x) y)))
  :hints (("Goal" :in-theory (e/d (bvcat-of-0 bvchop-identity)
                                  ( ;add-bvchop-to-bvxor-1
                                   bvcat-pad-low
                                   bvcat-pad-high
                                   bvmult-pad-arg1
                                   bvmult-pad-arg2
                                   )))))

(defthmd bvxor-pad-arg2
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize y) (newsize))
                (< newsize size)
                (natp size)
                (natp newsize)
                (force (unsigned-byte-p newsize y))
                (integerp x)
                )
           (equal (bvxor size x y)
                  (bvxor size x (bvcat (- size newsize) 0 newsize y))))
  :hints (("Goal" :in-theory (e/d (bvcat-of-0 bvchop-identity)
                                  ( ;add-bvchop-to-bvxor-1
                                   bvcat-pad-low
                                   bvcat-pad-high
                                   bvmult-pad-arg1
                                   bvmult-pad-arg2
                                   )))))

;these shouldn't be needed for "user" proofs:
(in-theory (disable getbit-when-val-is-not-an-integer
                    slice-when-val-is-not-an-integer
                    ;;bvxor-when-x-is-not-an-integer
                    ;;bvxor-when-y-is-not-an-integer
                    ))

(defthmd bvcat-blast-high
  (implies (and (syntaxp (not (quotep highval))) ;Fri Mar  4 20:24:01 2011
                (< 1 highsize)
                (integerp highsize)
                (natp lowsize)
                )
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat 1
                         (getbit (+ -1 highsize) highval)
                         (+ -1 highsize lowsize)
                         (bvcat (+ -1 highsize) highval lowsize lowval))))
  :hints (("Goal" :in-theory (enable natp))))

(defthmd plus-becomes-bvplus
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'xsize x))
                (bind-free (bind-var-to-unsigned-term-size 'ysize y))
                (force (unsigned-byte-p-forced xsize x))
                (force (unsigned-byte-p-forced ysize y))
                (posp xsize))
           (equal (+ x y)
                  (bvplus (+ 1 (max xsize ysize)) x y)))
  :hints (("Goal"
           :use (:instance EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1
                           (r 2)
                           (i (min xsize ysize))
                           (j (max xsize ysize)))
           :in-theory (e/d ( bvplus unsigned-byte-p unsigned-byte-p-forced) (EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1
                                                      <-of-expt-and-expt
                                                      ;;anti-bvplus
                                                      )))))

(defthmd plus-becomes-bvplus-arg1-free
  (implies (and (unsigned-byte-p xsize x)
                (bind-free (bind-var-to-unsigned-term-size 'ysize y))
                (force (unsigned-byte-p-forced ysize y))
                (posp xsize))
           (equal (+ x y)
                  (bvplus (+ 1 (max xsize ysize)) x y)))
  :hints (("Goal" :use (:instance plus-becomes-bvplus)
           :in-theory (e/d (unsigned-byte-p-forced) (plus-becomes-bvplus)))))

(defthmd plus-becomes-bvplus-arg2-free
  (implies (and (unsigned-byte-p xsize x)
                (bind-free (bind-var-to-unsigned-term-size 'ysize y))
                (force (unsigned-byte-p-forced ysize y))
                (posp xsize))
           (equal (+ y x)
                  (bvplus (+ 1 (max xsize ysize)) x y)))
  :hints (("Goal" :use (:instance plus-becomes-bvplus-arg1-free)
           :in-theory (e/d (<-of-constant-when-unsigned-byte-p-size-param)
                           ( plus-becomes-bvplus-arg1-free)))))

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
  :otf-flg t
  :hints (("Goal" :use (:instance BVCAT-SLICE-SLICE-SAME (lowindex1 0) (highindex1 (+ -1 size1)))
           :in-theory (disable BVCAT-SLICE-SLICE-SAME))))
