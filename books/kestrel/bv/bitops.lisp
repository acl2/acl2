; Rules to convert bitops operations to operations from the Kestrel BV library
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/bitops/part-install" :dir :system)
(include-book "centaur/bitops/rotate" :dir :system)
;(include-book "centaur/bitops/fast-rotate" :dir :system)
(include-book "bvcat-def")
(include-book "slice-def")
(include-book "getbit-def")
(include-book "rightrotate")
(include-book "leftrotate")
(include-book "bitand")
(include-book "bitor")
(include-book "bitxor")
(local (include-book "rules"))
(local (include-book "logand-b"))
(local (include-book "logior-b"))
(local (include-book "intro"))
(local (include-book "ash"))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/ash" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(in-theory (disable bitops::part-select-width-low
                    bitops::part-install-width-low))

;move?
(local
  (defthm <=-of-*-same-linear-special
    (implies (and (<= 1 y)
                  (<= 0 x)
                  (rationalp x)
                  (rationalp y))
             (<= x (* x y)))
    :rule-classes :linear
    :hints (("Goal" :use (:instance <=-of-*-and-*-same-forward-1 (x1 1) (x2 y) (y x))
             :in-theory (disable <=-of-*-and-*-same-forward-1)))))

;; (defthm cancel-two
;;   (equal (< (+ y x) x)
;;          (< y 0)))

;; ;gen
;; (defthm <-of-*-cancel-1
;;   (implies (and (posp a)
;;                 (posp b))
;;            (equal (< (* a b) a)
;;                   (< b 1))))

;gen
;; (defthm <-of-*-cancel-2
;;   (implies (and (posp a)
;;                 (posp b)
;;                 (posp c))
;;            (equal (< (* a b) (* c a))
;;                   (< b c))))

;move
(local
  ;; slicing a mask of all ones to extract the run of ones
  (defthm slice-mask
    (implies (and (natp low)
                  (natp width))
             (equal (slice (+ -1 low width)
                           low
                           (+ (- (expt 2 low))
                              (* (expt 2 low) (expt 2 width))))
                    (+ -1 (expt 2 width))))
    :hints (("Goal" :in-theory (enable slice)))))

(local
  ;; slicing a mask of all ones above the run of ones
  (defthm slice-too-high-lemma-2
    (implies (and (natp low)
                  (natp width)
                  (natp size))
             (equal (slice (+ -1 size)
                           (+ low width)
                           (+ (- (expt 2 low))
                              (* (expt 2 low) (expt 2 width))))
                    0))
    :hints (("Goal" :in-theory (e/d (slice getbit-of-+ logtail-of-plus)
                                    (<-of-bvchop-hack))))))

;move
(local
  (defthm bvnot-of-*-of-expt-same-arg2
    (implies (and (natp i)
                  (natp low))
             (equal (bvnot low (* i (expt 2 low)))
                    (+ -1 (expt 2 low))))
    :hints (("Goal" :in-theory (enable bvnot lognot bvchop-of-sum-cases)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; should almost always fire.
(defthm part-select-width-low-becomes-slice
  (implies (and (integerp low)
                (integerp width))
           (equal (bitops::part-select-width-low x width low)
                  (slice (+ low width -1) low x)))
  :hints (("Goal" :in-theory (enable bitops::part-select-width-low slice))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We want to replace calls of part-install-width-low with BV terms, but this
;; is awkward in general, because we may not know the size of the "x" argument.

(defthm getbit-of-part-install-width-low
  (implies (and (natp m)
                (natp low)
                (natp width))
           (equal (getbit m (bitops::part-install-width-low val x width low))
                  ;; not simplified; i just want to get rid of the part-install:
                  (getbit m (bvcat (- (+ m 1) (+ low width))
                                   (slice m
                                          (+ low width)
                                          x)
                                   (+ width low)
                                   (bvcat width
                                          val
                                          low
                                          x)))))
  :hints (("Goal" :cases ((NATP (+ 1 (- LOW) M)))
           :in-theory (e/d (bitops::part-install-width-low ifix getbit-of-logand)
                           (ash logmask)))))

(defthm bvchop-of-part-install-width-low-same
  (implies (and (natp low)
                (natp width))
           (equal (bvchop low (bitops::part-install-width-low val x width low))
                  (bvchop low x)))
  :hints (("Goal" :in-theory (e/d (bitops::part-install-width-low bvchop-of-lognot-becomes-bvnot ash)
                                  (logmask$inline)))))

(defthm bvchop-of-part-install-width-low-becomes-bvcat
  (implies (and (<= (+ low width) size)
                (natp low)
                (natp width)
                (natp size))
           (equal (bvchop size (bitops::part-install-width-low val x width low))
                  (bvcat (- size (+ width low))
                         (slice (+ -1 size) (+ width low) x)
                         (+ width low)
                         (bvcat width val low x))))
  :hints (("Goal" :cases ((equal size (+ low width)))
           :in-theory (e/d (bitops::part-install-width-low
                            BVNOT-OF-0
                            LOGAND-BECOMES-BVAND
                            BVCHOP-OF-LOGNOT-BECOMES-BVNOT
                            ash)
                           (;; SLICE-OF-BVAND
                            ;; EXPONENTS-ADD
                            )))))

;replace part-install-width-low with bvcat when inside a slice
;slow proof?
(defthm slice-of-part-install-width-low
  (implies (and (<= (+ low2 width) (+ high 1))
                (natp low)
                (natp high)
                (natp low2)
                (natp width))
           (equal (slice high low (bitops::part-install-width-low val x width low2))
                  ;;could further simplify this...:
                  (slice high low (bvcat (- (+ 1 high) (+ width low2))
                                         (slice high (+ width low2) x)
                                         (+ width low2)
                                         (bvcat width val low2 x)))))
  :hints (("Goal" :in-theory (e/d (slice
                                   BVCHOP-OF-LOGTAIL)
                                  (SLICE-OF-BVAND
                                   ;;for speed:
                                   UNSIGNED-BYTE-P-FROM-BOUNDS
                                   ;;UNSIGNED-BYTE-P-PLUS
                                   ;;UNSIGNED-BYTE-P-WHEN-ZP-CHEAP
                                   BVCAT-EQUAL-REWRITE-ALT
                                   BVCAT-EQUAL-REWRITE
                                   )))))

(defthm slice-of-part-install-width-low-high
  (implies (and (<= (+ width low2) low)
                (natp low)
                (integerp high)
                (natp low2)
                (natp width))
           (equal (slice high low (bitops::part-install-width-low val x width low2))
                  ;;could further simplify this...:
                  (slice high low x)))
  :hints (("Goal" :in-theory (e/d (slice
                                   BVCHOP-OF-LOGTAIL)
                                  (SLICE-OF-BVAND

                                   ;;for speed:
                                   UNSIGNED-BYTE-P-FROM-BOUNDS
                                   ;;UNSIGNED-BYTE-P-PLUS
                                   ;;UNSIGNED-BYTE-P-WHEN-ZP-CHEAP
                                   BVCAT-EQUAL-REWRITE-ALT
                                   BVCAT-EQUAL-REWRITE
                                   )))))

(defthm part-install-width-low-of-0-arg3
  (equal (bitops::part-install-width-low val x 0 low)
         (ifix x))
  :hints (("Goal" :in-theory (enable bitops::part-install-width-low))))

;; Unfortunately, PART-INSTALL-WIDTH-LOW does not indicate any size for X.
(defthm part-install-width-low-becomes-bvcat
  (implies (and (unsigned-byte-p xsize x) ; xsize is a free var
                (natp xsize) ;(posp xsize)              ;drop?
                ;(< (+ width low) xsize)   ;allow = ?
                (natp low)
                (natp width))
           (equal (BITOPS::PART-INSTALL-WIDTH-LOW val x width low)
                  (bvcat (- xsize (+ width low)) ;(max xsize (+ width low)) ;(- xsize (+ width low))
                         (slice (+ -1 xsize) (+ low width) x)
                         (+ width low)
                         (bvcat width val low x))))
  :hints (("Goal" :cases ((NATP (+ (- LOW) (- WIDTH) XSIZE))))))

;this guesses that X fits in 32 bits
(defthm part-install-width-low-becomes-bvcat-32
  (implies (and (unsigned-byte-p 32 x)
                (natp low)
                (natp width))
           (equal (bitops::part-install-width-low val x width low)
                  (bvcat (- 32 (+ width low))
                         (slice 31 (+ low width) x)
                         (+ width low)
                         (bvcat width val low x)))))

;this guesses that X fits in 64 bits
(defthm part-install-width-low-becomes-bvcat-64
  (implies (and (unsigned-byte-p 64 x)
                (natp low)
                (natp width))
           (equal (bitops::part-install-width-low val x width low)
                  (bvcat (- 64 (+ width low))
                         (slice 63 (+ low width) x)
                         (+ width low)
                         (bvcat width val low x)))))

;this guesses that X fits in 128 bits
(defthm part-install-width-low-becomes-bvcat-128
  (implies (and (unsigned-byte-p 128 x)
                (natp low)
                (natp width))
           (equal (bitops::part-install-width-low val x width low)
                  (bvcat (- 128 (+ width low))
                         (slice 127 (+ low width) x)
                         (+ width low)
                         (bvcat width val low x)))))

;this guesses that X fits in 256 bits
(defthm part-install-width-low-becomes-bvcat-256
  (implies (and (unsigned-byte-p 256 x)
                (natp low)
                (natp width))
           (equal (bitops::part-install-width-low val x width low)
                  (bvcat (- 256 (+ width low))
                         (slice 255 (+ low width) x)
                         (+ width low)
                         (bvcat width val low x)))))

;this guesses that X fits in 512 bits
(defthm part-install-width-low-becomes-bvcat-512
  (implies (and (unsigned-byte-p 512 x)
                (natp low)
                (natp width))
           (equal (bitops::part-install-width-low val x width low)
                  (bvcat (- 512 (+ width low))
                         (slice 511 (+ low width) x)
                         (+ width low)
                         (bvcat width val low x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Introduces the BV function
(defthm rotate-right-becomes-rightrotate
  (implies (and (natp width)
                (natp places))
           (equal (rotate-right x width places)
                  (rightrotate width places x)))
  :hints (("Goal"
           :in-theory (enable rotate-right
                              rightrotate
                              bvchop-of-logior-becomes-bvor
                              ash-becomes-logtail
                              logtail-of-bvchop-becomes-slice
                              logtail-becomes-0
                              bvchop-of-logior-becomes-bvor
                              ifix
                              logand-of-bvchop-becomes-bvand-alt))))

;; Introduces the BV function
(defthm rotate-left-becomes-leftrotate
  (implies (and (natp width)
                (natp places))
           (equal (rotate-left x width places)
                  (leftrotate width places x)))
  :hints (("Goal"
           :in-theory (enable rotate-left
                              leftrotate
                              bvchop-of-logior-becomes-bvor
                              ash-becomes-logtail
                              logtail-of-bvchop-becomes-slice
                              logtail-becomes-0
                              bvchop-of-logior-becomes-bvor
                              ifix
                              logand-of-bvchop-becomes-bvand-alt))))

;; ;; todo: handle more specialized variants of rotate-left.  also handle the variants of rotate-right.
;; ;; or just open these to expose the non-specialized rotate ops!
;; (defthm rotate-left-32-becomes-leftrotate
;;   (implies (and (natp places)
;;                 (<= places 32) ;gen
;;                 )
;;            (equal (bitops::rotate-left-32 x places)
;;                   (leftrotate 32 places x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm logbit-becomes-getbit
  (equal (logbit pos i)
         (getbit pos i)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm b-and-becomes-bitand
  (implies (and (unsigned-byte-p 1 x)
                (unsigned-byte-p 1 y))
           (equal (b-and x y)
                  (bitand x y)))
  :hints (("Goal" :in-theory (e/d (bitand b-and) (bvand-1-becomes-bitand)))))

(defthm b-ior-becomes-bitor
  (implies (and (unsigned-byte-p 1 x)
                (unsigned-byte-p 1 y))
           (equal (b-ior x y)
                  (bitor x y)))
  :hints (("Goal" :in-theory (e/d (bitor b-ior) (bvor-1-becomes-bitor)))))

(defthm b-xor-becomes-bitxor
  (implies (and (unsigned-byte-p 1 x)
                (unsigned-byte-p 1 y))
           (equal (b-xor x y)
                  (bitxor x y)))
  :hints (("Goal" :in-theory (e/d (bitxor b-xor) (bvxor-1-becomes-bitxor)))))
