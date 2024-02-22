; Rules to convert bitops operations to operations from the Kestrel BV library
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/bitops/part-install" :dir :system)
(include-book "centaur/bitops/rotate" :dir :system)
(include-book "bvcat-def")
(include-book "slice-def")
(include-book "getbit-def")
(include-book "rightrotate")
(include-book "leftrotate")
(local (include-book "rules"))
(local (include-book "logior-b"))
(local (include-book "intro"))
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

;move or make local
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

(local
  (defthm slice-mask
    (implies (and (natp low)
                  (natp width))
             (equal (SLICE (+ -1 LOW WIDTH)
                           LOW
                           (+ (- (EXPT 2 LOW))
                              (* (EXPT 2 LOW) (EXPT 2 WIDTH))))
                    (+ -1 (expt 2 width))))
    :hints (("Goal" :in-theory (e/d (slice) (BVCHOP-OF-LOGTAIL-BECOMES-SLICE))))))

;; ;;move
;; (defthm <-of-expt-and-expt
;;   (implies (and (natp i)
;;                 (Natp j))
;;            (equal (< (EXPT '2 i) (EXPT '2 j))
;;                   (< i j))))

(local
  (defthm slice-too-high-lemma-2
    (implies (and (natp low)
                  (natp width)
                  (natp size))
             (equal (SLICE (+ -1 SIZE)
                           (+ LOW WIDTH)
                           (+ (- (EXPT 2 LOW))
                              (* (EXPT 2 LOW) (EXPT 2 WIDTH))))
                    0))
    :hints (("Goal" :in-theory (e/d (slice GETBIT-OF-PLUS)
                                    (BVCHOP-OF-LOGTAIL-BECOMES-SLICE
                                     <-OF-BVCHOP-HACK))))))

(defthm part-select-width-low-becomes-slice
  (implies (and (integerp low)
                (integerp width))
           (equal (bitops::part-select-width-low x width low)
                  (slice (+ low width -1) low x)))
  :hints (("Goal" :in-theory (e/d (bitops::part-select-width-low slice)
                                  (bvchop-of-logtail-becomes-slice)))))

(defthmd getbit-of-part-install-width-low-helper
  (implies (and (natp m)
                (natp low)
                (natp width)
;                (integerp x)   ;drop
                )
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
  :hints (("Goal" :use (:instance getbit-of-part-install-width-low-helper (x (ifix x)))
           :in-theory (disable BITOPS::PART-INSTALL-WIDTH-LOW$INLINE))))

;; Unfortunately, PART-INSTALL-WIDTH-LOW does not indicate any size for X.
(defthm part-install-width-low-becomes-bvcat
  (implies (and (unsigned-byte-p xsize x) ; xsize is a free var
                (natp xsize) ;(posp xsize)              ;drop?
                ;(< (+ width low) xsize)   ;allow = ?
                (natp low)
                (natp width))
           (equal (BITOPS::PART-INSTALL-WIDTH-LOW val x width low)
                  (bvcat (max xsize (+ width low)) ;(- xsize (+ width low))
                         (slice (+ -1 xsize) (+ low width) x)
                         (+ width low)
                         (bvcat width val low x))))
  :hints (("Goal" :in-theory (e/d (BITOPS::PART-INSTALL-WIDTH-LOW
                                   BVCAT-EQUAL-REWRITE
                                   SLICE-TOO-HIGH-IS-0-NEW
                                   bvnot-of-0
                                   bvuminus-of-1-arg2
;BVNOT-TRIM-ALL
                                   SLICE-TOO-HIGH-IS-0-NEW
                                   expt-of-+
                                   BVCHOP-OF-LOGNOT-BECOMES-BVNOT
                                   LOGAND-BECOMES-BVAND
                                   LOGAND-BECOMES-BVAND-alt
                                   ash)
                                  (;EXPONENTS-ADD
                                   ;SLICE-OF-+
                                   ;BVCAT-OF-+-HIGH   ;looped
                                   ;BVAND-OF-+-ARG3 ;looped (we should treat a mask of 2^n-1 differently from a generic +
                                   ;BVCAT-OF-+-LOW
                                   )))))

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
                            REPEATBIT-OF-1-ARG2
                            BVNOT-OF-0
                            LOGAND-BECOMES-BVAND
                            BVCHOP-OF-LOGNOT-BECOMES-BVNOT
                            ash)
                           (                  ;SLICE-OF-BVAND
                                                        ;;BVCAT-OF-+-HIGH
                            ;;EXPONENTS-ADD
                            ;;BVCAT-OF-+-LOW         ;looped
                            ;;SLICE-OF-+             ;looped
                            ;;BVAND-OF-+-ARG3        ;looped
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
                                   BVCHOP-OF-LOGTAIL-BECOMES-SLICE
                                   ;;for speed:
                                   UNSIGNED-BYTE-P-FROM-BOUNDS
                                   ;;UNSIGNED-BYTE-P-PLUS
                                   ;;UNSIGNED-BYTE-P-WHEN-ZP-CHEAP
                                   ;;BOUND-FROM-NATP-FACT ;seems bad?
                                   BVCAT-EQUAL-REWRITE-ALT
                                   BVCAT-EQUAL-REWRITE
                                   )))))

;this guesses that X fits in 32 bits, which is common when X is (XR :RFLAGS I X86)
(defthm part-install-width-low-becomes-bvcat-32
  (implies (and (unsigned-byte-p 32 x) ;e.g., the flags
                (natp low)
                (natp width))
           (equal (bitops::part-install-width-low val x width low)
                  (bvcat (max 32 (+ width low))
                         (slice (+ -1 32) (+ low width) x)
                         (+ width low)
                         (bvcat width val low x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Introduces the BV function
(defthm rotate-right-becomes-rightrotate
  (implies (and (natp width)
                (natp x)
                (natp places))
           (equal (acl2::rotate-right x width places)
                  (acl2::rightrotate width places x)))
  :hints (("Goal"
           :in-theory (enable acl2::rotate-right
                              acl2::rightrotate
                              acl2::bvchop-of-logior-becomes-bvor
                              ash-of-negative-becomes-logtail
                              logtail-of-bvchop-becomes-slice
                              acl2::logtail-becomes-0
                              acl2::bvchop-of-logior-becomes-bvor
                              ifix
                              logand-of-bvchop-becomes-bvand-alt))))

;; Introduces the BV function
(defthm rotate-left-becomes-leftrotate
  (implies (and (natp width)
                (natp x)
                (natp places))
           (equal (acl2::rotate-left x width places)
                  (acl2::leftrotate width places x)))
  :hints (("Goal"
           :in-theory (enable acl2::rotate-left
                              acl2::leftrotate
                              acl2::bvchop-of-logior-becomes-bvor
                              ash-of-negative-becomes-logtail
                              logtail-of-bvchop-becomes-slice
                              acl2::logtail-becomes-0
                              acl2::bvchop-of-logior-becomes-bvor
                              ifix
                              logand-of-bvchop-becomes-bvand-alt))))
