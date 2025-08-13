; Mixed theorems about bit-vectors
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
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
(include-book "bitwise")
(include-book "unsigned-byte-p-forced")
(include-book "bvif")
(include-book "bvcat")
(include-book "bvand")
(include-book "bvxor")
(include-book "bvplus")
(include-book "repeatbit")
(local (include-book "unsigned-byte-p"))
(local (include-book "logxor-b"))
(local (include-book "kestrel/library-wrappers/arithmetic-inequalities" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/arithmetic-light/lg" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor-and-expt" :dir :system))
(local (include-book "kestrel/library-wrappers/ihs-logops-lemmas" :dir :system)) ;drop, for sub1-logcdr-induction-1

;move
;use polarities?
(defthmd my-non-integerp-<-integerp
  (implies (and (syntaxp (quotep k))
                (not (integerp k))
                (integerp n)
                (rationalp k))
           (equal (< k n)
                  (< (floor k 1) n))))
;fixme drop?
;use polarities?
(defthmd <-of-non-integerp-and-integerp
  (implies (and (syntaxp (quotep k))
                (not (integerp k))
                (integerp n)
                (rationalp k))
           (equal (< k n)
                  (< (floor k 1) n)))
  :hints (("Goal" :in-theory (disable my-non-integerp-<-integerp)
           :use (:instance my-non-integerp-<-integerp (k k)))))

;move
;use polarities?
(defthmd my-integerp-<-non-integerp
  (implies (and (syntaxp (quotep k))
                (not (integerp k))
                (rationalp k)
                (integerp n))
           (equal (< n k)
                  ;phrase this as a < ?
                  (<= n (floor k 1)))))

;move?
(in-theory (enable bvchop-identity
                   ;;bvxor-of-bvchop-1
                   ;;bvxor-of-bvchop-2
                   ))

(defthm bvmult-tighten
  (implies (and (bind-free (bind-var-to-bv-term-size 'xsize x))
                (bind-free (bind-var-to-bv-term-size 'ysize y))
                (< (+ xsize ysize) size)
                (natp size)
                (force (unsigned-byte-p-forced xsize x))
                (force (unsigned-byte-p-forced ysize y))
                )
           (equal (bvmult size x y)
                  (bvmult (+ xsize ysize) x y)))
  :hints (("Goal" :in-theory (enable UNSIGNED-BYTE-P-FORCED bvmult))))

(defthm bvmult-tighten-when-power-of-2p
  (implies (and (syntaxp (quotep x))
                (power-of-2p x)
                (bind-free (bind-var-to-bv-term-size 'ysize y))
                (< (+ (lg x) ysize) size)
                (natp size)
                ;; (force (unsigned-byte-p-forced xsize x))
                (force (unsigned-byte-p-forced ysize y))
                )
           (equal (bvmult size x y)
                  (bvmult (+ (lg x) ysize) x y)))
  :hints (("Goal" :in-theory (enable UNSIGNED-BYTE-P-FORCED bvmult power-of-2p))))

(defthmd floor-when-usb-bind-free
  (implies (and (bind-free (bind-var-to-bv-term-size 'xsize x) (xsize))
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
                    (;anti-slice
                     ;bvchop-of-floor-of-expt-of-2
                     )))))

;bozo do stuff like this better?
(defthm logapp-of-bvif
  (implies (and (integerp size)
                (integerp a)
                (integerp b)
                (< 0 size))
           (equal (logapp lowsize lowval (bvif size test a b))
                  (BVCAT SIZE (BVIF SIZE TEST A B)
                         LOWSIZE LOWVAL)))
  :hints (("Goal" :in-theory (enable bvcat bvif))))

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
           :in-theory (enable logand*
                            logcdr ;fl
                            expt-of-+ mod-expt-split)
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

(defthm bvcat-of-bvxor-tighten-2
  (implies (and (< size1 size2)
                (natp size1)
                (natp size2)
                (integerp x)
                (integerp z)
                (integerp y))
           (equal (bvcat size1 (bvxor size2 z y) lowsize x)
                  (bvcat size1 (bvxor size1 z y) lowsize x)))
  :hints (("Goal" :in-theory (enable bvcat))))

;(in-theory (disable bvxor-trim-arg2 bvxor-trim-arg1)) ;bozo

;; (defthm mod-by-1
;;  (implies (integerp x)
;;           (equal (mod x 1)
;;                  )))

;drop?
(defthm getbit-of-bvmult-single-bit
  (implies (and (unsigned-byte-p 1 x)
                (< n size)
                (< 0 n)
                (natp n)
                (natp size)
                (integerp k))
           (equal (getbit n (bvmult size k x))
                  (bvand n (getbit n k) x)))
  :hints (("Goal" :cases ((equal x 0)))))

;; (thm
;;  (IMPLIES (AND (<= SIZE SIZE2)
;;                (natp SIZE)
;;                (natp SIZE2)
;;                (INTEGERP X))
;;           (EQUAL (MOD (LOGEXT SIZE2 X) (EXPT 2 SIZE))
;;                  (MOD X (EXPT 2 SIZE))))
;;  :hints (("Goal" :in-theory (enable logext LOGAPP))))

(defthmd bvchop-of-logxor-back
  (implies (and (natp n) (natp a) (natp b)) ;used to have integerp hyps
           (equal (logxor (bvchop n a) (bvchop n b))
                  (bvchop n (logxor a b)))))

(theory-invariant (incompatible (:rewrite bvchop-of-logxor) (:rewrite bvchop-of-logxor-back)))

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
  :hints (("Goal" :in-theory (enable bvcat))))

;mixes theories?
(defthmd logtail-of-bvxor
  (implies (and (natp size)
                (natp n))
           (equal (logtail n (bvxor size x y))
                  (slice (+ -1 size) n (bvxor size x y))))
  :hints (("Goal"
           :use (:instance LOGTAIL-BECOMES-SLICE (x (bvxor size x y))
                           (m size))
           :in-theory (disable LOGTAIL-BECOMES-SLICE))))

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
  :hints (("Goal" :in-theory (e/d (bvxor)
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
  :hints (("Goal" :in-theory (e/d (bvxor)
                                  (logxor-bvchop-bvchop)))))

(defthm slice-too-high-of-bvmult-with-usb1
  (implies (and (syntaxp (equal 1 (bv-term-size x)))
                (unsigned-byte-p low k)
                (unsigned-byte-p 1 x)
                (natp size)
                (integerp k)
                (natp low)
                (natp high))
           (equal (slice high low (bvmult size k x)) 0))
  :hints (("Goal" :in-theory (enable getbit-too-high)
           :cases ((equal 0 x)))))

;bozo handle this even though the sizes don't match (BVXOR 8 x (bvcat 6 z 1 y))

(defthm bvmult-with-usb1
  (implies (and (syntaxp (equal 1 (bv-term-size x)))
;                (unsigned-byte-p n k)
                (unsigned-byte-p 1 x)
                (natp size)
                (integerp k))
           (equal (bvmult size k x)
                  (bvand size k (repeatbit size x))))
  :hints (("Goal" :in-theory (enable repeatbit)
           :use (usb1-cases))))

;; ;bozo why did this arise?
;; (IMPLIES (SIGNED-BYTE-P 32 X)
;;          (UNSIGNED-BYTE-P 7 (SLICE 31 24 X)))

(defthmd bvand-open-to-bvcat-high-bit-special-case-for-bvmult
  (implies (and (syntaxp (quotep x)) ;bozo restrcit to when x is sparse (lots of zeros)
                (< 1 size)
                (natp size)
                (integerp x)
                (integerp y))
           (equal (bvmult size2 k (bvand size x y))
                  (bvmult size2 k (bvcat
                           1 (bvand 1 (getbit (+ -1 size) x) (getbit (+ -1 size) y)) (+ -1 size) (bvand (+ -1 size)  x y)))))
  :hints (("Goal" :in-theory (enable bvand-open-to-bvcat-high-bit ; todo: go to bvand instead
                                     ))))

(defun count-ones (size x)
  (if (zp size)
      0
    (if (equal (getbit (+ -1 size) x) 1)
        (+ 1 (count-ones (+ -1 size) x))
      (count-ones (+ -1 size) x))))

;bozo think more about this
(defun sparse-bit-vector (size x)
  (<= (count-ones size x) (/ size 4)))

(defthmd bvand-open-to-bvcat-high-bit-when-sparse-constant
  (implies (and (syntaxp (and (quotep size)
                              (quotep x)
                              (sparse-bit-vector (unquote size) (unquote x))
                              ))
                (< 1 size)
                (natp size)
                (integerp x)
                (integerp y))
           (equal (bvand size x y)
                  (bvcat 1 (bvand 1 (getbit (+ -1 size) x) (getbit (+ -1 size) y)) (+ -1 size) (bvand (+ -1 size) x y))))
  :hints (("Goal" :in-theory (enable slice-becomes-getbit))))

;; (thm
;;  (implies (and (< high n)
;;                (<= low high)
;;                (natp low)
;;                (natp high)
;;                (natp n))
;;           (equal (SLICE high low (REPEATBIT n bit))
;;                  (repeatbit (+ 1 high (- low)) bit)))
;;  )

;bozo more like this for other ops (some may exist and need to be turned on)
;todo: use trim, not bvchop
(defthm bvmult-trim-arg1
  (implies (and (bind-free (bind-var-to-bv-term-size 'xsize x) (xsize))
                (< size xsize)
                (natp size)
                (integerp xsize))
           (equal (bvmult size x y)
                  (bvmult size (bvchop size x) y))))

;todo: use trim, not bvchop
(defthm bvmult-trim-arg2
  (implies (and (bind-free (bind-var-to-bv-term-size 'ysize y) (ysize))
                (< size ysize)
                (natp size)
                (integerp ysize))
           (equal (bvmult size x y)
                  (bvmult size x (bvchop size y)))))

;add theory invars?
;(in-theory (disable BVCAT-OF-BVCHOP-HIGH BVCAT-OF-BVCHOP-low))

;these shouldn't be needed for "user" proofs outside the BV library:
;todo: consider dropping this.
;where should these disables go?
(in-theory (disable slice-too-high-is-0
                    bvcat-when-highval-is-not-an-integer
                    bvcat-when-lowval-is-not-an-integer
                    bvchop-when-i-is-not-an-integer
                    ;;getbit-when-val-is-not-an-integer
                    slice-when-val-is-not-an-integer
                    ;;bvxor-when-x-is-not-an-integer
                    ;;bvxor-when-y-is-not-an-integer
                    ))

;todo: use TRIM instead of bvchop?
(defthm logext-trim-arg
  (implies (and (bind-free (bind-var-to-bv-term-size 'newsize x) (newsize))
                (< size newsize)
                (natp size)
                (< 0 size)
                (natp newsize)
                (integerp x))
           (equal (logext size x)
                  (logext size (bvchop size x)))))

;rename
(defthmd plus-becomes-bvplus
  (implies (and (bind-free (bind-var-to-bv-term-size 'xsize x))
                (bind-free (bind-var-to-bv-term-size 'ysize y))
                (force (unsigned-byte-p-forced xsize x))
                (force (unsigned-byte-p-forced ysize y))
                (posp xsize))
           (equal (+ x y)
                  (bvplus (+ 1 (max xsize ysize)) x y)))
  :hints (("Goal"
           :use (:instance expt-is-weakly-increasing-for-base>1
                           (r 2)
                           (i (min xsize ysize))
                           (j (max xsize ysize)))
           :in-theory (e/d (bvplus unsigned-byte-p unsigned-byte-p-forced)
                           (expt-is-weakly-increasing-for-base>1
                            <-of-expt-and-expt-same-base)))))

(theory-invariant (incompatible (:definition bvplus) (:rewrite plus-becomes-bvplus)))

;rename
(defthmd plus-becomes-bvplus-arg1-free
  (implies (and (unsigned-byte-p xsize x)
                (bind-free (bind-var-to-bv-term-size 'ysize y))
                (force (unsigned-byte-p-forced ysize y))
                (posp xsize))
           (equal (+ x y)
                  (bvplus (+ 1 (max xsize ysize)) x y)))
  :hints (("Goal" :use plus-becomes-bvplus
           :in-theory (disable plus-becomes-bvplus))))

(theory-invariant (incompatible (:definition bvplus) (:rewrite plus-becomes-bvplus-arg1-free)))

;rename
(defthmd plus-becomes-bvplus-arg2-free
  (implies (and (unsigned-byte-p ysize y)
                (bind-free (bind-var-to-bv-term-size 'xsize x))
                (force (unsigned-byte-p-forced xsize x))
                (posp ysize))
           (equal (+ x y)
                  (bvplus (+ 1 (max xsize ysize)) x y)))
  :hints (("Goal" :use plus-becomes-bvplus-arg1-free
                  :in-theory (disable plus-becomes-bvplus-arg1-free))))

(theory-invariant (incompatible (:definition bvplus) (:rewrite plus-becomes-bvplus-arg2-free)))
