; Mixed theorems about bit-vector operations
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "rules")
(include-book "bvashr")
(local (include-book "kestrel/library-wrappers/arithmetic-inequalities" :dir :system))
;(local (include-book "arith"))
(local (include-book "rules0"))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/library-wrappers/ihs-quotient-remainder-lemmas" :dir :system)) ;drop
(local (include-book "kestrel/library-wrappers/ihs-logops-lemmas" :dir :system)) ;drop

;bozo drop any special cases
(defthm slice-bound
  (implies (and (syntaxp (and (quotep k)
                              (quotep high)
                              (quotep low)))
                (<= (expt 2 (+ 1 high (- low))) k)
                (<= low high) ;bozo
                (natp high)
                (natp low)
                )
           (< (slice high low x) k))
  :hints (("Goal" :use (:instance UNSIGNED-BYTE-P-OF-SLICE (n (+ 1 high (- low))))
           :in-theory (e/d (UNSIGNED-BYTE-P)( UNSIGNED-BYTE-P-OF-SLICE UNSIGNED-BYTE-P-OF-SLICE-GEN)))))

(defthm slice-of-bitand-too-high
  (implies (and (<= 1 low)
                (natp low))
           (equal (slice high low (bitand x y))
                  0))
  :hints (("Goal" :in-theory (enable bitand slice-too-high-is-0))))

;rename
(defthmd bvplus-recollapse
  (implies (and (integerp x) ;these are new, since bvplus ifixes its args
                (integerp y))
           (equal (bvchop size (+ x y))
                  (bvplus size x y)))
  :hints (("Goal" :in-theory (enable bvplus))))

(theory-invariant (incompatible (:definition bvplus) (:rewrite bvplus-recollapse)))

;here we drop the bvchop (and thus avoid conflicts with the anti-bvplus rules)
(defthmd bvplus-opener
  (implies (and (unsigned-byte-p size (+ x y))
                (natp size)
                (integerp x)
                (integerp y))
           (equal (bvplus size x y)
                  (+ x y)))
  :hints (("Goal" :in-theory (e/d (bvplus) (;anti-bvplus
                                            )))))

(defthm lessthan-256-backchain
  (implies (and (unsigned-byte-p 8 x))
           (< x 256)))

(defthm plus-bvcat-with-0-special
  (implies (and (unsigned-byte-p n x)
                (natp m)
                (natp n))
           (equal (+ x (BVCAT m y n 0))
                  (bvcat m y n x)))
  :hints (("Goal" :in-theory (e/d (BVCAT LOGAPP) ()))))


;deprecate!
(defun bind-newsize2-to-unsigned-term-size (x)
  (declare (xargs :guard (pseudo-termp x)))
  (let ((newsize (unsigned-term-size x)))
    (if (natp newsize)
        (acons 'newsize2
               (list 'quote newsize)
               nil)
      nil)))

;the complication here is because of how we associate bvcat...
;restrict to when y is a bvcat?
(defthm plus-bvcat-with-0
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize y) (newsize))
                (bind-free (bind-newsize2-to-unsigned-term-size x) (newsize2))
                (equal 0 (bvchop newsize2 y))
                (natp newsize)
                (< 1 newsize)
                (natp newsize2)
                (force (unsigned-byte-p newsize2 x))
                (force (unsigned-byte-p newsize y)))
           (equal (+ x y)
                  (bvcat (- newsize newsize2) (slice (+ -1 newsize) newsize2 y) newsize2 x)))
  :hints (("Goal"
           :use (:instance split-bv (n newsize) (m newsize2))
           :in-theory (e/d (BVCAT LOGAPP bvchop)
                           (mod-=-0
                            NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG)))))

(defthm plus-bvcat-with-0-alt
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize y) (newsize))
                (bind-free (bind-newsize2-to-unsigned-term-size x) (newsize2))
                (equal 0 (bvchop newsize2 y))
                (natp newsize)
                (< 1 newsize)
                (natp newsize2)
                (force (unsigned-byte-p newsize2 x))
                (force (unsigned-byte-p newsize y)))
           (equal (+ y x)
                  (bvcat (- newsize newsize2) (slice (+ -1 newsize) newsize2 y) newsize2 x)))
  :hints (("Goal" :use (:instance plus-bvcat-with-0)
           :in-theory (disable plus-bvcat-with-0))))

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

;; These loop (note that <-UNARY-/-POSITIVE-LEFT <-UNARY-/-POSITIVE-RIGHT should probably have syntaxp hyps added).
(theory-invariant (incompatible (:rewrite collect-constants-<-/) (:rewrite <-unary-/-positive-left)))
(theory-invariant (incompatible (:rewrite collect-constants-<-/-two) (:rewrite <-unary-/-positive-right)))

;; (thm
;;  (equal (SLICE '19 '14 (bvcat '8 y '8 x))
;;         (slice



;bozo drop some hyps

(defthm slice-tighten-top
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize x) (newsize))
                (<= newsize high) ; prevents loops
                (force (unsigned-byte-p-forced newsize x))
                (natp low)
                (natp newsize)
;                (integerp newsize)
                (natp high))
           (equal (slice high low x)
                  (slice (+ -1 newsize) low x)))
  :hints (("Goal" :cases ((equal 0 low)
                          (<= low newsize))
           :in-theory (e/d (slice UNSIGNED-BYTE-P-FORCED) (anti-slice)))))

;move or drop?
(defun bind-newsize-to-constant-size (x)
  (declare (xargs :guard (and (quotep x)
                              (pseudo-termp x)
                              (natp (unquote x)))

                  ))
  (acons 'newsize
         (list 'quote (integer-length (unquote x)))
         nil))

(defthm bvand-of-constant-tighten
   (implies (and (syntaxp (and (quotep k)
                               (< (integer-length (unquote k))
                                  (unquote size))))
                 (bind-free (bind-newsize-to-constant-size k) (newsize))
                 (unsigned-byte-p newsize k)
                 (< newsize size)
                 (integerp x)
                 (natp size)
                 (natp newsize)
                 )
            (equal (bvand size k x)
                   (bvand newsize k x)))
   :hints (("Goal" :in-theory (enable bvand-tighten-1))))

;fixme change to go to bvif?
(defthmd getbit-of-if
  (equal (getbit n (if test a b))
         (if test (getbit n a) (getbit n b))))

;for axe
(defthmd getbit-test-is-self
  (equal (if (equal 1 (getbit x n)) 1 0)
         (getbit x n)))

(defthmd times-of-2-and-bvchop-of-sub-1
  (implies (and (posp n)
                (integerp x))
           (equal (* 2 (BVCHOP (+ -1 N) x))
                  (bvchop n (* 2 x))))
  :hints (("Goal" :in-theory (e/d (bvchop mod-expt-split)
                                  (MOD-OF-EXPT-OF-2 mod-of-expt-of-2-constant-version)))))

(defthmd split-when-low-bit-1
  (implies (and (INTEGERP X)
                (integerp y)
                (EQUAL 1 (BVCHOP 1 X)))
           (equal (+ 1 (* 2 (floor x 2)))
                  x))
  :hints (("Goal" :in-theory (e/d (bvchop mod) (BVCHOP-1-BECOMES-GETBIT
                                                 MOD-OF-EXPT-OF-2
                                                 mod-of-expt-of-2-constant-version
                                                 ;;MOD-RECOLLAPSE-LEMMA2
                                                 ;;MOD-RECOLLAPSE-LEMMA
                                                 )))))

(defthmd split-when-low-bit-0
  (implies (and (INTEGERP X)
                (integerp y)
                (EQUAL 0 (BVCHOP 1 X)))
           (equal (* 2 (floor x 2))
                  x))
  :hints (("Goal" :in-theory (e/d (bvchop mod) (MOD-OF-EXPT-OF-2
                                                 mod-of-expt-of-2-constant-version
                                                 BVCHOP-1-BECOMES-GETBIT
                                                 ;;MOD-RECOLLAPSE-LEMMA2
                                                 ;;MOD-RECOLLAPSE-LEMMA
                                                 )))))

(defthm split-when-low-bit-1-hack
  (implies (and (INTEGERP X)
                (integerp y)
                (EQUAL 1 (BVCHOP 1 X)))
           (equal (+ Y (* 2 Y (FLOOR X 2)))
                  (* x y)))
  :hints (("Goal" :use (:instance split-when-low-bit-1))))

(defthm split-when-low-bit-0-hack
  (implies (and (INTEGERP X)
                (integerp y)
                (EQUAL 0 (BVCHOP 1 X)))
           (equal (* 2 Y (FLOOR X 2))
                  (* x y)))
  :hints (("Goal" :use (:instance split-when-low-bit-0)
           :in-theory (disable BVCHOP-1-BECOMES-GETBIT))))

(defthmd blast-bvmult-into-bvplus
  (implies (and (natp n)
                (integerp x)  ;new
                (integerp y)  ;new
                (< 0 n))
           (equal (bvmult n x y)
                  (bvplus n
                          (bvif n (equal 1 (getbit 0 x)) y 0)
                          (bvcat (+ -1 n) (bvmult (+ -1 n) (slice (+ -1 n) 1 x) y)
                                 1 0))))
  :hints (("Goal"
           :in-theory (e/d (bvmult bvif bvplus bvcat logapp slice logtail
                                   getbit
                                   split-when-low-bit-1-hack
                                   split-when-low-bit-0-hack
;bvchop
                                   times-of-2-and-bvchop-of-sub-1)
                           (bvchop-of-*
                            BVCHOP-SHIFT-GEN-CONSTANT-VERSION
                            BVCHOP-SHIFT
                            anti-slice
;                            anti-bvplus
                            )))))

(in-theory (disable logmaskp)) ;move

(defthmd blast-bvmult-into-bvplus-constant-version-arg2
  (implies (and (syntaxp (quotep y))
                (integerp x)  ;new
                (integerp y)  ;new
                (natp n)
                (< 0 n))
           (equal (bvmult n x y)
                  (bvplus n (bvif n (equal 1 (getbit 0 x)) y 0)
                          (bvcat (+ -1 n)
                                 (bvmult (+ -1 n) (slice (+ -1 n) 1 x) y)
                                 1 0))))
  :hints (("Goal" :in-theory (e/d (blast-bvmult-into-bvplus) (bvmult-commutative)))))

(DEFTHMd BLAST-BVMULT-INTO-BVPLUS-constant-version-arg1
  (IMPLIES (AND (syntaxp (quotep y))
                (integerp x)  ;new
                (integerp y)  ;new
                (NATP N)
                (< 0 N))
           (EQUAL (BVMULT N Y X)
                  (BVPLUS N (BVIF N (EQUAL 1 (GETBIT 0 X)) Y 0)
                          (BVCAT (+ -1 N)
                                 (BVMULT (+ -1 N) (SLICE (+ -1 N) 1 X) Y)
                                 1 0))))
  :HINTS (("Goal" :use (:instance BLAST-BVMULT-INTO-BVPLUS-constant-version-arg2))))

;might this be bad, if a bvplus is used to separate 2 big xor nests?
(defthm getbit-0-of-plus
  (implies (and (integerp x)
                (integerp y))
           (equal (getbit 0 (+ x y))
                  (bitxor x y)))
  :hints (("Goal" :in-theory (e/d (getbit bitxor-split)
                                  (bvchop-1-becomes-getbit slice-becomes-getbit
;bvplus-recollapse
                                                            )))))

;gen? go to bvplus?
(defthm bvchop-1-of-plus
  (implies (and (integerp x)
                (integerp y))
           (equal (bvchop 1 (+ X Y))
                  (bitxor x y)))
  :hints (("Goal" :in-theory (e/d (getbit bitxor-split)
                                  (BVCHOP-1-BECOMES-GETBIT SLICE-BECOMES-GETBIT
;                                                          BVPLUS-RECOLLAPSE
)))))


(defthmd logtail-1-of-+
  (implies (and (integerp x)
                (integerp y))
           (equal (logtail 1 (+ x y))
                  (if (and (equal (mod x 2) 1)
                           (equal (mod y 2) 1))
                      (+ 1 (+ (logtail 1 x)
                              (logtail 1 y)))
                    (+ (logtail 1 x)
                       (logtail 1 y)))))
  :hints (("Goal" :in-theory (enable logtail floor-of-sum))))

(defthmd blast-bvplus
  (implies (posp n)
           (equal (bvplus n x y)
                  (bvcat (+ -1 n)
                         (bvplus (+ -1 n)
                                 (slice (+ -1 n) 1 x)
                                 (bvplus (+ -1 n)
                                         (slice (+ -1 n) 1 y)
                                         ;;carry bit:
                                         (bvand 1 x y)))
                         1
                         (bitxor x y))))
  :hints (("Goal"
           :expand ((BVCHOP 1 X)
                    (BVCHOP 1 y))
           :in-theory (e/d (bvplus getbit logtail-1-of-+
                                   bvand-1-split
                                   LOGTAIL-OF-BVCHOP
                                   slice
                                   SLICE-WHEN-VAL-IS-NOT-AN-INTEGER
                                   GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER
                                   BITXOR-SPLIT)
                           (;anti-bvplus
                            MOD-OF-EXPT-OF-2
                            mod-of-expt-of-2-constant-version
                            anti-slice
                            ;hack-6
                            BVCHOP-OF-LOGTAIL)))))


;helps in blasting.  can we do this cheaper?!
;; (skip -proofs
;;  (defthm bvmult-27-bvcat-hack
;;    (implies (and ;(integerp x)
;; ;(integerp y)
;; ;(integerp z)
;; ;(integerp w)
;;              )
;;             (equal (bvmult 32 27 (BVCAT '8 (BVCAT '1 x '7 0) '17 (BVCAT '8 (BVCAT '1 y '7 0) '9 (BVCAT '8 (BVCAT '1 w '7 0) '1 z))))
;;                    (BVCAT
;;                     3 0 29
;;                     (BVCAT
;;                      1 (GETBIT 0 X)
;;                      28
;;                      (BVCAT
;;                       1 (GETBIT 0 X)
;;                       27
;;                       (BVCAT
;;                        1 0 26
;;                        (BVCAT
;;                         1 (GETBIT 0 X)
;;                         25
;;                         (BVCAT
;;                          1 (GETBIT 0 X)
;;                          24
;;                          (BVCAT
;;                           3 0 21
;;                           (BVCAT
;;                            1 (GETBIT 0 Y)
;;                            20
;;                            (BVCAT
;;                             1 (GETBIT 0 Y)
;;                             19
;;                             (BVCAT
;;                              1 0 18
;;                              (BVCAT
;;                               1 (GETBIT 0 Y)
;;                               17
;;                               (BVCAT
;;                                1 (GETBIT 0 Y)
;;                                16
;;                                (BVCAT
;;                                 3 0 13
;;                                 (BVCAT
;;                                  1 (GETBIT 0 W)
;;                                  12
;;                                  (BVCAT
;;                                   1 (GETBIT 0 W)
;;                                   11
;;                                   (BVCAT
;;                                    1 0 10
;;                                    (BVCAT
;;                                     1 (GETBIT 0 W)
;;                                     9
;;                                     (BVCAT
;;                                      1 (GETBIT 0 W)
;;                                      8
;;                                      (BVCAT
;;                                       3 0 5
;;                                       (BVCAT
;;                                        1 (GETBIT 0 Z)
;;                                        4
;;                                        (BVCAT
;;                                         1 (GETBIT 0 Z)
;;                                         3
;;                                         (BVCAT 1 0 2
;;                                                (BVCAT 1 (GETBIT 0 Z)
;;                                                       1 (GETBIT 0 Z))))))))))))))))))))))))))
;;    :hints (("Goal" :in-theory (disable BVCAT-EQUAL-REWRITE
;; ;                                      BVAND-OF-BVCAT-TIGHTEN-LOW
;;                                        )))))

(defthm trim-of-bvplus
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2))
           (equal (trim size1 (bvplus size2 x y))
                  (bvplus size1 x y)))
  :hints (("Goal" :in-theory (e/d (trim) nil))))

(defthm trim-of-bvmult
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2))
           (equal (trim size1 (bvmult size2 y z))
                  (bvmult size1 y z)))
  :hints (("Goal" :in-theory (e/d ( trim) nil))))

(defthm trim-of-bvminus
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2))
           (equal (trim size1 (bvminus size2 y z))
                  (bvminus size1 y z)))
  :hints (("Goal" :in-theory (e/d (bvuminus trim) (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

(defthm trim-of-bvuminus
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2))
           (equal (trim size1 (bvuminus size2 x))
                  (bvuminus size1 x)))
  :hints (("Goal" :in-theory (e/d (trim) nil))))

(defthm trim-of-bvand
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2))
           (equal (trim size1 (bvand size2 y z))
                  (bvand size1 y z)))
  :hints (("Goal" :in-theory (e/d ( trim) nil))))

(defthm trim-of-bvor
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2))
           (equal (trim size1 (bvor size2 y z))
                  (bvor size1 y z)))
  :hints (("Goal" :in-theory (enable trim)))) ;bozo

(defthm trim-of-bvxor
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2))
           (equal (trim size1 (bvxor size2 y z))
                  (bvxor size1 y z)))
  :hints (("Goal" :in-theory (enable trim))))

(defthm trim-of-bvchop
  (equal (trim size1 (bvchop size i))
         (if (< (ifix size1) (ifix size))
             (bvchop size1 i)
           (bvchop size i)))
  :hints (("Goal" :in-theory (enable trim))))

(defthm trim-of-bvnot
  (implies (and (<= n size) (natp n) (natp size))
           (equal (trim n (bvnot size val))
                  (bvnot n val)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd mod-becomes-bvmod-better-free-and-free
  (implies (and (unsigned-byte-p xsize x) ;xsize is a freevar
                (unsigned-byte-p ysize y)) ;ysize is a freevar
           (equal (mod x y)
                  (bvmod (max xsize ysize) x y)))
  :hints (("Goal"
           :use (:instance mod-becomes-bvmod-core (size (max xsize ysize)))
           :in-theory (enable ;mod-becomes-bvmod-core
                       unsigned-byte-p-forced))))

(defthm recollapse-hack-helper
  (implies (and (equal free1 (bvchop size x))
                (natp size)
                (syntaxp (quotep free1))
                (not (equal 0 (getbit size x)))
                (unsigned-byte-p (+ 1 size) x))
           (equal x
                  (bvcat 1 1 size free1)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable ;TRIM-TO-N-BITS-META-RULE-FOR-BVCAT
;                                      GETBIT-EQUAL-0-POLARITY
                                      ))))

;or we could rewrite the < into a bvlt or sbvlt...
; this may loop when k=2^32 since this backchains from < to unsigned-byte-p?
(defthm <-when-sbvlt-constants
  (implies (and (syntaxp (quotep k))
                (sbvlt 32 x free)
                (syntaxp (quotep free))
                (unsigned-byte-p 31 free) ;should get computed
                (<= free k) ;should get computed
                (< k (expt 2 31)) ;prevent loops between x<2^32 and (unsigned-byte-p 32 x) -- trying 31 here instead of 32
                (unsigned-byte-p 32 x)
                (not (sbvlt 32 x 0)))
           (< x k))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthm myif-with-logxor-on-one-branch
  (implies (integerp x)
           (equal (myif test x (logxor k x))
                  (logxor (myif test 0 k) x)))
  :hints (("Goal" :in-theory (enable myif))))

;rename
(DEFTHM <-LEMMA-FOR-KNOWN-OPERATORS-alt-non-dag
  (IMPLIES (AND (syntaxp (QUOTEP K))
                (bind-free (bind-var-to-unsigned-term-size 'xsize x))
                (<= (+ -1 (EXPT 2 XSIZE)) K)
                (UNSIGNED-BYTE-P XSIZE X))
           (not (< K X)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))


;just a special case of bvchop ident?  make a more general version of that rule?
(defthm bvchop-of-bvminus2
  (implies (and (<= size2 size1)
                (natp size1)
                (natp size2))
           (equal (bvchop size1 (bvminus size2 y z))
                  (bvminus size2 y z))))

(DEFTHM <-LEMMA-FOR-KNOWN-OPERATORS-NON-DAG
  (IMPLIES (AND (SYNTAXP (QUOTEP K))
                (BIND-FREE (BIND-VAR-TO-UNSIGNED-TERM-SIZE 'XSIZE
                                                           X))
                (<= (EXPT 2 XSIZE) K)
                (UNSIGNED-BYTE-P XSIZE X))
           (< X K))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

;skips the syntaxp hyp...
(defthm slice-bound-2
  (implies (and (<= (expt 2 (+ 1 high (- low))) k)
                (<= low high)
                (natp high)
                (natp low))
           (< (slice high low x) k))
  :hints (("Goal" :use (:instance slice-bound)
           :in-theory (disable slice-bound))))

;gen
(defthm bvor-appending-idiom-low
  (implies (and (equal n2 (- 32 n))
                (natp n)
                (natp n2)
                (unsigned-byte-p n x))
           (equal (bvor 32 (bvcat n2 y n 0) x)
                  (bvcat n2 y n x)))
  :hints (("Goal" :in-theory (enable slice-too-high-is-0))))

;gen
(defthm bvor-appending-idiom-low-alt
  (implies (and (equal n2 (- 32 n))
                (natp n)
                (natp n2)
                (unsigned-byte-p n x))
           (equal (bvor 32 x (bvcat n2 y n 0))
                  (bvcat n2 y n x))))

; a version that puts a bvchop around x to help us simplify stuff
(defthm bvshl-rewrite-with-bvchop
  (implies (and (<= shift-amount width)
                (natp shift-amount)
                (integerp width))
           (equal (bvshl width x shift-amount)
                  (bvcat (- width shift-amount) (bvchop (- width shift-amount) x) shift-amount 0)))
  :hints (("Goal" :in-theory (enable bvshl))))

;i don't think I like the bvchop here... trim rules should take care of that...
(defthm bvshl-rewrite-with-bvchop-for-constant-shift-amount
  (implies (and (syntaxp (quotep shift-amount))
                (syntaxp (quotep width)) ; will usually be true
                (<= shift-amount width)
                (natp shift-amount)
                (integerp width))
           (equal (bvshl width x shift-amount)
                  (bvcat (- width shift-amount)
                         (bvchop (- width shift-amount) x)
                         shift-amount
                         0)))
  :hints (("Goal" :by bvshl-rewrite-with-bvchop)))

;kill
;bozo gen
;think about which way we prefer this...
;trying disabled...
(defthmd usb-hack
  (implies (unsigned-byte-p 8 x)
           (equal (unsigned-byte-p 7 x)
                  (equal 0 (getbit 7 x))))
  :hints (("Goal"
           :use (:instance bvcat-of-getbit-and-x-adjacent (n 7))
           :in-theory (e/d (getbit-too-high bvcat-of-0) (bvcat-of-getbit-and-x-adjacent bvcat-equal-rewrite BVCAT-EQUAL-REWRITE-ALT)))))




;fixme we probably need a lot more rules like this to add sizes (we need sizes
;in the if nest, since there can be logexts to be gotten rid of at the leaves
;of the if nest)
(defthm bvor-of-myif-arg2
  (equal (bvor n x (myif test a b))
         (bvor n x (bvif n test a b)))
  :hints (("Goal" :in-theory (enable myif bvif bvor))))

(defthm bvor-of-myif-arg1
  (equal (bvor n (myif test a b) x)
         (bvor n (bvif n test a b) x))
  :hints (("Goal" :in-theory (enable myif bvif bvor))))

(defthm bvcat-of-myif-arg2
  (implies (and (Natp highsize)
                (<= 1 highsize)
                (natp lowsize))
           (equal (bvcat highsize (myif test a b) lowsize lowval)
                  (bvcat highsize (bvif highsize test a b) lowsize lowval)))
  :hints (("Goal" :in-theory (enable myif bvif))))

(defthm bvcat-of-myif-arg4
  (implies (and (Natp highsize)
                (<= 1 highsize)
                (natp lowsize))
           (equal (bvcat highsize highval lowsize (myif test a b))
                  (bvcat highsize highval lowsize (bvif lowsize test a b))))
  :hints (("Goal" :in-theory (enable myif bvif))))

(local
 (defun induct-floor-and-sub1 (x n)
   (if (zp n)
       (list x n)
     (induct-floor-and-sub1 (floor x 2) (+ -1 n)))))

;move
(defthm logand-of-minus-of-expt
  (implies (and (natp n)
                (integerp x)
                (< x 0)
                (<= (- (expt 2 n)) x))
           (equal (logand (- (expt 2 n)) x)
                  (- (expt 2 n))))
  :hints (("Subgoal *1/2" :use (:instance floor-weak-monotone
                                          (i1 (- (expt 2 n)))
                                          (i2 x)
                                          (j 2))
           :expand (logand x (- (expt 2 n)))
           :in-theory (e/d (expt-of-+ ;fl
                            mod-=-0
                            mod-expt-split)
                           (MOD-OF-EXPT-OF-2
                            mod-of-expt-of-2-constant-version
                            floor-unique-equal-version
                            floor-weak-monotone ;hack-6
                            )))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (induct-floor-and-sub1 x n)
           :expand (logand x (- (expt 2 n)))
           :in-theory (e/d (lognot logand ;fl
                                   expt-of-+
                                   mod-expt-split)
                           (;hack-6                     ;ffixme
                            ;EQUAL-OF-EXPT-AND-CONSTANT ;fixme
                            )))))

(defthm logand-of-minus-of-expt-alt
  (implies (and (natp n)
                (integerp x)
                (< x 0)
                (<= (- (expt 2 n)) x))
           (equal (logand x (- (expt 2 n)))
                  (- (expt 2 n))))
  :hints (("Goal" :use (:instance logand-of-minus-of-expt)
           :in-theory (disable logand-of-minus-of-expt))))

(defthm logand-of-minus-of-expt-and-lognot
  (implies (and (natp n)
                (unsigned-byte-p n x))
           (equal (logand (- (expt 2 n)) (lognot x))
                  (- (expt 2 n))))
  :hints (("Goal" :in-theory (e/d (lognot logand
                                          expt-of-+
                                          ;;INTEGER-TIGHTEN-BOUND ;why?
                                          )
                                  (size-non-negative-when-unsigned-byte-p-free)))))

(defthm logior-of-all-ones
  (implies (and (natp n)
                (unsigned-byte-p n x))
           (equal (logior (+ -1 (expt 2 n)) x)
                  (+ -1 (expt 2 n))))
  :hints (("Goal" :in-theory (e/d (logior) (lognot-of-logand)))))

(defthmd getbit-of-bvif-quoteps
  (implies (and (syntaxp (quotep thenpart))
                (syntaxp (quotep elsepart))
                (syntaxp (quotep n))
                (syntaxp (quotep size))
                (< n size)
                (natp n)
                (integerp size)
                )
           (equal (getbit n (bvif size test thenpart elsepart))
                  (bvif 1 test (getbit n thenpart) (getbit n elsepart))))
  :hints (("Goal" :in-theory (enable bvif myif))))


(DEFTHM UNSIGNED-BYTE-P-OF-MYIF-strong
  (equal (UNSIGNED-BYTE-P N (MYIF TEST A B))
         (myif test (UNSIGNED-BYTE-P N A)
               (UNSIGNED-BYTE-P N B)))
  :HINTS (("Goal" :IN-THEORY (ENABLE MYIF))))


;go to bvif!
(defthmd slice-of-myif-consant-branches
  (implies (and (syntaxp (quotep high))
                (syntaxp (quotep low))
                (syntaxp (quotep x))
                (syntaxp (quotep y)))
           (equal (slice high low (myif test x y))
                  (myif test (slice high low x) (slice high low y))))
  :hints (("Goal" :in-theory (enable myif bvif))))

;bbozo gen
;drop?
(defthm unsigned-byte-p-of-bvchop-of-logext-7-32-8
  (implies (integerp x)
           (equal (unsigned-byte-p 7 (bvchop 32 (logext 8 x)))
                  (unsigned-byte-p 7 (bvchop 8 x))))
  :hints (("Goal" :in-theory (e/d (bvsx) (;BVCHOP-32-LOGEXT-8
                                          )))))



(defthm getbit-of-bvor-when-other-bit-is-0-arg1
  (implies (and (equal (getbit n x) 0)
                (< n size)
                (natp n)
                (natp size))
           (equal (getbit n (bvor size x y))
                  (getbit n y))))

(defthm getbit-of-bvor-when-other-bit-is-0-arg2
  (implies (and (equal (getbit n x) 0)
                (< n size)
                (natp n)
                (natp size))
           (equal (getbit n (bvor size y x))
                  (getbit n y))))

;; (skip -proofs
;;  (defthmd floor-when-not-evenp
;;    (implies (and (not (evenp x))
;;                  (integerp x))
;;             (equal (floor x 2)
;;                    (+ -1/2 (/ x 2))))
;;    :hints (("Goal" :in-theory (enable evenp)
;;             :use (:instance FLOOR-UNIQUE  (i x) (j 2) (n (+ -1/2 (/ x 2))))))))

;; (logand -2 -3) = -4
;; (defthm logand-bound-when-negative
;;    (implies (and (< k x)
;;                  (< k y)
;;                  (< x 0)
;;                  (< y 0)
;;                  (integerp x)
;;                  (integerp y)
;;                  (integerp k)
;;                  (< k 0))
;;             (equal (< k (logand x y))
;;                    t))
;;    :hints (("Goal"
;;             :do-not '(generalize eliminate-destructors)
;;             :induct (triple-floor-by-2-induct x y k)
;;             :in-theory (e/d (logand  floor-when-evenp floor-when-not-evenp) ()))))

;; ;note that (logior 1 4)=5
;; (defthm logior-bound
;;   (implies (and (< x k)
;;                 (< y k)
;;                 (natp x)
;;                 (natp y)
;;                 (natp k))
;;            (equal (< (logior x y) k)
;;                   t))
;;   :hints
;;   (("Goal"
;;     :in-theory (e/d (logior lognot
;;                      ) (LOGNOT-OF-LOGAND)))))

;; ;note that (logxor 1 4)=5
;; (DEFTHM logxor-BOUND
;;    (IMPLIES (AND (< x K)
;;                  (< y K)
;;                  (Natp x)
;;                  (Natp y)
;;                  (natp k))
;;             (EQUAL (< (logxor X Y) K)
;;                    T))
;;    :HINTS
;;    (("Goal"
;;      :in-theory (e/d (logxor ;lognot
;;                       logeqv LOGORC1) (LOGXOR-BVCHOP-BVCHOP)))))

;; ;proveme! not true!
;; ;(bvxor 32 1 4)=5
;; (skip -proofs
;; (DEFTHM BVXOR-BOUND-3
;;    (IMPLIES (AND (< (bvchop size x) K)
;;                  (< (bvchop size y) K)
;; ;                 (integerp x)
;;  ;                (integerp y)
;;                  (natp k)
;;                  (< k (expt 2 size)) ;drop?
;;                  (NATP SIZE))
;;             (EQUAL (< (BVXOR SIZE X Y) K)
;;                    T))
;;    :HINTS
;;    (("Goal"
;;      :in-theory (e/d (BVXOR) (LOGXOR-BVCHOP-BVCHOP))))))

(defthmd <-of-myif-arg1
  (implies (and (syntaxp (quotep k)))
           (equal (< (myif test a b) k)
                  (myif test (< a k) (< b k))))
  :hints (("Goal" :in-theory (enable myif))))

;; ;bozo gen
;; (DEFTHM BVOR-6--64-HACK2
;;   (equal (< (BVOR 6 X Y) 64)
;;          t)
;;   :HINTS
;;   (("Goal"
;;     :USE (:INSTANCE UNSIGNED-BYTE-P-OF-BVOR-GEN (SIZE 6)
;;                     (SIZE2 6))
;;     :IN-THEORY (ENABLE UNSIGNED-BYTE-P))))


;; ;proveme!
;; ;note that (bvor 32 1 4)=5 !!
;; (skip -proofs
;; (DEFTHM BVOR-BOUND-3
;;    (IMPLIES (AND (< 0 k) ;otherwise the < is nil
;;                  (< (bvchop size x) K)
;;                  (< (bvchop size y) K)
;;                  (integerp x)
;;                  (integerp y)
;;                  (natp k)
;;                  (< k (expt 2 size)) ;drop?
;;                  (NATP SIZE))
;;             (EQUAL (< (BVOR SIZE X Y) K)
;;                    T))
;;    :HINTS
;;    (("Goal"
;;      :in-theory (e/d (BVOR logior) (;LOGIOR-BVCHOP-BVCHOP
;;                                     LOGNOT-OF-LOGAND
;;                                 ))))))


(DEFTHM natp-of-myif2
  (IMPLIES (AND (natp A)
                (natp B))
           (natp (MYIF TEST A B)))
  :HINTS (("Goal" :IN-THEORY (ENABLE MYIF))))

(defthm bvcat-bound-hack-1
  (implies (integerp x)
           (equal (< (BVCAT 31 x 1 0) 64)
                  (< (bvchop 31 x) 32)))
  :hints (("Goal" :in-theory (e/d (bvcat logapp) ()))))

(defthm logext-64-bound-hack
  (implies (integerp x)
           (equal (< (logext 32 x) 64)
                  (or (equal 1 (getbit 31 x))
                      (< (bvchop 31 x) 64))))
  :hints (("Goal" :in-theory (e/d (logext LOGAPP-0) (TIMES-4-BECOMES-LOGAPP)))))

(defthm <-bvchop-31-x-64
  (implies (and (< x 64)
                (natp x))
           (< (bvchop 31 x) 64)))

(defthm <-bvchop-32-x-64
  (implies (and (< x 64)
                (natp x))
           (< (bvchop 32 x) 64)))

(defthm logext-64-bound-hack-8
  (implies (integerp x)
           (equal (< (logext 8 x) 64)
                  (or (equal 1 (getbit 7 x))
                      (< (bvchop 7 x) 64))))
  :hints (("Goal" :in-theory (e/d (logext LOGAPP-0) (TIMES-4-BECOMES-LOGAPP)))))





;; ;bozo gen
;; (defthm bvchop-32-logext-8
;;   (implies (integerp x)
;;            (equal (bvchop 32 (logext 8 x))
;;                   (bvcat 25 (repeatbit 25 (getbit 7 x))
;;                          7 (bvchop 7 x)))))

;drop?
(defthm bvcat-0-<-hack
  (implies (natp n)
           (equal (< (bvcat n '0 '7 x) '64)
                  (< (bvchop 7 x) 64))))

(defthm bvcat-bound-hack-2
  (implies (integerp x)
           (equal (< (BVCAT 27 x 5 y) 64)
                  (< (bvchop 27 x) 2)))
  :hints (("Goal" :in-theory (e/d (bvcat logapp) ()))))

;bozo more generally, turn if into bvif if we can figure out the sizes?
(defthmd myif-of-constants-becomes-bvif
  (implies (and (syntaxp (quotep y))
                (syntaxp (quotep z))
                (natp y)
                (natp z)
                )
           (equal (myif x y z)
                  (bvif (max (integer-length y)
                             (integer-length z))
                        x
                        y
                        z)))
  :hints (("Goal" :in-theory (enable bvif myif unsigned-byte-p-of-integer-length-gen))))

(defthm signed-byte-p-of-bvif
  (implies (and (< size n)
                (natp size)
                (natp n))
           (signed-byte-p n (bvif size test a b)))
  :hints (("Goal" :in-theory (enable myif))))

;bbozo more like this
;or, better yet, do something more general and syntactic
(defthm myif-of-bvcat-becomes-bvif-arg1
  (implies (and (unsigned-byte-p (+ highsize lowsize) y)
                (natp lowsize)
                (natp highsize))
           (equal (myif test (bvcat highsize highval lowsize lowval) y)
                  (bvif (+ highsize lowsize) test (bvcat highsize highval lowsize lowval) y)))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm myif-of-bvcat-becomes-bvif-arg2
  (implies (and (unsigned-byte-p (+ highsize lowsize) y)
                (natp lowsize)
                (natp highsize))
           (equal (myif test y (bvcat highsize highval lowsize lowval))
                  (bvif (+ highsize lowsize) test y (bvcat highsize highval lowsize lowval))))
  :hints (("Goal" :in-theory (enable bvif myif))))

;bozo rename to have trim in the name?
;just use trim lemma?
(defthmd bitxor-of-bvif-arg1
  (implies (and (syntaxp (quotep size))
                (< 1 size) ;otherwise this might loop
                (integerp size))
           (equal (bitxor (bvif size test x y) z)
                  (bitxor (bvif 1 test x y) z)))
  :hints (("Goal" :in-theory (enable myif bvif))))

(defthmd bitxor-of-bvif-arg2
  (implies (and (syntaxp (quotep size))
                (< 1 size) ;otherwise this might loop
                (integerp size))
           (equal (bitxor z (bvif size test x y))
                  (bitxor z (bvif 1 test x y))))
  :hints (("Goal" :in-theory (enable myif bvif))))

(local (in-theory (enable myif)))

;bozo replace stuff like this with a more general syntaxp rule?
(DEFTHM MYIF-OF-bvxor-BECOMES-BVIF-ARG2
  (IMPLIES (AND (UNSIGNED-BYTE-P SIZE z)
                (NATP SIZE))
           (EQUAL (MYIF TEST z (bvxor SIZE x y))
                  (BVIF SIZE TEST z (bvxor SIZE x y))))
  :HINTS
  (("Goal" :IN-THEORY (E/D (BVIF) (BVIF-OF-MYIF-ARG2)))))

(DEFTHM MYIF-OF-bvxor-BECOMES-BVIF-ARG1
  (IMPLIES (AND (UNSIGNED-BYTE-P SIZE z)
                (NATP SIZE))
           (EQUAL (MYIF TEST (bvxor SIZE x y) z)
                  (BVIF SIZE TEST (bvxor SIZE x y) z)))
  :HINTS
  (("Goal" :IN-THEORY (E/D (BVIF) (BVIF-OF-MYIF-ARG2)))))

(in-theory (disable bvminus)) ;bozo?

;disable!
;drop?  this is for rc6?
(defthmd 32-minus-x-cases
  (implies (unsigned-byte-p 5 x)
           (equal (+ 32 (- x))
                  (IF
                   (EQUAL X '0)
                   '32
                   (IF
                    (EQUAL X '1)
                    '31
                    (IF
                     (EQUAL X '2)
                     '30
                     (IF
                      (EQUAL X '3)
                      '29
                      (IF
                       (EQUAL X '4)
                       '28
                       (IF
                        (EQUAL X '5)
                        '27
                        (IF
                         (EQUAL X '6)
                         '26
                         (IF
                          (EQUAL X '7)
                          '25
                          (IF
                           (EQUAL X '8)
                           '24
                           (IF
                            (EQUAL X '9)
                            '23
                            (IF
                             (EQUAL X '10)
                             '22
                             (IF
                              (EQUAL X '11)
                              '21
                              (IF
                               (EQUAL X '12)
                               '20
                               (IF
                                (EQUAL X '13)
                                '19
                                (IF
                                 (EQUAL X '14)
                                 '18
                                 (IF
                                  (EQUAL X '15)
                                  '17
                                  (IF
                                   (EQUAL X '16)
                                   '16
                                   (IF
                                    (EQUAL X '17)
                                    '15
                                    (IF
                                     (EQUAL X '18)
                                     '14
                                     (IF
                                      (EQUAL X '19)
                                      '13
                                      (IF
                                       (EQUAL X '20)
                                       '12
                                       (IF
                                        (EQUAL X '21)
                                        '11
                                        (IF
                                         (EQUAL X '22)
                                         '10
                                         (IF
                                          (EQUAL X '23)
                                          '9
                                          (IF
                                           (EQUAL X '24)
                                           '8
                                           (IF
                                            (EQUAL X '25)
                                            '7
                                            (IF
                                             (EQUAL X '26)
                                             '6
                                             (IF
                                              (EQUAL X '27)
                                              '5
                                              (IF
                                               (EQUAL X '28)
                                               '4
                                               (IF (EQUAL X '29)
                                                   '3
                                                   (IF (EQUAL X '30)
                                                       '2
                                                       '1))))))))))))))))))))))))))))))))))

;disable!
(defthmd 31-minus-x-cases
  (implies (unsigned-byte-p 5 x)
           (equal (+ 31 (- x))
                  (IF
 (EQUAL X '0)
 '31
 (IF
  (EQUAL X '1)
  '30
  (IF
   (EQUAL X '2)
   '29
   (IF
    (EQUAL X '3)
    '28
    (IF
     (EQUAL X '4)
     '27
     (IF
      (EQUAL X '5)
      '26
      (IF
       (EQUAL X '6)
       '25
       (IF
        (EQUAL X '7)
        '24
        (IF
         (EQUAL X '8)
         '23
         (IF
          (EQUAL X '9)
          '22
          (IF
           (EQUAL X '10)
           '21
           (IF
            (EQUAL X '11)
            '20
            (IF
             (EQUAL X '12)
             '19
             (IF
              (EQUAL X '13)
              '18
              (IF
               (EQUAL X '14)
               '17
               (IF
                (EQUAL X '15)
                '16
                (IF
                 (EQUAL X '16)
                 '15
                 (IF
                  (EQUAL X '17)
                  '14
                  (IF
                   (EQUAL X '18)
                   '13
                   (IF
                    (EQUAL X '19)
                    '12
                    (IF
                     (EQUAL X '20)
                     '11
                     (IF
                      (EQUAL X '21)
                      '10
                      (IF
                       (EQUAL X '22)
                       '9
                       (IF
                        (EQUAL X '23)
                        '8
                        (IF
                         (EQUAL X '24)
                         '7
                         (IF
                          (EQUAL X '25)
                          '6
                          (IF
                           (EQUAL X '26)
                           '5
                           (IF
                            (EQUAL X '27)
                            '4
                            (IF
                             (EQUAL X '28)
                             '3
                             (IF (EQUAL X '29)
                                 '2
                                 (IF (EQUAL X '30)
                                     '1
                                     '0))))))))))))))))))))))))))))))))))



(defthm slice-of-if
  (equal (slice (if test high1 high2) low val)
         (if test
             (slice high1 low val)
           (slice high2 low val))))

(defthm slice-of-if2
  (equal (slice low (if test high1 high2) val)
         (if test
             (slice low high1 val)
           (slice low high2 val))))

(defthm bvcat-of-if
  (equal (bvcat (if test highindex1 highindex2) highval lowindex lowval)
         (if test
             (bvcat highindex1 highval lowindex lowval)
           (bvcat highindex2 highval lowindex lowval))))

(defthm bvcat-of-if2
  (equal (bvcat highindex highval (if test lowindex1 lowindex2) lowval)
         (if test
             (bvcat highindex highval lowindex1 lowval)
           (bvcat highindex highval lowindex2 lowval))))

(defthm myif-of-getbit-becomes-bvif-arg1
  (implies (unsigned-byte-p 1 y)
           (equal (myif test (getbit n x) y)
                  (bvif 1 test (getbit n x) y)))
  :hints (("Goal" :in-theory (enable myif bvif))))

(defthm myif-of-getbit-becomes-bvif-arg2
  (implies (unsigned-byte-p 1 y)
           (equal (myif test y (getbit n x))
                  (bvif 1 test y (getbit n x))))
  :hints (("Goal" :in-theory (enable myif bvif))))

(defthmd bvchop-blast
  (implies (and (< 1 size) ;if size=1 go to getbit
                (integerp size))
           (equal (bvchop size x)
                  (bvcat 1
                         (getbit (+ -1 size) x)
                         (+ -1 size)
                         (bvchop (+ -1 size) x)))))

(defthm myif-of-myif-test
  (equal (myif (myif test t nil) a b)
         (myif test a b))
  :hints (("Goal" :in-theory (enable myif))))

;kill some others?
(DEFTHMd BVCAT-EQual-rewrite-constant
  (IMPLIES (AND (syntaxp (and (quotep x)
                              (quotep highsize)
                              (quotep lowsize)))
                (NATP LOWSIZE)
                (NATP HIGHSIZE))
           (EQUAL (EQUAL X
                         (BVCAT HIGHSIZE HIGHVAL LOWSIZE LOWVAL))
                  (AND (UNSIGNED-BYTE-P (+ LOWSIZE HIGHSIZE) X)
                       (EQUAL (BVCHOP LOWSIZE X)
                              (BVCHOP LOWSIZE LOWVAL))
                       (EQUAL (SLICE (+ -1 LOWSIZE HIGHSIZE)
                                     LOWSIZE X)
                              (BVCHOP HIGHSIZE HIGHVAL))))))
;move
(defthmd bvif-blast
  (implies (and (< 1 size)
                (integerp size))
           (equal (bvif size test x y)
                  (bvcat 1 (bvif 1 test (getbit (+ -1 size) x) (getbit (+ -1 size) y))
                         (+ -1 size) (bvif (+ -1 size) test x y))))
  :hints (("Goal" :in-theory (e/d (bvif myif) (MYIF-OF-GETBIT-BECOMES-BVIF-ARG2 MYIF-OF-GETBIT-BECOMES-BVIF-ARG1)))))

(defthm bvor-of-bvshl-and-bvshr-becomes-leftrotate
  (implies (and (equal size (+ amt amt2)) ;could use bvplus but what size?
                (natp amt)
                (natp amt2))
           (equal (bvor size (bvshl size x amt) (bvshr size x amt2))
                  (leftrotate size amt x)))
  :hints (("Goal" :cases ((equal 0 amt2))
           :in-theory (e/d (bvif myif bvplus bvshr leftrotate bvchop-of-sum-cases)
                           (;anti-bvplus
                            )))))

(defthm bvor-of-bvshr-and-bvshl-becomes-leftrotate
  (implies (and (equal size (+ amt amt2)) ;could use bvplus but what size?
                (natp amt)
                (natp amt2))
           (equal (bvor size (bvshr size x amt2) (bvshl size x amt))
                  (leftrotate size amt x)))
  :hints (("Goal" :use (:instance bvor-of-bvshl-and-bvshr-becomes-leftrotate)
          :in-theory (disable bvor-of-bvshl-and-bvshr-becomes-leftrotate))))
;; ;; what about non-powers of 2?
;; ;fixme what if the bvshl has already been turned into a bvcat?
;; ;this one won't match constant sizes
;; (defthm bvor-of-bvshl-and-bvshr-becomes-leftrotate
;;   (implies (and (equal 0 (bvplus size amt amt2))
;;                 (unsigned-byte-p size amt)
;;                 (unsigned-byte-p size amt2))
;;            (equal (bvor (expt 2 size) (bvshl (expt 2 size) x amt) (bvshr (expt 2 size) x amt2))
;;                   (leftrotate (expt 2 size) amt x)))
;;   :hints (("Goal" :in-theory (e/d (bvif myif bvplus bvshr leftrotate bvchop-of-sum-cases)
;;                                   (;anti-bvplus
;;                                    )))))

;special case for 32 (will match)
(defthm bvor-of-bvshl-and-bvshr-becomes-leftrotate32
  (implies (and (equal 0 (bvplus 5 amt amt2))
                (unsigned-byte-p 5 amt)
                (unsigned-byte-p 5 amt2))
           (equal (bvor 32 (bvshl 32 x amt) (bvshr 32 x amt2))
                  (leftrotate32 amt x)))
  :hints (("Goal" :use (:instance bvor-of-bvshl-and-bvshr-becomes-leftrotate (size 32))
           :in-theory (e/d (bvplus bvchop-of-sum-cases leftrotate
                                   LEFTROTATE32 ;why?
                                   )
                           (;anti-bvplus
                            BVSHL-REWRITE-WITH-BVCHOP
                                        bvor-of-bvshl-and-bvshr-becomes-leftrotate
                                        BVSHL-REWRITE-WITH-BVCHOP-FOR-CONSTANT-SHIFT-AMOUNT
                                        BVCAT-EQUAL-REWRITE-ALT
                                        BVCAT-EQUAL-REWRITE)))))

;allows the size of the bvor to be tighter than 32
(defthm bvor-of-bvshl-and-bvshr-becomes-leftrotate32-gen
  (implies (and (equal 0 (bvplus 5 amt amt2))
                (unsigned-byte-p 5 amt)
                (unsigned-byte-p 5 amt2)
                (<= size 32)
                (natp size))
           (equal (bvor size (bvshl 32 x amt) (bvshr 32 x amt2))
                  (bvchop size (leftrotate32 amt x))))
  :hints (("Goal" :use (bvor-of-bvshl-and-bvshr-becomes-leftrotate32
                        (:instance bvchop-of-both-sides (x (bvor 32 (bvshl 32 x amt) (bvshr 32 x amt2)))
                                   (y (leftrotate32 amt x))))
           :in-theory (disable
                       bvcat-of-if slice-of-if bvcat-equal-rewrite bvcat-equal-rewrite-alt bvshl-rewrite-with-bvchop
                       bvor-of-bvshl-and-bvshr-becomes-leftrotate32))))

;an idiom for rotating by 16 bits in a 32-bit field:
;gen!
;should we not just trim the bvshl and bvshr?
(defthm bvor-of-bvshl-and-bvshr
  (implies (and (equal size (+ amt1 amt2)) ;gen?
                (unsigned-byte-p size x)
                (< amt1 size)
                (< amt2 size)
                (natp amt1)
                (natp amt2)
                (natp size)
                (< size 32)
                )
           (equal (bvor size (bvshl 32 x amt1) (bvshr 32 x amt2))
                  (leftrotate size amt1 x)))
  :hints (("Goal" :in-theory (enable bvsx bvshr leftrotate))))

(defthm bvor-of-bvshr-and-bvshl-becomes-leftrotate32
  (implies (and (equal 0 (bvplus 5 amt amt2))
                (unsigned-byte-p 5 amt)
                (unsigned-byte-p 5 amt2)
                (natp amt2)
                )
           (equal (bvor 32 (bvshr 32 x amt2) (bvshl 32 x amt))
                  (leftrotate32 amt x)))
  :hints (("Goal" :use (:instance bvor-of-bvshl-and-bvshr-becomes-leftrotate32)
           :in-theory (disable bvor-of-bvshl-and-bvshr-becomes-leftrotate32))))

;add to more-runes?
(defthmd bvif-of-constant-tighten
  (implies (and (syntaxp (quotep k))
                (syntaxp (quotep size))
                (< (integer-length k) size)
                (unsigned-byte-p (integer-length k) y) ;often y is another constant
                (natp k)
                (natp y)
                (natp size)
                )
           (equal (bvif size test k y)
                  (bvif (integer-length k) test k y)))
  :hints (("Goal" :in-theory (enable myif bvif unsigned-byte-p-of-integer-length-gen))))

(defthm bvplus-disjoint-ones-32-24-8 ;bbozo gen!
  (equal (BVPLUS 32 (BVCAT 24 x 8 0) (BVCHOP 8 y))
         (bvcat 24 x 8 y))
  :hints (("Goal" :in-theory (enable BVPLUS-OPENER))))


;drop?
;better proof?
(defthm bvplus-disjoint-ones-32-24-8-two ;bbozo gen!
  (implies (equal 0 (bvchop 8 x))
           (equal (bvplus 32 x (bvchop 8 y))
                  (bvcat 24 (slice 31 8 x) 8 y)))
  :hints (("Goal" :in-theory (e/d ( ;BVPLUS-BECOMES-RIPPLE-CARRY-ADDER  ;slow! why?
                                   slice
                                   bvplus
                                   bvchop-of-sum-cases
                                   ) (;anti-bvplus
                                      anti-slice)))))

(defthm bvplus-disjoint-ones-32-24-8-two-alt ;bbozo gen!
  (implies (equal 0 (bvchop 8 x))
           (equal (bvplus 32 (bvchop 8 y) x)
                  (bvcat 24 (slice 31 8 x) 8 y)))
  :hints (("Goal" :use (:instance bvplus-disjoint-ones-32-24-8-two)
           :in-theory (disable bvplus-disjoint-ones-32-24-8-two))))

(defthm bvplus-1-of-bvplus-trim-arg1
  (implies (and (< 1 size)
                (integerp size))
           (equal (bvplus 1 (bvplus size x y) z)
                  (bvplus 1 (bvplus 1 x y) z)))
  :hints (("Goal" :use ((:instance bvplus-of-bvchop-arg1 (size 1)
                                   (x (bvplus size x y))
                                   (y z)))
           :in-theory (disable bvplus-of-bvchop-arg1
                               EQUAL-OF-BITXOR-AND-BITXOR-SAME-6
                               EQUAL-OF-BITXOR-AND-BITXOR-SAME-ALT
                               bvchop-1-becomes-getbit))))

(defthm bvplus-1-of-bvplus-trim-arg2
   (implies (and (< 1 size)
                (integerp size))
            (equal (bvplus 1 z (bvplus size x y))
                   (bvplus 1 z (bvplus 1 x y))))
   :hints (("Goal" :use (:instance bvplus-1-of-bvplus-trim-arg1)
            :in-theory (disable bvplus-1-of-bvplus-trim-arg1
                                EQUAL-OF-BITXOR-AND-BITXOR-SAME))))

;bozo make a general theory of this
(defthm bvmult-of-bvplus-trim-arg1
  (implies (and (< size1 size2)
                (natp size1)
                (integerp size2))
           (equal (bvmult size1 (bvplus size2 x z) y)
                  (bvmult size1 (bvplus size1 x z) y)))
  :hints (("Goal" :use (:instance bvmult-of-bvchop-arg2
                                  (x (bvplus size2 x z))
                                  (size size1))
           :in-theory (disable bvmult-of-bvchop-arg3
                               BVMULT-OF-BVCHOP-2-BETTER
                               BVMULT-OF-BVCHOP-1-BETTER
                               bvmult-of-bvchop-arg2
                               ))))

(defthm bvmult-of-bvplus-trim-arg2
   (implies (and (< size1 size2)
                 (natp size1)
                 (integerp size2))
            (equal (bvmult size1 y (bvplus size2 x z))
                   (bvmult size1 y (bvplus size1 x z))))
   :hints (("Goal" :use (:instance bvmult-of-bvplus-trim-arg1)
            :in-theory (disable bvmult-of-bvplus-trim-arg1))))

;of course, this loops
;; (defthm myif-nil-becomes-and
;;   (equal (myif a b nil)
;;          (and a b)))

;i suppose we could use any predicate here in place of booleanp
;shouldn't we turn myif into boolif in this case?
(defthm booleanp-of-myif
  (implies (and (booleanp y)
                (booleanp z))
           (booleanp (myif x y z)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm myif-x-x-t-not-nil
  (implies (not (equal nil val))
           (equal (equal nil (myif x x val))
                  nil))
  :hints (("Goal" :in-theory (enable myif))))

(defthmd bvif-blast-when-quoteps
  (implies (and (syntaxp (quotep x))
                (syntaxp (quotep Y))
                (< 1 size)
                (integerp size))
           (equal (bvif size test x y)
                  (bvcat 1 (bvif 1 test (getbit (+ -1 size) x) (getbit (+ -1 size) y))
                         (+ -1 size) (bvif (+ -1 size) test x y))))
  :hints (("Goal" :in-theory (e/d (bvif myif) (MYIF-OF-GETBIT-BECOMES-BVIF-ARG2 MYIF-OF-GETBIT-BECOMES-BVIF-ARG1)))))

;see PLUS-BVCAT-WITH-0-ALT
(defthm bvplus-of-bvcat-0-hack
  (equal (bvplus 3 (bvcat 1 x 1 y) (bvcat 1 z 2 0))
         (bvcat 1 z 2 (bvcat 1 x 1 y)))
  :hints (("Goal" :in-theory (enable bvplus-opener))))

(defthm bvplus-of-bvcat-0-arg1
  (implies (and (unsigned-byte-p n x)
                (equal (+ n size2) size)
                (natp size2)
                (natp n))
           (equal (bvplus size (bvcat size2 z n 0) x)
                  (bvcat size2 z n x)))
  :hints (("Goal" :in-theory (e/d (bvplus) (;anti-bvplus
                                            )))))

(defthm bvplus-of-bvcat-0-arg2
  (implies (and (unsigned-byte-p n x)
                (equal (+ n size2) size)
                (natp size2)
                (natp n))
           (equal (bvplus size x (bvcat size2 z n 0))
                  (bvcat size2 z n x)))
  :hints (("Goal" :in-theory (e/d (bvplus) (;anti-bvplus
                                            )))))



(defthm <-of-minus-of-expt-and-expt
  (implies (integerp k)
           (equal (< (+ (- (EXPT 2 k)) z)
                     (EXPT 2 k))
                  (< z
                     (EXPT 2 (+ 1 k)))))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm getbit-of-0-and-minus-of-expt
  (implies (posp size)
           (equal (EQUAL (GETBIT 0 (- (EXPT 2 SIZE))) 1)
                  nil))
  :hints (("Goal" :in-theory (e/d (getbit) (SLICE-BECOMES-GETBIT BVCHOP-1-BECOMES-GETBIT)))))

(defthm <-of-+-of-slice-and-slice-and-expt
  (implies (posp size)
           (equal (< (+ (SLICE (+ -1 SIZE) 1 X)
                        (SLICE (+ -1 SIZE) 1 Y))
                     (EXPT 2 SIZE))
                  t))
  :hints (("Goal" :in-theory (enable expt-of-+)
           :use ((:instance SLICE-BOUND (high (+ -1 size)) (low 1) (k (EXPT 2 (+ size -1))))
                 (:instance SLICE-BOUND (x y) (high (+ -1 size)) (low 1) (k (EXPT 2 (+ size -1))))))))

(defthm bvplus-when-low-bits-are-zero
  (implies (and (equal 0 (getbit 0 x))
                (equal 0 (getbit 0 y))
                (posp size)
                (integerp x)  ;new
                (integerp y)  ;new
                )
           (equal (bvplus size x y)
                  (bvcat (+ -1 size)
                         (bvplus (+ -1 size)
                                 (slice (+ -1 size) 1 x)
                                 (slice (+ -1 size) 1 y))
                         1
                         0)))
  :hints (("Goal"
           :expand ((:with UNSIGNED-BYTE-P (UNSIGNED-BYTE-P SIZE
                                                            (+ (- (EXPT 2 SIZE))
                                                               (BVCHOP SIZE X)
                                                               (BVCHOP SIZE Y)))))
           :cases ((equal size 1))
           :in-theory (e/d (bvplus bvchop-of-sum-cases
                                   slice-of-sum-cases
                                   SLICE-WHEN-VAL-IS-NOT-AN-INTEGER
                                   GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER
                                   bitxor
                                   bvxor)
                           (;hack-6 ;yuck!
                            BVXOR-1-BECOMES-BITXOR
                            BITXOR-OF-UNARY-MINUS-ARG1
                            BVPLUS-OF-PLUS2 BVPLUS-OF-PLUS)))))
;bbozo
(defthm bit-0-of-bvminus
  (implies (and (< 0 n)
                (integerp n))
           (equal (getbit 0 (bvminus n x y))
                  (bvminus 1 x y)))
  :hints (("Goal" :in-theory (e/d (bvminus) (BVPLUS-RECOLLAPSE)))))

;replace other
;see BVPLUS-DISJOINT-ONES-32-24-8-TWO
(defthm bvplus-of-bvcat-0-arg1-better
  (implies (and (unsigned-byte-p n x)
                (<= (+ n size2) size)
                (integerp size)
                (< 0 size2)
                (natp size2)
                (natp n))
           (equal (bvplus size (bvcat size2 z n 0) x)
                  (bvcat size2 z n x)))
  :hints (("Goal" :in-theory (e/d (bvplus) (;anti-bvplus
                                            SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE)))))

;replace other
(defthm bvplus-of-bvcat-0-arg2-better
  (implies (and (unsigned-byte-p n x)
                (<= (+ n size2) size)
                (integerp size)
                (< 0 size2)
                (natp size2)
                (natp n))
           (equal (bvplus size x (bvcat size2 z n 0))
                  (bvcat size2 z n x)))
  :hints (("Goal" :in-theory (e/d (bvplus) (;anti-bvplus
                                            SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE)))))

(defthm bvplus-bvminus-same
  (implies (natp size)
           (equal (bvplus size (bvminus size y x) x)
                  (bvchop size y)))
  :hints (("Goal" :in-theory (e/d (bvplus bvminus BVCHOP-WHEN-I-IS-NOT-AN-INTEGER) (;anti-bvplus
                                                                                     )))))

(defthm bvplus-bvminus-same-arg2
  (implies (natp size)
           (equal (bvplus size x (bvminus size y x))
                  (bvchop size y)))
  :hints (("Goal" :in-theory (e/d (bvplus bvminus BVCHOP-WHEN-I-IS-NOT-AN-INTEGER) (;anti-bvplus
                                                                                     )))))

(defthmd leftrotate32-open-when-constant-shift-amount
  (implies (syntaxp (quotep amt))
           (equal (leftrotate32 amt val)
                  (let* ((amt (mod (nfix amt) 32) ;(bvchop 5 amt)
                              ))
                    (bvcat (- 32 amt)
                           (slice (- 31 amt) 0 val)
                           amt (slice 31 (+ 32 (- amt)) val)))))
  :hints (("Goal" :expand (leftrotate32 amt val)
           :in-theory (enable leftrotate))))
;more like this
(defthmd slice-of-bvplus-low
  (implies (and (< high (+ -1 size)) ;bozo more cases
                (< 0 high)
                (<= low high)
                (natp size)
                (natp low)
                (natp high))
           (equal (slice high low (bvplus size x y))
                  (slice high low (bvplus (+ 1 high) x y))))
  :hints (("Goal" :in-theory (e/d (bvplus BVCHOP-WHEN-I-IS-NOT-AN-INTEGER) (;anti-bvplus
                                                                             )))))

(defthmd slice-blast
  (implies (and (< 1 high)
                (integerp high)
                (natp low)
                (<= low high)
                )
           (equal (slice high low x)
                  (bvcat 1
                         (getbit high x)
                         (+ high (- low))
                         (slice (+ -1 high) low x))))
  :hints (("Goal" :in-theory (enable natp))))

;bozo trim-all rule for getbit?
(defthmd getbit-of-bvplus
  (implies (and (< n (+ -1 size))
                (< 0 n)
                (integerp n)
                (natp size))
           (equal (getbit n (bvplus size x y))
                  (getbit n (bvplus (+ 1 n) x y))))
  :hints
  (("Goal"
    :in-theory (e/d (bvplus bvchop-when-i-is-not-an-integer)
                    (;anti-bvplus
                     )))))
;dups?
(defthm bvif-of-bvcat-low-arg2
  (implies (and (<= size lowsize)
                (natp size)
                (natp lowsize))
           (equal (bvif size test x (bvcat highsize highval lowsize lowval))
                  (bvif size test x lowval)))
  )

(defthm bvif-of-bvcat-low-arg1
  (implies (and (<= size lowsize)
                (natp size)
                (natp lowsize))
           (equal (bvif size test (bvcat highsize highval lowsize lowval) x)
                  (bvif size test lowval x)))
  )

;gen the 1 to any constant
;try without this?  may need a rule for usbp of bvcat in this case?
(defthm bvcat-trim-high-size-when-constant-1
  (implies (and (< 1 size)
                (integerp size)
                (natp size2)
                )
           (equal (bvcat size 1 size2 x)
                  (bvcat 1 1 size2 x))))

;bozo gen
(defthm bvcat-of-bitxor-trim-high-size
  (implies (and (< 1 size)
                (integerp size)
                (natp size2)
                )
           (equal (bvcat size (bitxor x y) size2 z)
                  (bvcat 1 (bitxor x y) size2 z))))

;There is already a natp-when-integerp in std/basic/arith-equivs.lisp.
(defthm natp-when-integerp-cheap
  (implies (integerp x)
           (equal (natp x)
                  (<= 0 x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;phrase in terms of bitnot?
(defthm bitxor-bitand-bvnot-hack
  (implies (and (unsigned-byte-p 1 x)
                (unsigned-byte-p 1 y))
           (equal (bitxor (bitand x y) (bvnot '1 x))
                  (bitor (bitand x y) (bvnot '1 x))))
  :hints (("Goal" :cases ((and (equal 0 x) (equal 0 y))
                          (and (equal 0 x) (equal 1 y))
                          (and (equal 1 x) (equal 0 y))
                          (and (equal 1 x) (equal 1 y))))))

;move
(defthm getbit-0-of-bvplus
  (implies (and (< 0 n)
                (natp n))
           (equal (getbit 0 (bvplus n x y))
                  (bitxor (getbit 0 x)
                          (getbit 0 y))))
  :hints (("Goal" :in-theory (e/d (GETBIT-OF-BVPLUS getbit) (SLICE-BECOMES-GETBIT BVCHOP-1-BECOMES-GETBIT)))))

;trying without these 2 Thu Mar 31 17:48:32 2011
;; ;for sha1? too gross of a hack?
;; (defthm bitxor-bitand-bitnot-hack
;;   (implies (and (unsigned-byte-p 1 x)
;;                 (unsigned-byte-p 1 y))
;;            (equal (bitxor (bitand x y) (bitxor 1 x))
;;                   (bitor (bitand x y) (bitxor 1 x))))
;;   :hints (("Goal"
;;            :in-theory (disable BVNOT-1-BECOMES-BITXOR-1)
;;            :cases ((and (equal 0 x) (equal 0 y))
;;                           (and (equal 0 x) (equal 1 y))
;;                           (and (equal 1 x) (equal 0 y))
;;                           (and (equal 1 x) (equal 1 y))))))

;; ;for sha1? too gross of a hack?
;; (defthm bitxor-bitand-bitnot-hack-alt
;;   (implies (and (unsigned-byte-p 1 x)
;;                 (unsigned-byte-p 1 y))
;;            (equal (bitxor (bitxor 1 x) (bitand x y))
;;                   (bitor (bitxor 1 x) (bitand x y))))
;;   :hints (("Goal" :cases ((and (equal 0 x) (equal 0 y))
;;                           (and (equal 0 x) (equal 1 y))
;;                           (and (equal 1 x) (equal 0 y))
;;                           (and (equal 1 x) (equal 1 y))))))

;work on this:
(defthm bvchop-of-bvsx
  (implies (and (<= n new-size)
;                (<= old-size new-size)
                (<= old-size n)
                (< 0 old-size)

                (natp n)
                (natp new-size)
                (natp old-size))
           (equal (bvchop n (bvsx new-size old-size val))
                  (bvsx n old-size val)))
  :hints (("Goal" :in-theory (enable bvsx))))

(defthm unsigned-byte-p-bound
  (implies (and (< small big)
                (natp small)
                (integerp big)
                )
           (unsigned-byte-p (integer-length big)
                            small))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-integer-length (x small))
           :in-theory (disable unsigned-byte-p-of-integer-length))))


;would be better to let it use the regular rule and execute fix
(defthm my-right-cancellation-for-+
  (implies (and (natp x) (natp y))
           (equal (equal (+ x z) (+ y z))
                  (equal x y))))

(defthm myif-equal-lemma
  (implies (not (equal x b))
           (equal (equal x (myif test a b))
                  (myif test (equal x a) nil)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm myif-myif-lift-same
  (equal (myif test1 (myif test2 x y) y)
         (myif (myif test1 test2 nil) x y))
  :hints (("Goal" :in-theory (enable myif))))


;; (defthm myif-same-test2
;;   (equal (myif test z (myif test x y))
;;          (myif test z y))
;;   :hints (("Goal" :in-theory (enable myif))))


(defthm myif-lemma
  (equal (equal x (myif test y x))
         (myif test (equal x y) t))
  :hints (("Goal" :in-theory (enable myif))))

(defthm <-of-myif-arg2
  (equal (< k (myif test a b))
         (myif test (< k a) (< k b)))
  :hints (("Goal" :in-theory (enable myif))))

;; ;just rewrite (boolif x 'nil 't)
;; (defthm myif-boolif
;;   (equal (myif (boolif x 'nil 't) y z)
;;          (myif x z y))
;;   :hints (("Goal" :in-theory (enable myif boolif))))

;gen to non-nil?
(defthmd myif-becomes-boolif-t-arg1
  (implies (booleanp c)
           (equal (myif a t c)
                  (boolor a c)))
  :hints (("Goal" :in-theory (enable boolor))))

;simplify rhs?
(defthmd myif-becomes-boolif-t-arg2
  (implies (booleanp c)
           (equal (myif a c t)
                  (boolif a c t)))
  :hints (("Goal" :in-theory (enable myif))))

;simplify rhs?
(defthmd myif-becomes-boolif-nil-arg1
  (implies (booleanp c)
           (equal (myif a nil c)
                  (boolif a nil c))))

(defthmd myif-becomes-boolif-nil-arg2
  (implies (booleanp c)
           (equal (myif a c nil)
                  (booland a c)))
  :hints (("Goal" :in-theory (enable booland))))

(defthm myif-equal-nil-rewrite
  (equal (equal (myif test a b) nil) ;reverse the equality?
         (myif test (equal a nil)
               (equal b nil)))
  :hints (("Goal" :in-theory (enable myif))))

;gen the 1
(defthm <-of-bvcat-and-constant-low
  (implies (and (natp k)
                (natp lowsize)
                (< 0 lowsize)
                (< k (expt 2 lowsize)) ;bozo
                )
           (equal (< (bvcat 1 x lowsize y) k)
                  (and (equal (getbit 0 x) 0)
                       (< (bvchop lowsize y) k))))
  :hints (("Goal" :in-theory (e/d (BVCAT LOGAPP bvchop
                                         ) ()))))


(defthmd getbit-numeric-bound
  (implies (and (syntaxp (quotep k))
                (<= 2 k)
                (integerp k))
           (< (getbit n x) k))
  :hints (("Goal" :use (:instance BOUND-WHEN-USB2 (n 1) (x (GETBIT N X)))
           :in-theory (disable BOUND-WHEN-USB2))))



;can use this to prove the mask thms?
(defthmd logand-bvchop-when-usb
  (implies (and (unsigned-byte-p xsize x)
                (natp xsize)
;               (integerp x)
                (natp y) ;gen?
                )
           (equal (logand x (bvchop xsize y))
                  (logand x y)))
  :hints (("Goal"
           :use ((:instance BVCHOP-OF-LOGAND (size xsize) (i x) (j (bvchop xsize y)))
                 (:instance BVCHOP-OF-LOGAND (size xsize) (i x) (j y)))
           :in-theory (disable BVCHOP-OF-LOGAND))))

;move
(defthmd bvmult-of-2-gen
  (implies (and (< 0 size)
                (integerp size)
                )
           (equal (bvmult size 2 x)
                  (bvcat (+ -1 size)
                         (bvchop (+ -1 size) x)
                         1
                         0)))
  :hints (("Goal" :in-theory (e/d (bvmult bvcat GETBIT)
                                  (bvchop-of-*
                                   BVCHOP-1-BECOMES-GETBIT SLICE-BECOMES-GETBIT)))))

;(EQUAL y (BITOR X y))

(defthm bitor-bitand-x-y-bitxor-1-y
  (equal (bitor (bitand x y) (bitxor '1 y))
         (bitor x (bitxor '1 y)))
  :hints (("Goal"
           :cases ((and (equal 0 (GETBIT 0 X)) (equal 0 (GETBIT 0 y)))
                   (and (equal 0 (GETBIT 0 X)) (equal 1 (GETBIT 0 y)))
                   (and (equal 1 (GETBIT 0 X)) (equal 0 (GETBIT 0 y)))
                   (and (equal 1 (GETBIT 0 X)) (equal 1 (GETBIT 0 y))))
           :in-theory (e/d (bvand bitand bitxor bvxor BITNOT) (BVXOR-1-BECOMES-BITXOR LOGXOR-BVCHOP-BVCHOP BITNOT-BECOMES-BVNOT)))))

;more like this?  add to amazing rules?
(defthm bvif-1-equal-0-becomes-bitor
  (implies (unsigned-byte-p 1 x)
           (equal (bvif 1 (equal 0 x) y 1)
                  (bitor x y)))
  :hints (("Goal" :in-theory (enable bvif))))



;move
(defthmd leftrotate-open-when-constant-shift-amount
  (implies (syntaxp (and (quotep amt)
                         (quotep width)))
           (equal (leftrotate width amt val)
                  (if (equal width 0)
                      0
                    (let* ((amt (mod (nfix amt) width) ;(bvchop (integer-length (+ -1 width)) amt)
                                ))
                      (bvcat (- width amt)
                             (slice (+ -1 width (- amt)) 0 val)
                             amt
                             (slice (+ -1 width)
                                    (+ width (- amt))
                                    val))))))
  :hints (("Goal" :in-theory (e/d (leftrotate)
;for speed:
                                  (;INTP-BECOMES-SBP32 JVM::INT-LEMMA0
                                   )))))





;slice trim rule?



(defthm bvor-of-bvshr-and-bvshl-becomes-leftrotate32-gen
  (implies (and (equal 0 (bvplus 5 amt amt2))
                (unsigned-byte-p 5 amt)
                (unsigned-byte-p 5 amt2)
                (<= size 32)
                (natp size)
                (natp amt2))
           (equal (bvor size (bvshr 32 x amt2) (bvshl 32 x amt))
                  (bvchop size (leftrotate32 amt x))))
  :hints (("Goal" :use (:instance bvor-of-bvshl-and-bvshr-becomes-leftrotate32-gen)
           :In-theory (disable bvor-of-bvshl-and-bvshr-becomes-leftrotate32-gen))))

;Wed Aug 18 05:40:07 2010
;; (defthm leftrotate32-of-logext-32-one
;;   (equal (leftrotate32 (logext 32 amt) x)
;;          (leftrotate32 amt x))
;;   :hints (("Goal" :in-theory (enable leftrotate32 leftrotate))))

(in-theory (disable BITNOT-BECOMES-BITXOR-WITH-1))

;is this true?  if not, redefine bvnot
;; (DEFTHM GETBIT-OF-BVNOT-better
;;   (IMPLIES (AND (< N M)
;;                 (NATP N)
;;                 (NATP M)
;; ;                (INTEGERP X)
;;                 )
;;            (EQUAL (GETBIT N (BVNOT M X))
;;                   (BVNOT 1 (GETBIT N X))))
;;   :HINTS (("Goal" :IN-THEORY (E/D (BVNOT LOGNOT getbit)
;;                                   (SLICE-BECOMES-GETBIT)))))

;bozo could go back and use something like this in the jvm model?
(defthmd <-of-logext-when-signed-byte-p
  (implies (and (signed-byte-p 32 y))
           (equal (< (logext 32 x) y)
                  (sbvlt 32 x y)))
  :hints (("Goal" :in-theory (e/d (sbvlt) (SBVLT-REWRITE)))))

(theory-invariant (incompatible (:definition sbvlt) (:rewrite <-of-logext-when-signed-byte-p)))

(defthmd <-of-logext-when-signed-byte-p-alt
  (implies (and (signed-byte-p 32 y))
           (equal (< y (logext 32 x))
                  (sbvlt 32 y x)))
  :hints (("Goal" :in-theory (e/d (sbvlt) (SBVLT-REWRITE)))))

(theory-invariant (incompatible (:definition sbvlt) (:rewrite <-of-logext-when-signed-byte-p-alt)))

(defthm bvcat-mask-lemma
  (implies (integerp x)
           (equal (BVAND '16 '65280 x)
                  (bvcat 8 (slice 15 8 x)
                         8 0))))


(defthm sum-bound
  (IMPLIES (AND (UNSIGNED-BYTE-P XSIZE X)
                (UNSIGNED-BYTE-P YSIZE Y)
                (NATP XSIZE)
                (NATP YSIZE)
                (<= XSIZE YSIZE))
           (< (+ X Y) (EXPT 2 (+ 1 YSIZE))))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p) (EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1 <-OF-EXPT-AND-EXPT))
           :use (:instance EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1 (r 2) (i (min xsize ysize)) (j (max xsize ysize))))))

(defthm sum-bound2
   (IMPLIES (AND (UNSIGNED-BYTE-P XSIZE X)
                 (UNSIGNED-BYTE-P YSIZE Y)
                 (NATP XSIZE)
                 (NATP YSIZE)
                 (<= XSIZE YSIZE))
            (< (+ X Y) (* 2 (EXPT 2 YSIZE))))
   :hints (("Goal" :in-theory (e/d (unsigned-byte-p) (EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1 <-OF-EXPT-AND-EXPT))
            :use (:instance EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1 (r 2) (i (min xsize ysize)) (j (max xsize ysize))))))

(defthm sum-bound-lemma
  (implies (and (unsigned-byte-p xsize x)
                (unsigned-byte-p ysize y)
                (natp xsize)
                (natp ysize))
           (< (+ x y) (expt 2 (+ 1 (max xsize ysize))))))

(defthm bvcat-hack
  (implies (unsigned-byte-p 8 x)
           (equal (BVPLUS '17 (BVCAT '8 y '8 '0) x)
                  (bvcat 8 y 8 x))))

(defthm bvcat-hack2
  (implies (unsigned-byte-p 8 x)
           (equal (BVPLUS '16 (BVCAT '8 y '8 '0) x)
                  (bvcat 8 y 8 x))))


(defthm bvcat-mask-lemma-14
  (implies (integerp x)
           (equal (BVAND '14 '16128 x)
                  (bvcat 8 (slice 13 8 x)
                         8 0))))

;bozo how does the max get introduced? maybe from LEN-OF-UPDATE-SUBRANGE?
(defthmd max-constants-lemma
  (implies (and (syntaxp (quotep k1))
                (syntaxp (quotep k2))
                (< k1 k2)
                )
           (< k1 (max x k2))))



;; (defthm getbit-of-bif
;;   (implies (and (natp n))
;;            (equal (getbit n (bif test thenpart elsepart))
;;                   (bif test (getbit n thenpart) (getbit n elsepart))))
;;   :hints (("Goal" :in-theory (enable bvif myif))))


(defthm bvif-1-equal-1
  (implies (unsigned-byte-p 1 x)
           (equal (bvif 1 (equal 1 x) tp ep)
                  (bif x (getbit 0 tp) (getbit 0 ep))))
  :hints (("Goal" :in-theory (disable BITXOR-OF-1-BECOMES-BITNOT-ARG1)
           :DO-NOT '(preprocess))))

;rename bif to bitif?
(defthm bif-rewrite
  (implies (unsigned-byte-p 1 test)
           (equal (bif test x y)
                  (bitor (bitand test x)
                         (bitand (bitnot test) y))))
  :hints (("Goal" :in-theory (disable BITXOR-OF-1-BECOMES-BITNOT-ARG1)
           :DO-NOT '(preprocess))))

(in-theory (disable bvuminus))

(defthm bvif-becomes-bif
  (equal (bvif 1 test x y)
         (bif (bool-to-bit test) x y))
  :hints (("Goal" :in-theory (e/d (bvif myif bool-to-bit) ( bitnot-becomes-bitxor-with-1)))))

;actually, we should go to bvif?!
(defthmd bvplus-of-myif
  (equal (bvplus size x (myif test a b))
         (myif test
               (bvplus size x a)
               (bvplus size x b)))
  :hints (("Goal" :in-theory (enable myif))))

;expensive?
(defthm integerp-implies-acl2-numberp
  (implies (integerp x)
           (acl2-numberp x)))

(defthm acl2-numberp-of-sum
  (acl2-numberp (+ x y)))

(defthm <-from-<=-free
  (implies (and (equal (< free x) ; i think we have this rather than (not (< free x))
                       nil)
                (< free y))
           (< x y)))




(defthm cancel-from-logext-equality-helper
  (implies (and (integerp x)
                (integerp k))
           (implies (equal (logext 32 (binary-+ k x)) x)
                    (equal 0 (bvchop 32 k))))
  :rule-classes nil
  :hints (("Goal"
           :cases ((SIGNED-BYTE-P 32 x))
           :in-theory (e/d ( ;logext BVCHOP-OF-SUM-CASES getbit slice
                            ADD-BVCHOPS-TO-EQUALITY-OF-SBPS-4
                            )
                           (BVCHOP-1-BECOMES-GETBIT
                            SLICE-BECOMES-GETBIT
                            LOGEXT-OF-PLUS
                            anti-slice
                            ;anti-bvplus
                            )))))

(defthm cancel-from-logext-equality-helper2
  (implies (and (integerp x)
                (integerp k)
                (signed-byte-p 32 x))
           (implies (equal 0 (bvchop 32 k))
                    (equal (logext 32 (binary-+ k x)) x)))
  :rule-classes nil

  :hints (("Goal"
           :use (:instance logext-of-+-of-bvchop)
           :in-theory (disable
                       ;;LOGEXT-EQUAL-LOGEXT-REWRITE
                       logext-of-+-of-bvchop
                       BVCHOP-1-BECOMES-GETBIT
                       SLICE-BECOMES-GETBIT
                       anti-slice
                       ;;anti-bvplus
                       ))))

(defthm cancel-from-logext-equality
  (implies (and (integerp x)
                (integerp k))
           (equal (equal (logext 32 (binary-+ k x)) x)
                  (and (signed-byte-p 32 x) ;new..
                       (equal 0 (bvchop 32 k)))))
  :hints (("Goal" :use (cancel-from-logext-equality-helper
                                  cancel-from-logext-equality-helper2))))

;stuff from rc6 rolled-up proof:
;FIXME gen this stuff

(defthm bvcat-hack-gross
  (implies (and (<= x 20)
                (natp x))
           (equal (bvcat '31 x '1 '0)
                  (bvcat 5 x 1 0)))
  :hints (("Goal" :in-theory (enable slice-too-high-is-0
;                                     bag::unsigned-byte-p-from-bounds
                                     ))))

(defthm bvcat-hack-gross2
  (implies (and (<= x 20)
                (natp x))
           (equal (bvcat '31 x '1 '1)
                  (bvcat 5 x 1 1)))
  :hints (("Goal" :in-theory (enable slice-too-high-is-0
                                     ;bag::unsigned-byte-p-from-bounds
                                     ))))

(defthm bvcat-bound-hack ;fixme gen!
  (implies (and (<= x 20)
                (natp x))
           (not (< 43 (BVCAT '5 x '1 y))))
  :hints (("Goal" :in-theory (e/d (bvcat LOGAPP bvchop-identity ;BAG::UNSIGNED-BYTE-P-FROM-BOUNDS
                                         )
                                  ()))))


;might be slow
;would be nice if the dag-rewriter had backchain limits..
(defthm bound-from-natp-fact
  (implies (and (< k 0)
                (natp x))
           (not (< x k))))

;;patterns   (EQUAL (BITXOR 1 X) 1) (EQUAL (LOGTAIL 1 (+ 1 X)) X)

;put this back (may need to repair it?)
;; ;instead we should probably turn the (* 2 x) into a bvmult
;; (defthm *-of-2-becomes-bvmult
;;   (implies (and (< x free)
;;                 (syntaxp (quotep free))
;;                 (integerp free)
;;                 (natp x))
;;            (equal (* 2 x)
;;                   (bvmult (ceiling-of-lg free) 2 x)))
;;   :hints (("Goal" :in-theory (e/d (bvmult)(bvchop-of-* BVMULT-OF-2-GEN)))))

;put this back (may need to repair it?)
;; (defthm *-of-2-becomes-bvmult->=
;;   (implies (and (equal (< free x) nil) ;;should it be (not blah) or (equal blah nil) ?
;;                 (syntaxp (quotep free))
;;                 (integerp free)
;;                 (natp x))
;;            (equal (* 2 x)
;;                   ;is this as tight as we can make the mult?
;;                   (bvmult (ceiling-of-lg (+ 1 free)) 2 x)))
;;   :hints (("Goal" :in-theory (e/d (bvmult)(bvchop-of-* BVMULT-OF-2-GEN)))))

;; ;yuck
;; (defthm bvcat-hack22
;;   (implies (and (< x 32)
;;                 (natp x))
;;            (equal (bvcat '5 x '1 '1)
;;                   (+ 1 (* 2 x))))
;;   :hints (("Goal" :in-theory (e/d (bvcat logtail bvplus getbit)
;;                                   (anti-bvplus
;;                                    bvchop-1-becomes-getbit
;;                                    slice-becomes-getbit
;;                                    bvplus-1-becomes-bitxor)))))

;; (defthm bvcat-hack22b
;;   (implies (and (< x 32)
;;                 (natp x))
;;            (equal (bvcat '5 x '1 '0)
;;                   (* 2 x)))
;;   :hints (("Goal" :in-theory (e/d (bvcat logtail bvplus getbit)
;;                                   (anti-bvplus
;;                                    bvchop-1-becomes-getbit
;;                                    slice-becomes-getbit
;;                                    bvplus-1-becomes-bitxor)))))


(defthm bvcat-of-*-high
  (implies (and (integerp x)
                (integerp y)
                (natp highsize)
                (natp lowsize)
                )
           (equal (bvcat highsize (* x y) lowsize lowval)
                  (bvcat highsize (bvmult highsize x y) lowsize lowval)))
  :hints (("Goal" :in-theory (e/d (bvmult) (bvchop-of-*)))))

(defthm bvcat-of-*-low
  (implies (and (integerp x)
                (integerp y)
                (natp highsize)
                (natp lowsize)
                )
           (equal (bvcat highsize highval lowsize (* x y))
                  (bvcat highsize highval lowsize (bvmult lowsize x y))))
  :hints (("Goal" :in-theory (e/d (bvmult) (bvchop-of-*)))))

(defthmd logext-of-+
  (implies (and (integerp x)
                (integerp y)
                (posp size))
           (equal (logext size (+ x y))
                  (logext size (bvplus size x y))))
  :hints (("Goal" :in-theory (e/d (bvplus) (;anti-bvplus
                                            )))))

;do this better with congruences?
(defthmd bvcat-of-+-high
  (implies (and (integerp x)
                (integerp y)
                (natp highsize)
                (natp lowsize)
                )
           (equal (bvcat highsize (+ x y) lowsize lowval)
                  (bvcat highsize (bvplus highsize x y) lowsize lowval)))
  :hints (("Goal" :in-theory (e/d (bvplus) (;anti-bvplus
                                            )))))

(defthmd bvcat-of-+-low
  (implies (and (integerp x)
                (integerp y)
                (natp highsize)
                (natp lowsize)
                )
           (equal (bvcat highsize highval lowsize (+ x y))
                  (bvcat highsize highval lowsize (bvplus lowsize x y))))
  :hints (("Goal" :in-theory (e/d (bvplus) (;anti-bvplus
                                            )))))

(defthm bvplus-of-*-arg2
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (natp size)
                )
           (equal (bvplus size x (* y z))
                  (bvplus size x (bvmult size y z))))
  :hints (("Goal" :in-theory (e/d (bvmult) (bvplus-recollapse bvchop-of-*)))))

;add in:
;; (defthm bvplus-of-*-arg1
;;   (implies (and (integerp x)
;;                 (integerp y)
;;                 (integerp z)
;;                 (natp size)
;;                 )
;;            (equal (bvplus size (* y z) x)
;;                   (bvplus size (bvmult size y z) x)))
;;   :hints (("Goal" :in-theory (e/d (bvmult) (bvplus-recollapse)))))

;fixme gen
(defthm bvplus-of-bvcat-of-0-hack
  (implies (integerp highval)
           (equal (bvplus '31 '2147483647 (bvcat '30 highval '1 '0))
                  (bvcat '30 (bvplus '31 (slice 30 1 '2147483647) highval) '1 (getbit 1 '2147483647))))
  :hints (("Goal"
           :cases ((equal 0 (getbit 30 highval))
                   (equal 1 (getbit 30 highval)))
           :in-theory (e/d (bvcat logapp bvplus bvchop
                                  bvchop-of-sum-cases
                                  mod-sum-cases)
                           ( ;anti-bvplus
                            expt
                            )))))

;newly disabled
(defthmd +-becomes-bvplus-hack
  (implies (unsigned-byte-p 30 x)
           (equal (binary-+ 1 x)
                  (bvplus 31 1 x)))
  :hints (("Goal" :in-theory (e/d (bvplus) (;anti-bvplus
                                            BVPLUS-OPENER)))))

(defthm unsigned-byte-p-from-bound-<=-version
  (implies (and (equal (< free x) nil)
                (<= (+ 1 free) (expt 2 n))
                (integerp x)
                (<= 0 x)
                (integerp n)
                (<= 0 n))
           (unsigned-byte-p n x))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))



(in-theory (disable BVPLUS-OPENER))

(defthm bvplus-tighten-hack
  (implies (and (< x 16)
                (natp x))
           (equal (bvplus '31 '1 x)
                  (bvplus 5 1 x)))
  :hints (("Goal" :in-theory (e/d (bvplus) (;anti-bvplus
                                            |+-BECOMES-BVPLUS-HACK|)))))



;bozo gen the inner term
(defthm times-2-of-bvplus-becomes-bvmult-of-bvplus
  (implies (natp size)
           (equal (* 2 (bvplus size x y))
                  (bvmult (+ 1 size) 2 (bvplus size x y))))
  :hints (("Goal" :in-theory (e/d (bvmult) (bvchop-of-*)))))

(defthm ifix-does-nothing
  (implies (integerp x)
           (equal (ifix x)
                  x)))

;should be cheap since n is a free var
(defthm integerp-when-signed-byte-p
  (implies (equal (signed-byte-p n x) ;the "equal xxx t" formulation is used in dag hyps
                  t)
           (integerp x)))

;move
(defthmd equal-constant-+-alt
  (implies (syntaxp (and (quotep c1)
                         (quotep c2)))
           (equal (equal c2 (+ c1 x)) ;order here is better
                  (if (acl2-numberp c2)
                      (if (acl2-numberp x)
                          (equal x (- c2 c1))
                        (equal (fix c1) c2))
                    nil))))

(defthm <-of-expt-and*-*-of-2-and-expt
  (IMPLIES (AND (INTEGERP N)
                (< 0 N)
                (NATP M)
                (<= N M))
           (<= (EXPT 2 N) (* 2 (EXPT 2 M))))
  :hints (("Goal" :use (:instance <-OF-EXPT-AND-EXPT (r 2)
                                  (i (+ 1 m))
                                  (j n)))))



(defthm logext-of-bvsx
  (implies (and (<= n m)
                (posp n)
                (natp m))
           (equal (logext m (bvsx m n x))
                  (logext n x)))
  :hints (("Goal" :in-theory (enable bvsx-rewrite))))

(defthm bvcat-equal-expt-2-rewrite
  (implies (natp n)
           (equal (EQUAL (BVCAT 1 1 n X) (EXPT 2 n))
                  (equal 0 (bvchop n x)))))

(defthm logext-of-one-less
  (implies (and (integerp x)
;                (equal n 32)
                (posp n)
;                (< 1 n) ;bozo
                )
           (equal (logext n (+ -1 x))
                  (if (equal (bvchop n x) (expt 2 (+ -1 n)))
                      (+ -1 (expt 2 (+ -1 n)))
                    (+ -1 (logext n x)))))
  :hints (("Goal"
           :use (:instance BVCAT-OF-GETBIT-AND-X-ADJACENT (n (+ -1 n)))
           :in-theory (e/d (logext logapp bvchop-of-sum-cases slice ;getbit
                                   REPEATBIT
                                   posp
                                   ) (BVCAT-OF-GETBIT-AND-X-ADJACENT bvplus-recollapse anti-slice +-becomes-bvplus-hack
                                   BVCAT-EQUAL-REWRITE-ALT
                                   BVCAT-EQUAL-REWRITE
                                   BVCAT-OF-GETBIT-AND-X-ADJACENT
                                   )))))
;gen the 1
(defthm bvplus-1-equal-constant
  (implies (and (syntaxp (quotep k))
                ;(integerp x)
                )
           (equal (equal k (bvplus 32 1 x))
                  (and (unsigned-byte-p 32 k)
                       (equal (bvplus 32 -1 k)
                              (bvchop 32 x)))))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases BVCHOP-WHEN-I-IS-NOT-AN-INTEGER) (;anti-bvplus
                                                                                                  )))))

(defthm plus-1-bvplus-1
  (implies t;(integerp x)
           (equal (EQUAL (+ 1 (BVCHOP 32 x)) (BVPLUS 32 1 x))
                  (not (equal (BVCHOP 32 x)
                              (+ -1 (expt 2 32))))))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases BVCHOP-WHEN-I-IS-NOT-AN-INTEGER) (;anti-bvplus
                                                                                                  )))))

(defthm logtail-of-one-more
  (implies (and (integerp x)
;                (equal n 32)
                (posp n))
           (equal (logtail n (+ 1 x))
                  (if (equal (+ -1 (expt 2 n)) (bvchop n x))
                      (+ 1 (logtail n x))
                    (logtail n x))))
  :hints (("Goal"
           :use (:instance FLOOR-PEEL-OFF-CONSTANT (k (+ -1 (expt 2 n))) (n x) (y (expt 2 n)))
           :in-theory (e/d (logtail bvchop FLOOR-OF-SUM)
                           (MOD-OF-EXPT-OF-2
                            mod-of-expt-of-2-constant-version
                            FLOOR-PEEL-OFF-CONSTANT)))))



(defthm getbit-of-one-more
  (implies (integerp x)
           (equal (getbit 31 (+ 1 x))
                  (if (equal (bvchop 31 x) (+ -1 (expt 2 31)))
                      (bitnot (getbit 31 x))
                    (getbit 31 x))))
  :hints (("Goal" :in-theory (e/d (getbit slice bvchop-of-sum-cases
                                        bvchop-32-split-hack
                                        ) (anti-slice bvplus-recollapse +-becomes-bvplus-hack BVCAT-OF-GETBIT-AND-X-ADJACENT
                                                      BVCHOP-1-OF-PLUS
                                        BVCAT-OF-GETBIT-AND-X-ADJACENT)))))


(defthm logext-of-one-more
  (implies (integerp x)
           (equal (logext 32 (+ 1 x))
                  (if (equal (bvchop 32 x) 2147483647)
                      -2147483648
                    (+ 1 (logext 32 x)))))
  :hints (("Goal" :in-theory (e/d (logext bvchop-32-split-hack
                                          ) (anti-slice BVCAT-OF-GETBIT-AND-X-ADJACENT
                                          BVCAT-OF-GETBIT-AND-X-ADJACENT)))))

(defthm sbvlt-of-one-more
  (implies (integerp x)
           (equal (sbvlt 32 (+ 1 x) 0)
                  (if (equal (bvchop 32 x) 2147483647)
                      t
                    (sbvlt 32 x -1))))
  :hints (("Goal" :in-theory (e/d (sbvlt ;logext getbit slice
                                   ) (anti-slice sbvlt-rewrite)))))

;version for <=?
(defthmd equal-when-bound-dag
  (implies (and (syntaxp (quotep y))
                ;(equal (< free x) t) ;awkward
                (< free x)
                (syntaxp (quotep free))
                (<= y free))
           (equal (equal y x)
                  nil)))



;more like this? sort of need a bool-trim rule?
(defthm booland-of-myif-arg1
  (equal (booland (myif test a b) c)
         (booland (boolif test a b) c))
  :hints (("Goal" :in-theory (enable booland boolif))))

(defthm plus-of-bvplus-of-minus1
  (equal (binary-+ '1 (bvplus '32 4294967295 x))
         (if (equal (bvchop 32 x) 0)
             (expt 2 32)
           (bvchop 32 x)))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases bvchop-when-i-is-not-an-integer)
                                  (;anti-bvplus ;bvlt-of-plus-arg1 bvlt-of-plus-arg2 plus-becomes-bvplus
                                   )))))


(defthmd <-of-0-and-logext
  (implies (natp size)
           (equal  (< 0 (logext size x))
                   (sbvlt size 0 x)))
  :hints (("Goal" :in-theory (e/d (sbvlt) (;sbvlt-rewrite
                                           )))))

;rename
(defthm myif-lemma-arg2
  (equal (equal (myif test y x) x)
         (myif test (equal x y) t))
  :hints (("Goal" :in-theory (enable myif))))

(defthm boolif-of-myif-arg1
  (equal (boolif test (myif test2 a b) c)
         (boolif test (boolif test2 a b) c))
  :hints (("Goal" :in-theory (enable boolif))))

(defthm boolif-of-myif-arg2
  (equal (boolif test c (myif test2 a b))
         (boolif test c (boolif test2 a b)))
  :hints (("Goal" :in-theory (enable boolif))))

;gen the 0?
;gen
(defthm sbvlt-of-0-when-shorter2
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'xsize x))
                (< xsize 32)
                (natp xsize)
                (force (unsigned-byte-p-forced xsize x))
                )
           (equal (sbvlt 32 x 0)
                  nil))
  :hints (("Goal" :in-theory (enable sbvlt UNSIGNED-BYTE-P-FORCED))))



(defthm bvplus-of-bvmult-tighten-6-5-4
  (implies (and (integerp x)
                (< y 4)
                (natp y))
           (equal (BVPLUS 6 y (BVMULT 5 4 x))
                  (BVPLUS 5 y (BVMULT 5 4 x))))
  :hints (("Goal" :in-theory (e/d (bvmult bvplus) (;anti-bvplus
                                                   bvchop-of-*
;                                                   BVLT-OF-PLUS-ARG1
;                                                  BVLT-OF-PLUS-ARG2
;                                                 SLICE-OF-+ ; fixme looped with meta rule?
;                                                PLUS-BECOMES-BVPLUS
                                                   BVPLUS-OF-BVCHOP-ARG2 ;fixme
                                                   )))))

;gen
;add quoteps?
(defthm bvmult-5-4-false
  (implies (not (equal 0 (bvchop 2 x)))
           (equal (equal (bvmult 5 4 y) x)
                  nil)))

(defthm trim-of-repeatbit
  (equal (trim size1 (repeatbit size i))
         (if (< (ifix size1) (ifix size))
             (repeatbit size1 i)
             (repeatbit size i)))
  :hints (("Goal" :in-theory (e/d (trim repeatbit)
                                  (bvplus-recollapse)))))

(local (in-theory (disable +-becomes-bvplus-hack)))

;an idiom for rotating by 16 bits in a 32-bit field:
;gen!
(defthm bvor-of-bvshl-and-bvashr
  (implies (and (equal size (+ amt1 amt2))
                (unsigned-byte-p size x)
                (< amt1 size)
                (< amt2 size)
                (natp amt1)
                (natp amt2)
                (natp size)
                (< size 32)
                )
           (equal (bvor size (bvshl 32 x amt1) (bvashr 32 x amt2))
                  (leftrotate size amt1 x)))
  :hints (("Goal" :in-theory (e/d (bvsx bvshr leftrotate) (+-becomes-bvplus-hack)))))

(defthm bvor-of-bvashr-and-bvshl
  (implies (and (equal size (+ amt1 amt2))
                (unsigned-byte-p size x)
                (< amt1 size)
                (< amt2 size)
                (natp amt1)
                (natp amt2)
                (natp size)
                (< size 32)
                )
           (equal (bvor size (bvashr 32 x amt2) (bvshl 32 x amt1))
                  (leftrotate size amt1 x)))
  :hints (("Goal" :use (:instance bvor-of-bvshl-and-bvashr)
           :in-theory (disable bvor-of-bvshl-and-bvashr))))

(defthm bvor-of-bvshl-and-bvashr-alt
  (implies (and (unsigned-byte-p (+ amt1 amt2) x)
                (<= k (+ amt1 amt2))
                (< (+ amt1 amt2) 32)
                (posp amt1)
                (posp amt2)
                (natp k))
           (equal (bvor k (bvshl 32 x amt1) (bvashr 32 x amt2))
                  (bvchop k (leftrotate (+ amt1 amt2) amt1 x))))
  :hints (("Goal" :in-theory (enable bvshr bvsx leftrotate))))

(defthm bvor-of-bvashr-and-bvshl-alt
  (implies (and (unsigned-byte-p (+ amt1 amt2) x)
                (<= k (+ amt1 amt2))
                (< (+ amt1 amt2) 32)
                (posp amt1)
                (posp amt2)
                (natp k))
           (equal (bvor k (bvshl 32 x amt1) (bvashr 32 x amt2))
                  (bvchop k (leftrotate (+ amt1 amt2) amt1 x))))
  :hints (("Goal" :in-theory (disable bvor-of-bvshl-and-bvashr-alt)
           :use (:instance bvor-of-bvshl-and-bvashr-alt))))

(defthm bvor-of-bvshr-and-bvshl
  (implies (and (equal size (+ amt1 amt2))
                (unsigned-byte-p size x)
                (< amt1 size)
                (< amt2 size)
                (natp amt1)
                (natp amt2)
                (natp size)
                (< size 32)
                )
           (equal (bvor size (bvshr 32 x amt2) (bvshl 32 x amt1))
                  (leftrotate size amt1 x)))
  :hints (("Goal" :use (:instance bvor-of-bvshl-and-bvshr)
           :in-theory (disable bvor-of-bvshl-and-bvshr))))

(defthm bvor-of-bvshl-and-bvshr-alt
  (implies (and (unsigned-byte-p (+ amt1 amt2) x)
                (<= k (+ amt1 amt2))
                (< (+ amt1 amt2) 32)
                (posp amt1)
                (posp amt2)
                (natp k))
           (equal (bvor k (bvshl 32 x amt1) (bvshr 32 x amt2))
                  (bvchop k (leftrotate (+ amt1 amt2) amt1 x))))
  :hints (("Goal" :in-theory (enable bvshr bvsx leftrotate))))

(defthm bvor-of-bvshr-and-bvshl-alt
  (implies (and (unsigned-byte-p (+ amt1 amt2) x)
                (<= k (+ amt1 amt2))
                (< (+ amt1 amt2) 32)
                (posp amt1)
                (posp amt2)
                (natp k))
           (equal (bvor k (bvshl 32 x amt1) (bvshr 32 x amt2))
                  (bvchop k (leftrotate (+ amt1 amt2) amt1 x))))
  :hints (("Goal" :in-theory (disable bvor-of-bvshl-and-bvshr-alt)
           :use (:instance bvor-of-bvshl-and-bvshr-alt))))
;gen!
;gen the bvchop to any usb8
(defthm bvplus-of-bvchop-and-bvshl
  (equal (bvplus 32 (bvchop 8 x) (bvshl 32 y 8))
         (bvcat 24 y 8 x)))

;suddenly becomes needed for rc2 decryption proof
;maybe we should turn pluses into cats before pushing the minuses???
;gen!
(defthm bvuminus-of-bvcat-of-0-16-8
  (equal (bvuminus '16 (bvcat '8 x '8 '0))
         (bvcat '8 (bvuminus 8 x) '8 '0))
  :hints (("Goal" :in-theory (e/d (bvuminus bvcat bvminus) (bvminus-becomes-bvplus-of-bvuminus
                                                            bvchop-of-*)))))

;gen or add non-dag trim rule?
(defthm bvplus-of-bvcat
  (equal (bvplus 16 x (bvcat 24 y 8 0))
         (bvplus 16 x (bvcat 8 y 8 0)))
  :hints (("Goal" :in-theory (e/d (bvplus) (;anti-bvplus
                                            )))))

;gen!
(defthm bvplus-of-bvshl-becomes-bvcat
  (implies (and (unsigned-byte-p 8 x)
                (unsigned-byte-p 8 y))
           (equal (bvplus 16 x (bvshl 32 y 8)) ;trim the bvshl?
                  (bvcat 8 y 8 x))))

;fixme just add support for bvshl to trim? and then rewrite (bvshl 6 x 8) to 0..
;gen
(defthm bvplus-of-bvshl
  (equal (bvplus '6 (bvshl 32 x '8) y)
         (bvchop 6 y)))

(defthm +-of-minus
  (implies (and (equal (bvlt freesize x free) 'nil) ;or should we match (not (bvlt '7 x free)) ? (special case for that in the matching code?)
                (unsigned-byte-p freesize k)
                (unsigned-byte-p freesize free)
                (integerp k)
                (<= k (bvchop freesize free))
                (natp freesize)
                (unsigned-byte-p freesize x))
           (equal (binary-+ (- k) x)
                  (bvplus freesize (- k) x)))
  :hints (("Goal"
;          :expand (UNSIGNED-BYTE-P FREESIZE (- K)) ;this expands with the wrong defn..
           :in-theory (e/d (bvlt bvplus bvchop-of-sum-cases ;unsigned-byte-p
                              ) (;anti-bvplus
                                 <-BECOMES-BVLT
                                 <-BECOMES-BVLT-ALT
                                 <-BECOMES-BVLT-FREE
                                 )))))

(defthm +-of-minus-constant-version
  (implies (and (syntaxp (quotep k))
                (not (bvlt freesize x free)) ;or should we match (not (bvlt '7 x free)) ? (special case for that in the matching code?)
                (unsigned-byte-p freesize (- k))
                (unsigned-byte-p freesize free)
                (integerp k)
                (<= (- k) (bvchop freesize free))
                (natp freesize)
                (unsigned-byte-p freesize x))
           (equal (binary-+ k x)
                  (bvplus freesize k x)))
  :hints (("Goal" :use (:instance +-of-minus (k (- k)))
           :in-theory (disable +-of-minus))))

(defthm <-of-negative-when-usbp
  (implies (and (syntaxp (quotep k))
                (<= k 0)
                (unsigned-byte-p free x))
           (not (< x k))))

(defthm slice-of-leftrotate32-high
  (implies (and (<= amt low)
                (<= low high)
                (<= high 31)
                (unsigned-byte-p 5 amt) ;drop
                (natp high)
                (natp low)
                (natp amt))
           (equal (SLICE high low (LEFTROTATE32 amt x))
                  (SLICE (- high amt) (- low amt) x)))
  :hints (("Goal" :in-theory (e/d (leftrotate leftrotate32) (+-BECOMES-BVPLUS-HACK)))))

(defthm <-cancel-lemma-100
  (implies (and (< 0 x)
                (rationalp y)
                (rationalp z)
                (rationalp x))
           (equal (< (+ x (* x z)) (* x y))
                  (< (+ 1 z) y)))
  :hints (("Goal" :use (:instance <-*-left-cancel (z x) (x (+ 1 z))))))

(defthm getbit-of-+-of-expt
  (implies (and (natp n)
                (natp x))
           (equal (GETBIT n x)
                  (bitnot (getbit n (+ (expt 2 n) x)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable getbit-of-plus))))

(defthm getbit-of-+-bvchop-expand
  (implies (and (natp n)
                (natp x))
           (equal (getbit n (bvchop n x))
                  (if (equal 0 (getbit n x))
                      (getbit n (bvchop (+ 1 n) x))
                    (bitnot (getbit n (bvchop (+ 1 n) x))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable getbit-of-plus))))

(defthmd getbit-of-+-bvchop-expand2
  (implies (and (natp n)
                (Natp y)
                (natp x))
           (equal (getbit n (+ y (bvchop n x)))
                  (if (equal 0 (getbit n x))
                      (getbit n (bvchop (+ 1 n) (+ y x)))
                    (bitnot (getbit n (bvchop (+ 1 n) (+ y x)))))))
;  :rule-classes nil
  :hints (("Goal" :in-theory (enable getbit-of-plus))))

(defthmd getbit-of-+-bvchop-expand3
  (implies (and (natp n)
                (Natp y1)
                (Natp y2)
                (natp x))
           (equal (getbit n (+ y1 (bvchop n x) y2))
                  (if (equal 0 (getbit n x))
                      (getbit n (bvchop (+ 1 n) (+ y1 y2 x)))
                    (bitnot (getbit n (bvchop (+ 1 n) (+ y1 y2 x)))))))
;  :rule-classes nil
  :hints (("Goal" :use (:instance getbit-of-+-bvchop-expand2 (y (+ y1 y2))))))

(defthmd getbit-of-+-bvchop-expand4
  (implies (and (natp n)
                (Natp y1)
                (Natp y2)
                (natp x))
           (equal (getbit n (+ y1 y2 (bvchop n x)))
                  (if (equal 0 (getbit n x))
                      (getbit n (bvchop (+ 1 n) (+ y1 y2 x)))
                    (bitnot (getbit n (bvchop (+ 1 n) (+ y1 y2 x)))))))
  :hints (("Goal" :use (:instance getbit-of-+-bvchop-expand3)
           :in-theory (disable getbit-of-+-bvchop-expand3))))

(defthm unsigned-byte-p-when-zp-cheap
  (implies (zp n)
           (equal (unsigned-byte-p n x)
                  (and (equal 0 x)
                       (equal 0 n))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable zp unsigned-byte-p))))

(defthmd unsigned-byte-p-of-size-1
  (equal (unsigned-byte-p 1 carry)
         (or (equal 0 carry)
             (equal 1 carry))))

;make this work!
;; (defthmd bvplus-becomes-ripple-carry-adder-helper
;;    (implies (and (natp n)
;;                  (unsigned-byte-p n x)
;;                  (unsigned-byte-p n y)
;;                  (unsigned-byte-p 1 carry))
;;             (equal (+ carry x y) ;(bvplus (+ 1 n) carry (bvplus (+ 1 n) x y))
;;                    (ripple-carry-adder n x y carry)))
;;    :otf-flg t
;;    :hints (("Goal" :in-theory (enable ripple-carry-adder
;;                                       unsigned-byte-p-of-size-1
;;                                       ;GETBIT-OF-PLUS yuck
;;                                       )
;;             :induct t
;;             :do-not '(generalize eliminate-destructors))))


;rename
(defthmd bvchop-recollapse
  (implies (natp n)
           (equal (+ (BVCHOP n x)
                     (* (EXPT 2 n)
                        (GETBIT n x)))
                  (bvchop (+ 1 n) x)))
  :hints (("Goal" :in-theory (enable bvcat logapp)
           :use (:instance split-bv (y (bvchop (+ 1 n) x)) (n (+ 1 n)) (m n)))))



(defthm unsigned-byte-p-of-+-of-bvchop-and-*-of-expt
  (implies (and (unsigned-byte-p 1 bit)
                (posp n))
           (unsigned-byte-p n (+ (BVCHOP (+ -1 N) x)
                                 (* (EXPT 2 (+ -1 N)) bit))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p)
           :cases ((equal 0 bit)))))


(defthm recollapse-sum-bits
  (implies (posp n)
           (equal (+ (* (expt 2 n)
                        (getbit 1 x))
                     (* (expt 2 (+ -1 n))
                        (getbit 0 x)))
                  (* (expt 2 (+ -1 n)) (slice 1 0 x))))
  :hints (("Goal" :in-theory (enable logapp bvcat expt-of-+)
           :use (:instance split-bv (y (bvchop 2 x)) (n 2) (m 1)))))
;gen the 8
(defthm unsigned-byte-p-1-of-*
  (implies (integerp x)
           (equal (unsigned-byte-p '1 (binary-* '8 x))
                  (equal 0 x))))

(defthm unsigned-byte-p-of-*-of-constant-helper
  (implies (and (<= (expt 2 size) k)
                (integerp k)
                (integerp x))
           (equal (unsigned-byte-p size (binary-* k x))
                  (and (natp size)
                       (equal 0 x))))
  :hints (("Goal" :cases ((< k (* k x))(= k (* k x)))
           :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-of-*-of-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (<= (expt 2 size) k) ;gets computed
                (integerp k)
                (integerp x))
           (equal (unsigned-byte-p size (binary-* k x))
                  (and (natp size)
                       (equal 0 x))))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-*-of-constant-helper)
           :in-theory (disable unsigned-byte-p-of-*-of-constant-helper))))

;where should this go? it needs stuff from bv-syntax.lisp
;rename to -bind-free
(defthmd mod-becomes-bvmod-better
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'xsize x))
                (bind-free (bind-var-to-unsigned-term-size 'ysize y))
                (force (unsigned-byte-p-forced xsize x))
                (force (unsigned-byte-p-forced ysize y))
;(natp xsize) ;drop
;(natp ysize) ;drop
                )
           (equal (mod x y)
                  (bvmod (max xsize ysize) x y)))
  :hints (("Goal" :use (:instance mod-becomes-bvmod-core (size (max xsize ysize)))
           :in-theory (enable ;mod-becomes-bvmod-core
                       unsigned-byte-p-forced))))

(theory-invariant (incompatible (:definition bvmod) (:rewrite mod-becomes-bvmod-better)))

(defthm bvlt-of-bvmod-same
  (equal (bvlt size (bvmod size x y) y)
         (not (equal 0 (bvchop size y))))
  :hints (("Goal" :in-theory (enable bvlt bvmod))))

(defthmd *-becomes-bvmult-non-dag
  (implies (and (unsigned-byte-p-forced n x)
                (unsigned-byte-p-forced m y))
           (equal (* x y)
                  (bvmult (+ m n) x y)))
  :hints (("Goal"
           :use (:instance <-of-*-and-*
                           (x1 x)
                           (y1 y)
                           (x2 (EXPT 2 N))
                           (y2 (EXPT 2 m)))
           :cases ((equal 0 x)
                   (and (equal 0 y) (equal 0 x)))
           :in-theory (e/d (BVMULT UNSIGNED-BYTE-P unsigned-byte-p-forced)
                           (<-of-*-and-*
                            bvchop-of-*)))))

(DEFTHM
  BVSHL-REWRITE-FOR-CONSTANT-SHIFT-AMOUNT
  (IMPLIES (AND (SYNTAXP (QUOTEP SHIFT-AMOUNT))
                (SYNTAXP (QUOTEP WIDTH))
                (<= SHIFT-AMOUNT WIDTH)
                (NATP SHIFT-AMOUNT)
                (INTEGERP WIDTH))
           (EQUAL (BVSHL WIDTH X SHIFT-AMOUNT)
                  (BVCAT (- WIDTH SHIFT-AMOUNT)
                         x
                         SHIFT-AMOUNT 0)))
  :HINTS (("Goal" :in-theory (enable BVSHL-REWRITE-WITH-BVCHOP))))


;todo move to bv library
(defthm sbvlt-of-bvplus-of-1-when-sbvlt-rev
  (implies (sbvlt 32 y x)
           (not (sbvlt 32 x (bvplus 32 1 y))))
  :hints (("Goal" :in-theory (enable bvplus bvlt sbvlt-rewrite))))

;can help prove loop functions terminate
(defthm <-of-bvplus-and-bvchop-same
  (implies (and (syntaxp (quotep k))
                (posp size)
                (integerp k))
           (equal (< (bvplus size k x) (bvchop size x))
                  (and (bvle size 1 k)
                       (bvle size (- (expt 2 size) k) x))))
  :hints (("Goal" :in-theory (enable bvlt bvplus bvchop-of-sum-cases))))

;; i-1 < -1 is false when i >= 0
(defthm sbvlt-of-bvminus-of-1-and-minus-1
  (implies (SBVLT 32 4294967295 I) ;todo: does this get rewritten to >= 0 ?
           (not (SBVLT 32 (BVMINUS 32 I 1) 4294967295)))
  :hints (("Goal" :in-theory (enable sbvlt bvminus))))

(defthm sbvlt-of-bvplus-of-minus-1-and-minus-1
  (implies (SBVLT 32 4294967295 I) ;todo: does this get rewritten to >= 0 ?
           (not (SBVLT 32 (BVplus 32 4294967295 I) 4294967295)))
  :hints (("Goal" :in-theory (enable sbvlt bvminus))))

;; i-1 < i unless the subtraction overflows
(defthm sbvlt-of-bvminus-of-1
  (equal (sbvlt 32 (bvminus 32 i 1) i)
         (not (equal (expt 2 31) (bvchop 32 i))))
  :hints (("Goal" :in-theory (enable sbvlt bvminus))))

(defthm sbvlt-of-bvplus-of-minus-1-and-1
  (equal (sbvlt 32 (bvplus 32 4294967295 i) i)
         (not (equal (expt 2 31) (bvchop 32 i))))
  :hints (("Goal" :in-theory (enable sbvlt bvminus bvplus))))

(defthm not-bvlt-of-one-less-when-not-bvlt-and-not-zero
  (implies (and ;(integerp dx)
                (not (EQUAL '0 (BVCHOP '31 dx))) ;move to rhs?
                (UNSIGNED-BYTE-P '31 olddx) ;gen?
                (NOT (BVLT '31 olddx dx)))
           (equal (BVLT '31 olddx (BVPLUS '32 4294967295 dx))
                  nil
                  ))
  :hints (("Goal" :in-theory (enable bvminus bvlt bvchop-of-sum-cases bvplus))))

;or maybe just go to bvlt
(defthm <-of-bvplus-same-gen
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p size x)
                (posp size)
                (integerp k))
           (equal (< (bvplus size k x) x)
                  (and (bvle size 1 k)
                       (bvle size (- (expt 2 size) k) x))))
  :hints (("Goal" :in-theory (enable bvlt bvplus bvchop-of-sum-cases))))

;todo: do we prefer bvminus or bvuminus?
(defthm <-of-bvminus-of-minus-1-and-bvuminus-same
  (equal (< (bvminus 32 4294967295 (nth 0 params))
            (bvuminus 32 (nth 0 params)))
         (bvlt '32 '0 (nth '0 params)))
  :hints (("Goal" :in-theory (enable bvminus-becomes-bvplus-of-bvuminus))))

;disabled because it seemed to be causing slowdown
(defthmd sbvlt-bound-lemma
  (implies (and (<= (- (expt 2 31) 1) n)
                (unsigned-byte-p 32 n))
           (equal (sbvlt 32 n 0)
                  (not (equal (- (expt 2 31) 1) n))))
  :hints (("Goal" :in-theory (enable sbvlt-rewrite bvplus bvchop-of-sum-cases))))

;rename
(defthmd bvplus-of-unary-minus
  (implies (integerp x)
           (equal (bvplus size y (- x))
                  (bvplus size y (bvuminus size x))))
  :hints (("Goal" :in-theory (e/d (bvuminus bvminus) (bvminus-becomes-bvplus-of-bvuminus)))))

(defthmd bvplus-of-unary-minus-arg2
  (implies (natp size)
           (equal (bvplus size (- x) y)
                  (bvplus size (bvuminus size x) y)))
  :hints (("Goal" :in-theory (e/d (bvuminus bvminus) (bvminus-becomes-bvplus-of-bvuminus)))))

(defthmd bvnot-trim-all
  (implies (and (syntaxp (term-should-be-trimmed2 size x 'all))
                (natp size))
           (equal (bvnot size x)
                  (bvnot size (trim size x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthm slice-too-high-is-0-cheap
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize x) (newsize))
                ;make sure it's not nil:
                (natp newsize) ;newsize continues to be a bad name for uses like this...
                (natp low)
                (<= newsize low)
                (force (unsigned-byte-p newsize x))) ;use unsigned-byte-p-forced?
           (equal (slice high low x)
                  0))
  :hints (("Goal" :in-theory (e/d (slice) (BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

;yikes this doubles the number of occurrences of y...

(defthmd bvor-of-large-and-small
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize x) (newsize))
                (< newsize n)
                (force (unsigned-byte-p newsize x))
                (natp n)
                (< 1 n)
                (natp newsize)
                (integerp y) ;bozo
                (integerp x) ;bozo
                (< 1 newsize) ;drop?
                )
           (equal (BVOR n x y)
                  (bvcat (- n newsize)
                         (slice (+ -1 n) newsize y) newsize
                         (bvor newsize (bvchop newsize x) (bvchop newsize y)))))
  :hints (("Goal" :in-theory (e/d (SLICE-TOO-HIGH-IS-0) (INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM
                                                         NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG)))))

(defthm bvor-cat-extra-bit-alt
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize x) (newsize))
                (<= newsize lowsize)
                (< lowsize size)
                (natp size)
                (natp lowsize)
                (natp newsize)
                (force (unsigned-byte-p newsize x))
                )
           (equal (bvor size (bvcat 1 y lowsize z) x)
                  (bvcat 1 y lowsize (bvor lowsize x z))))
  :hints (("Goal" :in-theory (enable GETBIT-TOO-HIGH))))

;bozo might this be bad?
(defthmd bvxor-of-bvif
  (implies (and (natp size)
                (< 0 size)
                (integerp a)
                (integerp b)
                (integerp x)
                )
           (equal (BVXOR size (BVIF size test a b) x)
                  (bvif size
                         test
                         (bvxor size a x)
                         (bvxor size b x))))
  :hints (("Goal" :in-theory (enable bvif myif bvxor))))

(defthmd bvxor-of-bvif-2
  (implies (and (natp size)
                (< 0 size)
                (integerp a)
                (integerp b)
                (integerp x)
                )
           (equal (BVXOR size x (BVIF size test a b))
                  (bvif size
                         test
                         (bvxor size x a)
                         (bvxor size x b))))
  :hints (("Goal" :in-theory (enable bvif myif bvxor))))

;rename
;needed?
(defthm bvxor-of-bvif-and-bvif
  (implies (and (integerp a)
                (integerp b)
                (integerp c)
                (integerp d)
                (integerp size)
                (< 0 size)
                )
           (equal (bvxor size
                           (bvif size test a b)
                           (bvif size test c d))
                  (bvif size test (bvxor size a c) (bvxor size b d))))
  :hints (("Goal" :in-theory (enable bvif myif bvxor))))

;saves us from having to chose a prefered form.  maybe i'm just being a wimp
(defthm bvmult-equal-bvchop-times-rewrite
  (implies (and (integerp x)
                (integerp y))
           (equal (equal (bvmult 32 x y)
                         (bvchop 32 (* x y)))
                  t))
  :hints (("Goal" :in-theory (e/d (bvmult) (bvchop-of-*)))))

(defthm sbvlt-of-bvsx-and-constant
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p 7 k)) ;gen?
           (equal (sbvlt 32 (bvsx 32 8 x) k)
                  (sbvlt 8 x k)))
  :hints (("Goal" :in-theory (enable bvlt bvsx sbvlt-rewrite))))

(defthm sbvlt-of-constant-and-bvsx
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p 7 k)) ;gen?
           (equal (sbvlt 32 k (bvsx 32 8 x))
                  (sbvlt 8 k x)))
  :hints (("Goal" :in-theory (enable bvlt bvsx sbvlt-rewrite))))

;; Rules that conflict wth bvplus:
(defthy anti-bvplus '(bvplus-recollapse bvplus-of-plus bvplus-of-plus2))
