; More rules about bit vectors
;
; Copyright (C) 2017-2021 Kestrel Technology, LLC
; Copyright (C) 2022-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Organize this material

;(include-book "kestrel/arithmetic-light/floor" :dir :system)
;(include-book "kestrel/arithmetic-light/ash" :dir :system)
(include-book "logext")
(include-book "bvplus")
(include-book "bv-syntax")
(include-book "rules") ;(local (include-book "rules"))
(local (include-book "logior"))
(local (include-book "logior-b"))
(local (include-book "logxor-b"))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/divide" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

(defthm equal-of-ifix-self
  (equal (equal (ifix x) x)
         (integerp x)))

;(in-theory (disable mod-x-y-=-x+y-for-rationals)) ;seemed to lead to generalization/

;todo: think about this
(defthm signed-byte-p-of-bvchop
  (signed-byte-p 64 (bvchop 32 x))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

(defthm plus-of-minus-subst-constant
  (implies (and (equal x (+ k y)) ;k is a free var
                (syntaxp (quotep k))
                (acl2-numberp k))
           (equal (+ (- y) x)
                  k)))

;; (defthm getbit-of-ash
;;   (implies (and (natp c)
;;                 (natp i)
;;                 (natp n))
;;            (equal (getbit n (ash i c))
;;                   (getbit n (bvcat (+ 1 n (- C)) i c 0))))
;;   :hints (("Goal" :in-theory (e/d (ash GETBIT BVCAT logapp SLICE
;;                                        BVCHOP-OF-LOGTAIL)
;;                                   (
;;
;;                                    )))))

;(in-theory (enable logext-of-sum-trim-constant))

(defthm getbit-of-slice-both
  (implies (and (natp n)
                (natp low)
;                (integerp x)
                (integerp high))
           (equal (getbit n (slice high low x))
                  (if (<= n (+ high (- low)))
                      (getbit (+ low n) x)
                    0)))
  :hints (("Goal" :use ((:instance GETBIT-OF-SLICE-TOO-HIGH
                                   (X X)
                                   (LOW LOW)
                                   (HIGH HIGH)
                                   (N N))
                        (:instance getbit-of-slice
                                   (x x)
                                   (low low)
                                   (high high)
                                   (n n)))
           :in-theory (disable getbit-of-slice))))

;gen the -1
(defthm ash-of-bvchop-32-and-minus1
  (equal (ash (bvchop 32 x) -1)
         (slice 31 1 x))
  :hints (("Goal" :in-theory (enable ash LOGTAIL-BECOMES-SLICE-BIND-FREE floor-of-2-becomes-logtail-of-1))))

(defthm integerp-of-*-of-1/2
  (implies (integerp x)
           (equal (integerp (* 1/2 x))
                  (equal 0 (getbit 0 x))))
  :hints (("Goal" :in-theory (e/d (getbit
                                   bvchop
                                   ifix)
                                  (

                                   )))))


(defthm UNSIGNED-BYTE-P-shift-lemma
  (IMPLIES (AND (natp n)
                (UNSIGNED-BYTE-P XSIZE X)
                (<= N XSIZE))
           (UNSIGNED-BYTE-P (- XSIZE n)
                            (FLOOR (* X (EXPT 2 (- N))) 1)))
  :hints (("Goal" :in-theory (enable UNSIGNED-BYTE-P))))

(defthm ash-negative-becomes-slice
  (implies (and (< n 0)
                (bind-free (bind-var-to-bv-term-size 'xsize x))
                (unsigned-byte-p xsize x)
                (<= (- n) xsize)
                (integerp n)
                )
           (equal (ash x n)
                  (slice (+ -1 xsize) (- n) x)))
  :hints (("Goal"
           :use (:instance UNSIGNED-BYTE-P-shift-lemma (n (- n)))
           :in-theory (e/d (ash SLICE LOGTAIL ;floor
                                )
                           ()))))

(defthmd bvand-of-+-arg2
  (implies (and (natp width)
                (integerp x)
                (integerp y))
           (equal (bvand width (+ x y) z)
                  (bvand width (bvplus width x y) z)))
  :hints (("Goal" :in-theory (enable bvplus))))

(theory-invariant (incompatible (:rewrite bvand-of-+-arg2) (:definition bvplus)))

(defthmd bvand-of-+-arg3
  (implies (and (natp width)
                (integerp x)
                (integerp y))
           (equal (bvand width z (+ x y))
                  (bvand width z (bvplus width x y))))
  :hints (("Goal" :in-theory (enable bvplus))))

(theory-invariant (incompatible (:rewrite bvand-of-+-arg3) (:definition bvplus)))

;move
;todo: gen to reduce the constant even if not down to 0
(defthm mod-of-+-of-constant
  (implies (and (syntaxp (quotep k))
                (syntaxp (quotep j))
                (equal 0 (mod k j))
                (rationalp j)
                (rationalp k)
                (not (equal 0 j))
                (integerp x))
           (equal (mod (+ k x) j)
                  (mod x j))))

(defthm slice-of-all-ones-too-high
  (implies (and (natp low)
                (natp high)
                ;(<= low high)
                )
           (equal (slice high low (+ -1 (expt 2 low)))
                  0))
  :hints (("Goal" :in-theory (e/d (slice)
                                  (repeatbit

                                   logtail-of-plus)))))

(defthm ash-becomes-bvcat
  (implies (and (bind-free (bind-var-to-bv-term-size 'xsize x)) ;only works for constant size?
                (force (unsigned-byte-p xsize x))
                (natp amt))
           (equal (ash x amt)
                  (bvcat (+ xsize amt)
                               x
                               amt
                               0)))
  :hints (("Goal" :in-theory (enable bvcat ash))))

(defthm ash-of-ones
  (implies (and (natp n)
                (natp low))
           (equal (ASH (+ -1 (EXPT 2 n)) LOW)
                  (bvcat n (+ -1 (EXPT 2 n))
                               low 0)))
  :hints (("Goal" :in-theory (e/d (bvcat ash BVUMINUS BVMINUS)
                                  (;BVPLUS-OF-UNARY-MINUS-ARG2
                                   BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

;helpful for address calculations (yikes, this almost seems to violate our normal form)
(defthmd logext-of-bvplus-64
  (implies (and (integerp x)
                (integerp y))
           (equal (logext 64 (bvplus 64 x y))
                  (logext 64 (+ x y))))
  :hints (("Goal" :in-theory (enable bvplus))))

;really want this for every unary function
(defthm unsigned-byte-p-of-if-two-constants
  (implies (and (syntaxp (and (quotep n)
                              (quotep x1)
                              (quotep x2))))
           (equal (unsigned-byte-p n (if test x1 x2))
                  (if test
                      (unsigned-byte-p n x1)
                      (unsigned-byte-p n x2)))))


(defthm bvchop-of-ash
  (implies (and (natp size)
                (natp n))
           (equal (bvchop size (ash x n))
                  (bvcat (- size n) x n 0)))
  :hints (("Goal" :in-theory (e/d (ash slice logtail)
                                  ()))))

;used by axe
(defthmd natp-of-+
  (implies (and (natp x)
                (natp y))
           (natp (+ x y))))

;used by axe
(defthmd natp-of-nfix
  (natp (nfix x)))

;the bvcat of 0 is essentially multiplication by a power of 2
(defthm bvmult-of-bvcat-of-0
  (implies (and (syntaxp (and (quotep k)
                              (quotep lowsize)
                              (quotep highsize)
                              (quotep size)))
                (equal highsize (- size lowsize))
                (integerp x)
                (integerp k)
                (natp lowsize)
                (natp highsize)
                (natp size))
           (equal (bvmult size k (bvcat highsize x lowsize 0))
                  (bvmult size
                                (* k (expt 2 lowsize)) ;gets computed
                                x)))
  :hints (("Goal" :in-theory (e/d (bvmult bvcat)
                                  (bvchop-of-*-of-bvchop-arg2))
           :use (:instance bvchop-of-*-of-bvchop-arg2
                           (y (* (expt 2 lowsize) x))
                           (x k)))))

;this is a mask of all 1's (do we prefer repeatbit or 2^n-1 to represent such a thing?)
(defthm bvuminus-of-1-arg2-alt
  (equal (bvuminus size 1)
         (repeatbit size 1))
  :hints (("Goal" :in-theory (e/d (bvuminus bvminus repeatbit)
                                  (bvminus-becomes-bvplus-of-bvuminus)))))

;goes to 2^n-1, but I think I like repeatbit better
(in-theory (disable repeatbit-of-1-arg2))

;todo: move
(defthm equal-of-bvchop-and-constant-when-signed-byte-p
  (implies (and (syntaxp (want-to-strengthen (equal k (bvchop 64 x))))
                (syntaxp (quotep k))
                (unsigned-byte-p 64 k)
                (signed-byte-p 64 x))
           (equal (equal k (bvchop 64 x))
                  (equal (logext 64 k) ;gets computed
                         x)))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

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

;gen
(defthm signed-byte-p-of-one-more
  (implies (and (syntaxp (want-to-weaken (signed-byte-p 48 (+ 1 x))))
                (signed-byte-p 48 x))
           (equal (signed-byte-p 48 (+ 1 x))
                  (not (equal x (+ -1 (expt 2 47))))))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

;move
(defthm getbit-of-logior-better
  (equal (getbit n (logior a b))
         (bvor 1 (getbit n a)
               (getbit n b)))
  :hints (("Goal" :in-theory (enable bvor))))

;(in-theory (disable getbit-of-logior)) ; consider what to do here

;move
(defthm getbit-of-bvchop-both
  (implies (and (natp m) ;drop?
                (natp n))
           (equal (getbit m (bvchop n x))
                  (if (< m n)
                      (getbit m x)
                    0))))

;todo: think about this
(defthm signed-byte-p-of-bvchop
  (signed-byte-p 64 (bvchop 32 x))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

;; This can help if the model splits into cases unnecessarily, but we are
;; attempting to handle that better by keeping JCC/CMOVCC/SETCC-SPEC disabled.
(defthm not-sbvlt-of-0-recollapse
  (equal (if (equal 0 (bvchop 32 x))
             t
           (not (equal 0 (getbit 31 x))))
         (not (sbvlt 32 0 x)))
  :hints (("Goal" :in-theory (enable sbvlt logext))))

;; This can help if the model splits into cases unnecessarily, but we are
;; attempting to handle that better by keeping JCC/CMOVCC/SETCC-SPEC disabled.
(defthm not-sbvlt-of-0-recollapse-2
  (implies (unsigned-byte-p 32 x)
           (equal (if (equal 0 x)
                      t
                    (not (equal 0 (getbit 31 x))))
                  (not (sbvlt 32 0 x))))
  :hints (("Goal" :in-theory (enable sbvlt logext))))

(defthmd equal-of-bitxor-and-1
  (equal (equal (bitxor x y) 1)
         (or (and (equal (getbit 0 x) 1)
                  (equal (getbit 0 y) 0))
             (and (equal (getbit 0 x) 0)
                  (equal (getbit 0 y) 1)))))


(defthm +-of-bvplus-of-x-and-minus-x
  (implies (and (unsigned-byte-p 32 x)
                (bvlt 32 x (- k)))
           (equal (+ (bvplus 32 k x)
                     (- x))
                  (bvchop 32 k)))
  :hints (("Goal" :in-theory (enable bvplus bvchop-of-sum-cases bvlt))))

;In case we don't want to commit to a normal form
(defthm equal-of-bvchop-of-+-and-bvplus
  (implies (and (integerp x)
                (integerp y))
           (equal (equal (bvchop 64 (+ x y))
                         (bvplus 64 x y))
                  t))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm bvsx-lemma
  (equal (bvcat 128 ;not tight
                (if (equal 1
                           (getbit 63 x))
                    18446744073709551615 0)
                64 x)
         (bvsx 128 64 x))
  :hints (("Goal" :in-theory (enable
                              bvsx ;todo
                              ))))

(defthmd getbit-when-logext-bound
  (implies (and (<= k (logext 64 x)) ;k is a free variable
                (syntaxp (quotep k))
                (natp k))
           (equal (getbit 63 x)
                  0))
  :hints (("Goal" :in-theory (enable logext))))

(defthm mod-of-bvchop-and-2
  (equal (mod (bvchop 63 x) 2)
         (getbit 0 x))
  :hints (("Goal" :in-theory (e/d (bvchop getbit)
                                  ()))))

;move to an arith library
(defthm <-of-constant-when-<-of-constant-integer
  (implies (and (syntaxp (quotep k))
                (integerp k) ;gets computed
                (< free x)
                (syntaxp (quotep free))
                (integerp free)  ;gets computed
                (<= k (+ 1 free)) ;gets computed
                (integerp x))
           (not (< x k))))

;move to an arith library
(defthm <-of-constant-when-<=-of-constant-integer
  (implies (and (syntaxp (quotep k))
                (integerp k) ;gets computed
                (<= free x)
                (syntaxp (quotep free))
                (integerp free)  ;gets computed
                (<= k free) ;gets computed
                (integerp x))
           (not (< x k))))

(defthm slice-of-if-arg3
  (equal (slice high low (if test v1 v2))
         (if test
             (slice high low v1)
             (slice high low v2))))

(defthm ash-of-if
  (equal (ash (if test i1 i2) c)
         (if test
             (ash i1 c)
           (ash i2 c))))

(defthm bvchop-of-if-when-constants
  (implies (syntaxp (and (quotep n)
                         (quotep k1)
                         (quotep k2)))
           (equal (bvchop n (if test k1 k2))
                  (if test
                      (bvchop n k1)
                    (bvchop n k2)))))

;todo: or go to bvplus of bvplus
(defthm bvplus-of-+-combine-constants
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (integerp x)
                (integerp k1)
                (integerp k2))
           (equal (bvplus size k1 (+ k2 x))
                  (bvplus size (+ k1 k2) x)))
  :hints (("Goal" :in-theory (enable bvplus))))

; Helps resolve updates to ESP
; Note that this replaces BVPLUS with +.  TODO: Think about when we want this.
(defthmd bvplus-of-constant-when-overflow
  (implies (and (syntaxp (quotep k))
                (<= (- (expt 2 32) k) x)
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 k))
           (equal (bvplus 32 k x)
                  (+ (- (- (expt 2 32) k)) ;gets computed
                     x)))
  :hints (("Goal" :in-theory (enable bvplus bvchop-of-sum-cases))))

(defthmd bvcat-of-logtail-low
  (implies (and (natp lowsize)
                (natp highsize)
                (natp n))
           (equal (bvcat highsize highval
                         lowsize
                         (logtail n lowval))
                  (bvcat highsize highval
                         lowsize
                         (slice (+ -1 lowsize n)
                                n
                                lowval))))
  :hints (("Goal" :in-theory (enable logtail-of-bvchop-becomes-slice
                                     bvchop-of-logtail-becomes-slice))))
