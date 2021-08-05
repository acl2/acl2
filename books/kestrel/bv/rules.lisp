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

;; This book contains a large number of theorems, many of which mix several BV
;; operators.  It would be good to sort these into more specific books when
;; possible.

(include-book "signed-byte-p")
;(include-book "rules0") ;for BVCHOP-OF-FLOOR-OF-EXPT-OF-2-CONSTANT-VERSION
(include-book "kestrel/utilities/polarity" :dir :system)
(include-book "kestrel/utilities/myif" :dir :system)
(include-book "kestrel/utilities/smaller-termp" :dir :system)
(include-book "single-bit")
(include-book "bvxor")
(include-book "bitor")
(include-book "bitand")
(include-book "logapp")
(include-book "bvcat2")
(include-book "bvif")
(include-book "sbvlt")
(include-book "logext")
(include-book "bvnot")
(include-book "bitxor")
(include-book "bvmult")
(include-book "bvuminus")
(include-book "kestrel/booleans/booleans" :dir :system) ;why included here? maybe to get bool-to-bit...
(include-book "kestrel/arithmetic-light/lg" :dir :system)
(include-book "bv-syntax")
(include-book "leftrotate")
(include-book "leftrotate32")
(include-book "sbvrem")
(include-book "bvdiv")
(include-book "sbvdiv")
(include-book "sbvdivdown")
(include-book "bvsx")
(include-book "repeatbit2")
(include-book "bvshr")
(include-book "bvshl")
(include-book "bool-to-bit")
(include-book "bit-to-bool")
(include-book "bitxnor")
(include-book "slice2")
(include-book "sbvlt-rules")
(include-book "slice-rules")
(include-book "getbit-rules")
(include-book "bvcat-rules")
(local (include-book "kestrel/arithmetic-light/denominator" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor-mod-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))
(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/arithmetic-light/nonnegative-integer-quotient" :dir :system))
(local (include-book "kestrel/arithmetic-light/numerator" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/divides" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divides" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/evenp" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "floor-mod-expt"))
(local (include-book "arith")) ;todo for integerp-squeeze
;(local (include-book "arith2"))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
;(local (include-book "kestrel/library-wrappers/ihs-quotient-remainder-lemmas" :dir :system)) ;drop
(local (include-book "kestrel/library-wrappers/ihs-logops-lemmas" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system)) ;move
;(local (include-book "kestrel/library-wrappers/arithmetic-top-with-meta" :dir :system)) ; for EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))


(local (in-theory (disable ;EQUAL-/
                           logapp-0
                           UNSIGNED-BYTE-P-OF-+-WHEN-<-OF-LOGTAIL-AND-EXPT ;move
                           UNSIGNED-BYTE-P-PLUS
                           LOGAND-WITH-MASK
                           )))

;include rotate book?

;rename
(defthm bvchop-shift-gen-constant-version
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                (integerp x)
                (natp n))
           (equal (bvchop n (* k x))
                  (* k (bvchop (- n (+ -1 (integer-length k))) x))))
  :hints (("Goal" :use (:instance bvchop-shift-gen (m (+ -1 (integer-length k))))
           :in-theory (e/d (power-of-2p)( bvchop-shift-gen)))))

(defthm bvchop-of-expt-alt
  (implies (and (syntaxp (quotep k)) ;new
                (power-of-2p k)
                (natp size1))
           (equal (bvchop size1 k)
                  (if (<= size1 (lg k))
                      0
                    k)))
  :hints (("Goal" :use (:instance bvchop-of-expt (size2 (lg k)))
           :in-theory (e/d (power-of-2p lg) ( bvchop-of-expt)))))

(defthm equal-of-slice-and-constant-extend-when-bvchop-known
  (implies (and (syntaxp (and (quotep high)
                              (quotep low)
                              (quotep k1)
                              (want-to-strengthen (equal (slice 31 low x) k1))))
                (equal k2 (bvchop size x))
                (syntaxp (and (quotep k2)
                              (quotep size)))
                (integerp size)
                (<= low size)
;                (integerp x)
                (natp high)
                (natp low)
                (<= low high)
                )
           (equal (equal (slice high low x) k1)
                  (and (unsigned-byte-p (+ high (- low) 1) k1)
                       (equal (bvchop (+ 1 high) x)
                              (bvcat (+ high (- low) 1)
                                     k1
                                     low
                                     k2))))))

;get rid of this?
;; (defund smyif (size test thenpart elsepart)
;;   (myif test
;;         (logext size thenpart)
;;         (logext size elsepart)))

;; (defthm bvchop-of-smyif-less
;;   (implies (and (< size size2)
;;                 (integerp size)
;;                 (integerp size2)
;;                 (< 0 size2)
;;                 (integerp x) ;bozo?
;;                 (integerp y) ;bozo
;;                 (< 0 size))
;;            (equal (bvchop size (smyif size2 test x y))
;;                   (bvif size test (bvchop size x) (bvchop size y))))
;;   :hints (("Goal" :in-theory (enable smyif bvif myif))))

;trying disabled
(defthmd logapp-recollect-from-shift
  (implies (and (integerp x)
                (<= 0 n))
           (equal (* X (EXPT 2 N))
                  (LOGAPP N 0 X)))
  :hints (("Goal" :in-theory (enable logapp))))

(theory-invariant (incompatible (:definition logapp ) (:rewrite LOGAPP-RECOLLECT-FROM-SHIFT)))

(defthm logext-of-logtail
  (implies (and (natp n)
                (< 0 n)
                (<= 0 m)
                (natp m)
                (integerp x)
                )
           (equal (logext n (LOGTAIL M X))
                  (logtail m (logext (+ m n) x))))
  :hints (("Goal" :in-theory (e/d (slice
                                   ;why does slice get introduced?
                                   bvchop-of-logtail
                                   logext) (;hack-6
                                            BVCHOP-OF-LOGTAIL-BECOMES-SLICE
                                                   LOGBITP-IFF-GETBIT ;why? need getbit of logtail?
                                                   )))))


(defthm expt-hack
  (implies (integerp n)
           (equal (* 2 (expt 2 (+ -1 n)))
                  (expt 2 n)))
  :hints (("Goal" :in-theory (enable expt))))

(defthm zbp-times-2
  (equal (zbp (* 2 x))
         (not (equal x 1/2))))

(local (in-theory (disable FLOOR-MINUS-ERIC-BETTER)))

;(in-theory (disable binary-logand binary-logxor))

;(local (in-theory (disable MOD-X-Y-=-X)))

(defthm logbitp-of-logxor
  (implies (and (natp i)
                (integerp j1)
                (integerp j2))
           (equal (logbitp i (logxor j1 j2))
                  (xor (logbitp i j1) (logbitp i j2))))
  :hints (("Goal" :in-theory (e/d (logbitp EVENP-BECOMES-MOD-FACT oddp)
                                  (LOGBITP-IFF-GETBIT ;fixme why?
                                   MOD-=-0 mod-cancel
                                   ;;for speed:
                                   FLOOR-=-X/Y
                                   floor-bounded-by-/)))))

(defthm logbitp-of-logand
  (implies (and (natp i)
                (integerp j1)
                (integerp j2))
           (equal (logbitp i (logand j1 j2))
                  (and (logbitp i j1) (logbitp i j2))))
  :hints (("Goal" :in-theory (e/d (logbitp EVENP-BECOMES-MOD-FACT oddp)
                                  (LOGBITP-IFF-GETBIT
                                   MOD-=-0 mod-cancel
                                   ;;for speed:
                                   FLOOR-=-X/Y
                                   floor-bounded-by-/)))))

(defthm logbitp-of-logior
  (implies (and (natp i)
                (integerp j1)
                (integerp j2))
           (equal (logbitp i (logior j1 j2))
                  (or (logbitp i j1) (logbitp i j2))))
  :hints (("Goal" :in-theory (e/d (logbitp EVENP-BECOMES-MOD-FACT oddp)
                                  (LOGBITP-IFF-GETBIT
                                   MOD-=-0 mod-cancel
;for speed:
                                   FLOOR-=-X/Y
                                   floor-bounded-by-/)))))

(defthm logxor-of-logapp
  (implies (and (natp n)
                (integerp a)
                (integerp b)
                (integerp c)
                (integerp d))
           (equal (LOGXOR (LOGAPP n A c)
                          (LOGAPP n B d))
                  (logapp n
                          (logxor a b)
                          (logxor c d)
                          ))))

(defthm logand-of-logapp
  (implies (and (natp n)
                (integerp a)
                (integerp b)
                (integerp c)
                (integerp d))
           (equal (LOGAND (LOGAPP n A c)
                          (LOGAPP n B d))
                  (logapp n
                          (logand a b)
                          (logand c d)
                          ))))

(defthm logior-of-logapp
  (implies (and (natp n)
                (integerp a)
                (integerp b)
                (integerp c)
                (integerp d))
           (equal (LOGIOR (LOGAPP n A c)
                          (LOGAPP n B d))
                  (logapp n
                          (logior a b)
                          (logior c d)
                          ))))

(defthm logext-of-logxor
  (implies (and (integerp n)
                (integerp a)
                (integerp b)
                (< 0 n))
           (equal (logext n (logxor a b))
                  (logxor (logext n a)
                          (logext n b))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (logext
                            getbit
                            slice)
                           (BVCHOP-OF-LOGTAIL ;looped
                            BVCHOP-1-BECOMES-GETBIT
                            slice-BECOMES-GETBIT
                            BVCHOP-OF-LOGTAIL-BECOMES-SLICE
                            )))))

(defthm logext-of-logand
  (implies (and (integerp n)
                (integerp a) ;new
                (integerp b) ;new
                (< 0 n))
           (equal (logext n (logand a b))
                  (logand (logext n a)
                          (logext n b))))
  :hints (("Goal" :in-theory (e/d (logext
                                   getbit
                                   slice)
                                  ( ;gen LOGAND-OF-LOGAPP and drop?
                                   LOGAPP-OF-0-ARG3
                                   BVCHOP-1-BECOMES-GETBIT
                                   slice-BECOMES-GETBIT
                                   BVCHOP-OF-LOGTAIL-BECOMES-SLICE
                                   )))))

(defthm logext-of-logior
  (implies (and (integerp n)
                (integerp a)
                (integerp b)
                (< 0 n))
           (equal (logext n (logior a b))
                  (logior (logext n a)
                          (logext n b))))
  :hints (("Goal" :in-theory (e/d (logext getbit slice) (LOGAPP-0
                                                         BVCHOP-1-BECOMES-GETBIT
                                                         slice-BECOMES-GETBIT
                                                         BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

(defthm logext-of-myif
  (equal (logext n (myif test a b))
         (myif test
               (logext n a)
               (logext n b)))
  :hints (("Goal" :in-theory (enable myif)))
  )

;bozo gen
;restrict to only certain applications of logand?
(defthm logand-of-myif
  (equal (binary-logand k (myif test a b))
         (myif test (binary-logand k a)
               (binary-logand k b)))
  :hints (("Goal" :in-theory (enable myif))))

;rewrite
(defthm oddp-of-double
  (implies (integerp x)
           (not (oddp (* 2 x))))
  :hints (("Goal" :in-theory (enable oddp))))

(defthm logbitp-0-of-times-2
  (implies (integerp x)
           (not (LOGBITP 0 (* 2 X))))
  :hints (("Goal" :in-theory (e/d (LOGBITP oddp) (LOGBITP-IFF-GETBIT)))))

(defthm logbitp-of-double
  (implies (and (natp n)
                (integerp x))
           (equal (logbitp n (* 2 x))
                  (if (equal 0 n)
                      nil
                    (logbitp (+ -1 n) x))))
  :hints (("Goal" :in-theory (e/d (logbitp) (LOGBITP-IFF-GETBIT)))))

(defthm logbitp-when-i-is-negative
  (implies (and (< i 0)
                (Integerp i))
           (equal (LOGBITP i j)
                  (LOGBITP 0 j)))
  :hints (("Goal" :in-theory (e/d (logbitp) (LOGBITP-IFF-GETBIT)))))

;used to allow n=1 but untrue for that case?
(defthm logext-shift
  (implies (and (integerp x)
                (natp n)
                (< 1 n))
           (equal (logext n (* 2 x))
                  (* 2 (logext (+ -1 n) x))))
  :hints (("Goal" :in-theory (e/d (logext) (LOGBITP-IFF-GETBIT)))))

(defthm logext-of-logapp
  (implies (and (integerp x)
                (natp k)
                (< 1 k) ;used to allow k=1
                )
           (equal (LOGEXT k (LOGAPP 1 0 x))
                  (logapp 1 0 (logext (+ -1 k) x))))
  :hints (("Goal" :in-theory (enable logapp))))

(defthm oddp-of-times-expt
  (implies (and (natp m)
                (integerp x))
           (equal (oddp (* x (expt 2 m)))
                  (if (equal m 0)
                      (oddp x)
                    nil)))
  :hints (("Goal" :in-theory (enable oddp))))

(defthm logbitp-of-shift
  (implies (and (natp n)
                (natp m)
                (<= m n)
                (integerp x))
           (equal (logbitp n (* (expt 2 m) x))
                  (if (equal 0 n)
                      (logbitp 0 x)
                    (logbitp (- n m) x))))
  :hints (("Goal" :in-theory (e/d (logbitp floor oddp expt-of-+) (LOGBITP-IFF-GETBIT)))))

;(local (in-theory (disable hack-6))) ;bozo

;move?
(defthm signed-byte-p-longer
  (implies (and (signed-byte-p free i)
                (<= free size)
                (integerp size)
                (natp free))
           (signed-byte-p size i))
  :hints (("Goal"
;           :use (:instance EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1 (r 2) (i (+ -1 free)) (j (+ -1 size)))
           :in-theory (e/d (signed-byte-p) (;EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1
                                            ;<-OF-EXPT-AND-EXPT
                                            )))))

;; (skip -proofs
;;  (defthm sbp-longer
;;    (implies (and (signed-byte-p free x)
;;                  (natp free)
;;                  (natp n)
;;                  (<= free n))
;;             (signed-byte-p n x))
;;    :hints (("Goal" :in-theory (e/d () ( ;integer-range-p
;;                                                     hack-6))))))

(defthm logext-identity2
  (implies (and (signed-byte-p free i)
                (>= size free)
                (natp size)
                (natp free))
           (equal (logext size i)
                  i))
;   :hints (("Goal" :induct (sub1-logcdr-induction-1 size i)))
  :hints (("Goal" :use (:instance logext-identity)
           :in-theory (e/d ( ;signed-byte-p
                            ) (logext-identity)))))

;bozo consider < vs. <= each time here
(defthm logext32-drop-from-constant-bounds-<=-and-<=
  (implies (and (<= x freeupper)
                (syntaxp (quotep freeupper))
                (< (+ freeupper k) (expt 2 31))
                (<= freelower x)
                (syntaxp (quotep freelower))
                (< (- (expt 2 31)) (+ freelower k))
                (integerp x)
                (integerp k))
           (equal (LOGEXT 32 (+ k x))
                  (+ k x)))
  :hints (("Goal" :in-theory (enable SIGNED-BYTE-P))))


(defthm logext32-drop-from-constant-bounds-<=-and-<
  (implies (and (< x freeupper)
                (syntaxp (quotep freeupper))
                (< (+ freeupper k) (expt 2 31))
                (<= freelower x)
                (syntaxp (quotep freelower))
                (<= (- (expt 2 31)) (+ freelower k))
                (integerp x)
                (integerp k))
           (equal (LOGEXT 32 (+ k x))
                  (+ k x)))
  :hints (("Goal" :in-theory (enable SIGNED-BYTE-P))))

(defthm sbp32-drop-from-constant-bounds-<=-and-<=
  (implies (and (<= x freeupper)
                (syntaxp (quotep freeupper))
                (< (+ freeupper k) (expt 2 31))
                (<= freelower x)
                (syntaxp (quotep freelower))
                (< (- (expt 2 31)) (+ freelower k))
                (integerp x)
                (integerp k))
           (signed-byte-p 32 (+ k x)))
  :hints (("Goal" :in-theory (enable SIGNED-BYTE-P))))

(defthm sbp32-drop-from-constant-bounds-<=-and-<
  (implies (and (< x freeupper)
                (syntaxp (quotep freeupper))
                (< (+ freeupper k) (expt 2 31))
                (<= freelower x)
                (syntaxp (quotep freelower))
                (<= (- (expt 2 31)) (+ freelower k))
                (integerp x)
                (integerp k))
           (signed-byte-p 32 (+ k x)))
  :hints (("Goal" :in-theory (enable SIGNED-BYTE-P))))

(defthm oddp=sum-with-evenp-reduce
   (implies (and (evenp i)
                 (integerp i)
                 (integerp j))
            (equal (oddp (+ i j))
                   (oddp j)))
   :hints (("Goal" :in-theory (enable oddp))))





;bozo gen
(defthm logext-31-drop
 (implies (and (<= (- (expt 2 30)) x)
               (< x (expt 2 30))
               (integerp x))
          (equal (LOGEXT 31 x)
                 x))
 :rule-classes ((:rewrite :backchain-limit-lst (1 1 nil)))
 :hints (("Goal" :in-theory (enable SIGNED-BYTE-P))))


(defthm getbit-of-logext
  (implies (and (< n size)
                (integerp size)
                (< 0 size)
                (natp n))
           (equal (getbit n (logext size x))
                  (getbit n x)))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (e/d (getbit slice BVCHOP-OF-LOGTAIL)
                           (SLICE-BECOMES-GETBIT ;LOGTAIL-BVCHOP
                                               BVCHOP-1-BECOMES-GETBIT
                                               BVCHOP-OF-LOGTAIL-BECOMES-SLICE
;BVCHOP-OF-LOGTAIL
                                               )))))

(defthm getbit-of-bvif
  (implies (and (< n size)
                (natp n)
                (integerp size))
           (equal (getbit n (bvif size test x1 x2))
                  (bvif 1 test (getbit n x1) (getbit n x2))))
  :hints (("Goal" :in-theory (enable bvif myif))))



;; (defthmd equal-hack
;;   (implies (and (equal free1 free2)
;;                 (equal (logext newsize free1) (logext newsize x))
;;                 (equal (logext newsize free2) (logext newsize y))
;;                 (posp newsize)
;;                 )
;;            (equal (equal (logext newsize x) (logext newsize y))
;;                   t)))

(defthm logext-hack
  (implies (and (equal (bvchop newsize x)
                       y)
                (syntaxp (smaller-termp (caddr y) x)) ;gross
                (integerp x)
                (posp newsize)
                )
           (equal (logext newsize x)
                  (logext newsize y)))

  :hints (("Goal" :in-theory (e/d ( logext) (logext-identity logext-identity2)))))

(defthmd helper-lemm
  (IMPLIES (AND (INTEGERP NEWSIZE)
                (< 0 NEWSIZE)
                (INTEGERP X)
                (SIGNED-BYTE-P NEWSIZE Y)
                (EQUAL (BVCHOP NEWSIZE X)
                       (BVCHOP NEWSIZE Y)))
           (EQUAL (LOGEXT NEWSIZE X) (logext newsize y)))
  :hints (("Goal" ;:use (:instance logext-hack (y (BVCHOP NEWSIZE Y)))
           :in-theory (e/d (logext-hack) (LOGEXT-IDENTITY LOGEXT-IDENTITY2)))))

;this gets in the way of substituting...
(defthmd add-bvchops-to-equality-of-sbps-4
  (implies (and ; (bind-free (bind-newsize-to-termsize x) (newsize))
            (integerp newsize)
            (< 0 newsize)
; (integerp x)
            (signed-byte-p newsize y)
            )
           (equal (equal (logext newsize x) y)
                  (if (integerp x)
                      (equal (bvchop newsize x) (bvchop newsize y))
                    (equal 0 y))))
  :hints (("Goal"
           :use (:instance helper-lemm)
           :in-theory (enable ;smyif
                       ))))

(defthmd add-bvchops-to-equality-of-sbps-4-alt
  (implies (and ; (bind-free (bind-newsize-to-termsize x) (newsize))
            (integerp newsize)
            (< 0 newsize)
            (signed-byte-p newsize y)
            )
           (equal (equal y (logext newsize x))
                  (if (integerp x)
                      (equal (bvchop newsize x) (bvchop newsize y))
                    (equal 0 y))))
  :hints (("Goal" :use (:instance add-bvchops-to-equality-of-sbps-4)
           :in-theory (disable add-bvchops-to-equality-of-sbps-4))))

;; ;get rid of these?
;; (defconst *signed-operators*
;;   '(;smyif
;;     logext slogxor ;;slogand
;;           slogior ;slognot ;slice
;;           slogapp s-bit ;bool-to-bit
;;           ))

;; ;watch out for loops!
;; (defthmd add-bvchop-to-bvand-2
;;   (implies (and (syntaxp (and (not (quotep y))
;;                               (not (member-equal (car y) (append *trimmable-operators*
;;                                                                   *signed-operators*)))))
;;                 (natp size)
;;                 (integerp x)
;;                 (integerp y)
;;                 )
;;            (equal (bvand size x y)
;;                   (bvand size x (bvchop size y))))
;;   :hints (("Goal" :in-theory (enable bvand))))

;; (defthmd add-bvchop-to-bvand-1
;;   (implies (and (syntaxp (and (not (quotep y))
;;                               (not (member-equal (car y) (append *trimmable-operators*
;;                                                                   *signed-operators*)))))
;;                 (natp size)
;;                 (integerp x)
;;                 (integerp y)
;;                 )
;;            (equal (bvand size y x)
;;                   (bvand size (bvchop size y) x)))
;;   :hints (("Goal" :in-theory (enable bvand))))

;; (defthmd add-bvchop-to-bvxor-2
;;   (implies (and (syntaxp (and (not (quotep y))
;;                               (not (member-equal (car y) (append *trimmable-operators*
;;                                                                   *signed-operators*)))))
;;                 (natp size)
;;                 (integerp x)
;;                 (integerp y)
;;                 )
;;            (equal (bvxor size x y)
;;                   (bvxor size x (bvchop size y))))
;;   :hints (("Goal" :in-theory (e/d (bvxor) ()))))

;; (defthmd add-bvchop-to-bvxor-1
;;   (implies (and (syntaxp (and (not (quotep y))
;;                               (not (member-equal (car y) (append *trimmable-operators*
;;                                                                   *signed-operators*)))))
;;                 (natp size)
;;                 (integerp x)
;;                 (integerp y)
;;                 )
;;            (equal (bvxor size y x)
;;                   (bvxor size (bvchop size y) x)))
;;   :hints (("Goal" :in-theory (e/d (bvxor) ()))))

(in-theory (enable BVCHOP-OF-LOGTAIL)) ;fixme why?

;rename
(defthm slice-of-logext
  (implies (and (< highbit n)
                (posp n)
                (natp lowbit)
                (integerp highbit))
           (equal (slice highbit lowbit (logext n x))
                  (slice highbit lowbit x)))
  :hints (("Goal" :expand (slice highbit lowbit x)
           :cases ((and (integerp x) (<= lowbit highbit))
                   (and (integerp x) (> lowbit highbit)))
           :in-theory (e/d (slice) (bvchop-of-logtail-becomes-slice
                                    logtail-of-bvchop-becomes-slice)))))

(defthm bvxor-of-bvchop-hack6
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (bvxor 5 x (+ (bvchop 32 y) z))
                  (bvxor 5 x (+ y z))))
  :hints (("Goal" :in-theory (enable bvxor))))

(defthm bvxor-of-bvchop-hack6b
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (bvxor 5 (+ (bvchop 32 y) z) x)
                  (bvxor 5 x (+ y z))))
  :hints (("Goal" :in-theory (enable bvxor))))

(defthm slice-of-bvchop-hack6
  (implies (and (integerp y)
                (integerp z))
           (equal (slice 31 5 (+ (bvchop 32 y) z))
                  (slice 31 5 (+ y z))))
  :hints (("Goal" :in-theory (e/d (slice) (bvchop-of-logtail-becomes-slice
                                           LOGTAIL-EQUAL-0)))))

(defthm slice-of-bvchop-hack6b
  (implies (and (integerp y)
                (integerp z))
           (equal (slice 31 5 (+ z (bvchop 32 y)))
                  (slice 31 5 (+ y z))))
  :hints (("Goal" :in-theory (e/d (slice) (bvchop-of-logtail-becomes-slice
                                           LOGTAIL-EQUAL-0)))))

(defthm slice-of-sum-drop-bvchop
  (implies (and (< high size)
                (natp size)
                (natp low)
                (<= low high)
                (natp high)
                (integerp y)
                (integerp z))
           (equal (slice high low (+ (bvchop size y) z))
                  (slice high low (+ y z))))
  :hints (("Goal" :in-theory (e/d (slice) (bvchop-of-logtail-becomes-slice)))))

(defthm slice-of-sum-drop-bvchop-alt
  (implies (and (< high size)
                (natp size)
                (natp low)
                (<= low high)
                (natp high)
                (integerp y)
                (integerp z))
           (equal (slice high low (+ z (bvchop size y)))
                  (slice high low (+ y z))))
  :hints (("Goal" :in-theory (e/d (slice) (bvchop-of-logtail-becomes-slice)))))

;make a general theory of cancellation for associative and commutative functions with an inverse and identity
;i guess you get left and right cancellation (but not more general cancellation) for non-abelian groups.

;bozo gen the size..
;needed for DES proof
;use a subst rule instead?
;yuck?
(defthm bvxor-cancel-special
  (implies (equal (getbit 0 x)
                  (getbit 0 w))
           (equal (equal (bvxor 1 x y) (bvxor 1 w z))
                  (equal (bvchop 1 y) (bvchop 1 z))))
  :hints (("Goal" :use ((:instance bvxor-1-of-getbit-arg1)
                        (:instance bvxor-1-of-getbit-arg1 (x w) (y z))
                        (:instance bvxor-cancel
                                   (x (getbit 0 x))
                                   (y y)
                                   (z z)
                                   (size 1)
                                   ))
           :in-theory (disable bvxor-cancel-cross-2 bvxor-cancel-alt ;bvxor-usb1-cancel
                               bvxor-cancel
                               bvxor-1-becomes-bitxor
                               bvxor-1-of-getbit-arg1 bvxor-1-of-getbit-arg2 bvxor-commutative ;bvxor-commutative
                               ))))

;gen?! expand range for x at all?
(defthm logext-times-4-hack
  (implies (and (< x (/ (expt 2 31) 4))
                (natp x))
           (equal (logext 32 (* 4 x))
                  (* 4 x)))
  :hints (("Goal" :in-theory (enable signed-byte-p unsigned-byte-p))))

(defthm logext-of-logapp-gen
  (implies (and (integerp x)
                (natp n)
                (natp m)
                (< m n)
                (integerp v))
           (equal (logext n (logapp m v x))
                  (logapp m v (logext (- n m) x))))
  :hints (("Goal" :in-theory (e/d ( ;logapp
                                   slice
                                   ;logtail-bvchop
                                   logext) (bvchop-of-logtail
                                            logbitp-iff-getbit ;why - need getbit of logapp
                                            bvchop-of-logtail-becomes-slice)))))

(defthmd bozohack
  (implies (signed-byte-p 8 x)
           (equal (logext 24 x)
                  x)))

;fixme consider "pick a bit" proofs?

;fixme copy all bitxor thms for bitand and bitor

;am i sure i want this?
(defthm bvif-of-getbit-arg1
  (equal (bvif 1 test (getbit 0 x) y)
         (bvif 1 test x y))
  :hints (("Goal" :in-theory (enable bvif))))

;am i sure i want this?
(defthm bvif-of-getbit-arg2
  (equal (bvif 1 test x (getbit 0 y))
         (bvif 1 test x y))
  :hints (("Goal" :in-theory (enable bvif))))

;bbozo gen and add
(defthmd 0-1-split
  (implies (and (not (< 1 x))
                (integerp x))
           (equal (< x 0)
                  (and (not (equal x 0))
                       (not (equal x 1))))))

;trying disabled
(defthmd 0-1-split-cheap
  (implies (and (not (< 1 x))
                (integerp x))
           (equal (< x 0)
                  (and (not (equal x 0))
                       (not (equal x 1)))))
  :rule-classes ((:rewrite :backchain-limit-lst (1 1))))

(defthm integer-squeeze-0-1
  (implies (and (integerp x)
                (<= 0 x)
                (< x 1))
           (equal x 0))
  :rule-classes nil)

(defthm mod-hack-lemma1023242
  (implies (and (integerp x)
                (natp m)
                (< 0 m)
                )
           (equal (integerp (* (/ m) (mod x m)))
                  (equal (mod x m)
                         0)))
  :hints (("Goal" :in-theory (disable |0-1-SPLIT-CHEAP|)
           :use (:instance integer-squeeze-0-1 (x  (* (/ m)
                                                      (mod x m)))))))


(defthm slice-of-bvxor
  (implies (and (< highbit size)
;                (<= lowbit highbit)
                (integerp size)
                (<= 0 size)
                (natp lowbit)
                (natp highbit)
                )
           (equal (slice highbit lowbit (bvxor size x y))
                  (bvxor (+ 1 highbit (- lowbit))
                         (slice highbit lowbit x)
                         (slice highbit lowbit y))))
  :hints (("Goal"
           :cases ((and (integerp x) (integerp y))
                   (and (integerp x) (not (integerp y)))
                   (and (not (integerp x)) (integerp y))
                   )
           :in-theory (e/d (slice bvxor natp) (BVCHOP-OF-LOGTAIL-BECOMES-SLICE
                                               LOGTAIL-OF-BVCHOP-BECOMES-SLICE)))))



(defthm bvchop-bvchop-8-32-hack
  (implies (and (integerp x)
                (integerp y))
           (equal (BVCHOP 8 (+ (BVCHOP 32 y) x))
                  (BVCHOP 8 (+ y x)))))

;fixme
(defthm gross-helper2
  (implies (and (equal (bvchop 32 x)
                       (bvchop 32 y))
                (natp k))
           (equal (equal (slice 15 k x)
                         (slice 15 k y))
                  t))
  :hints (("Goal" :use ((:instance SLICE-OF-BVCHOP-LOW (X X) (N 32) (LOW K) (HIGH 15))
                        (:instance SLICE-OF-BVCHOP-LOW (X y) (N 32) (LOW K) (HIGH 15)))
           :in-theory (disable SLICE-OF-BVCHOP-LOW SLICE-OF-BVCHOP-LOW-GEN))))

(defthm slice-bvchop-8-32-hack
  (implies (and (integerp x)
                (integerp y))
           (equal (slice 15 8 (+ (BVCHOP 32 y) x))
                  (slice 15 8 (+ y x)))))

(defthm gross-helper3
  (implies (and (equal (bvchop 32 x)
                       (bvchop 32 y))
                (natp k))
           (equal (equal (slice 23 k x)
                         (slice 23 k y))
                  t))
  :hints (("Goal" :use ((:instance SLICE-OF-BVCHOP-LOW (X X) (N 32) (LOW K) (HIGH 23))
                        (:instance SLICE-OF-BVCHOP-LOW (X y) (N 32) (LOW K) (HIGH 23)))
           :in-theory (disable SLICE-OF-BVCHOP-LOW SLICE-OF-BVCHOP-LOW-GEN))))


(defthm slice-bvchop-23-16-32-hack
  (implies (and (integerp x)
                (integerp y))
           (equal (slice 23 16 (+ (BVCHOP 32 y) x))
                  (slice 23 16 (+ y x)))))

(defthm gross-helper4
  (implies (and (equal (bvchop 32 x)
                       (bvchop 32 y))
                (natp k))
           (equal (equal (slice 31 k x)
                         (slice 31 k y))
                  t))
  :hints (("Goal" :use ((:instance SLICE-OF-BVCHOP-LOW (X X) (N 32) (LOW K) (HIGH 31))
                        (:instance SLICE-OF-BVCHOP-LOW (X y) (N 32) (LOW K) (HIGH 31)))
           :in-theory (disable SLICE-OF-BVCHOP-LOW SLICE-OF-BVCHOP-LOW-GEN))))

(defthm slice-bvchop-31-24-32-hack
  (implies (and (integerp x)
                (integerp y))
           (equal (slice 31 24 (+ (BVCHOP 32 y) x))
                  (slice 31 24 (+ y x)))))

(defthm bitand-of-bvcat-arg1
   (implies (and (< 0 lowsize)
                 (integerp lowsize)
                 (natp highsize))
            (equal (BITAND (BVCAT highsize highval lowsize lowval)
                           x)
                   (BITAND lowval
                           x)))
   :hints (("Goal" :in-theory (e/d (BITAND bvand) (BVAND-1-BECOMES-BITAND
                                                   BVCHOP-OF-BVCAT-CASES-GEN)))))

(defthm bitand-of-bvcat-arg2
   (implies (and (< 0 lowsize)
                 (integerp lowsize)
                 (natp highsize))
            (equal (BITAND x
                           (BVCAT highsize highval lowsize lowval))
                   (BITAND x
                           lowval)))
   :hints (("Goal" :in-theory (e/d (BITAND bvand) (BVAND-1-BECOMES-BITAND)))))

(defthm bvplus-of-bvcat-irrel-arg2
  (implies (and (<= size2 size)
                (natp size2)
                (integerp size)
                )
           (equal (bvplus size2 x (bvcat n z size y))
                  (bvplus size2 x y)))
  :hints (("Goal"
           :use ((:instance bvplus-of-bvchop-arg2
                           (size size2)
                           (x x)
                           (y (bvcat n z size y)))
                 (:instance bvplus-of-bvchop-arg2
                           (size size2)
                           (x x)
                           (y y)))
           :in-theory (disable bvplus-of-bvchop-arg2))))

(defthm bvplus-of-bvcat-irrel-arg1
  (implies (and (<= size2 size)
                (natp size2)
                (integerp size))
           (equal (bvplus size2 (bvcat n z size y) x)
                  (bvplus size2 y x)))
  :hints (("Goal" :use (:instance bvplus-of-bvcat-irrel-arg2)
           :in-theory (disable bvplus-of-bvcat-irrel-arg2))))

(defthm bvif-equal-0-usb1
  (implies (unsigned-byte-p 1 x)
           (equal (bvif 1 (equal 0 x) 1 0)
                  (bvnot 1 x)))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm bvif-equal-0-usb1-2
  (implies (unsigned-byte-p 1 x)
           (equal (bvif 1 (equal 0 x) 0 1)
                  x))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm bvif-equal-1-usb1
  (implies (unsigned-byte-p 1 x)
           (equal (bvif 1 (equal 1 x) 1 0)
                  (getbit 0 x)))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm bvif-equal-1-usb1-2
  (implies (unsigned-byte-p 1 x)
           (equal (bvif 1 (equal 1 x) 0 1)
                  (bvnot 1 x)))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm bvxor-of-bvand-tighten-alt
  (implies (and (< size1 size2)
                (integerp z)
                (natp size1)
                (natp size2))
           (equal (bvxor size1 z (bvand size2 x y))
                  (bvxor size1 z (bvand size1 x y))))
  :hints (("Goal" :in-theory (enable bvxor))))

(defthm bvand-of-bvxor-tighten
  (implies (and (< size1 size2)
                (integerp z)
                (natp size1)
                (natp size2))
           (equal (bvand size1 (bvxor size2 x y) z)
                  (bvand size1 (bvxor size1 x y) z)))
  :hints (("Goal" :in-theory (enable bvxor bvand))))

(defthm bvand-of-bvxor-tighten-alt
  (implies (and (< size1 size2)
                (integerp z)
                (natp size1)
                (natp size2))
           (equal (bvand size1 z (bvxor size2 x y))
                  (bvand size1 z (bvxor size1 x y))))
  :hints (("Goal" :in-theory (enable bvxor bvand))))

(defthm integerp-when-unsigned-byte-p-free
  (implies (unsigned-byte-p free x) ;FREE is a free var., so this rule should be cheap
           (integerp x)))

;fixme LOGTAIL-WHEN-I-IS-NOT-AN-INTEGER and LOGTAIL-WHEN-VAL-IS-NOT-AN-INTEGER

;drop this one eventually (or at least move it from the logext book):
(in-theory (disable bvchop-of-logtail))

;move
(defthm logtail-of-logapp-gen
  (implies (and (<= n lowsize) ;other case?
                (integerp lowsize)
                (natp n))
           (equal (logtail n (logapp lowsize x y))
                  (if (natp lowsize)
                      (logapp (- lowsize n) (logtail n x) y)
                    (logtail n (ifix y)))))
  :hints
  (("Goal"
    :use (:instance logtail-logapp (size n) (size1 lowsize) (i x) (j y))
    :in-theory (e/d (bvchop-of-logtail)
                    (LOGTAIL-SHIFT-GEN2-ALT
                     ;LOGAPP-0-NEW2
                     BVCHOP-OF-LOGTAIL-BECOMES-SLICE
                     LOGTAIL-OF-BVCHOP-BECOMES-SLICE
                     logtail-logapp)))))

(DEFTHM LOGBITP-LOGTAIL-better
  (IMPLIES (AND (INTEGERP POS)
                (NOT (< POS '0))
;               (INTEGERP I)
                (INTEGERP POS1)
                (>= POS1 0)
                )
           (EQUAL (LOGBITP POS1 (LOGTAIL POS I))
                  (LOGBITP (+ POS POS1) I)))
  :hints (("Goal" :use (:instance LOGBITP-LOGTAIL)
           :in-theory (disable LOGBITP-LOGTAIL))))

(local (in-theory (disable LOGBITP-LOGTAIL))) ;not exported by this book

(local (in-theory (enable bvchop-of-logtail)))

(DEFTHMd logatil-OF-LOGEXT-GEN
  (IMPLIES (AND (< N M) ;not true if =?
                ;;(INTEGERP X)
                (NATP N)
                (natp m))
           (EQUAL (logtail N (LOGEXT M X))
                  (LOGEXT (- M N) (logtail N X))))
  :HINTS (("Goal" :IN-THEORY (E/d (slice
                                   posp
                                   LOGEXT)
                                  (logtail-logapp LOGBITP-LOGTAIL
                                                  BVCHOP-OF-LOGTAIL-BECOMES-SLICE
                                                  LOGBITP-IFF-GETBIT
                                                  )))))

;use trim
(defthm bvmult-of-bvand-tighten-2
  (implies (and (< size size2)
                (natp size)
                (natp size2)
                (integerp z)
                (integerp x))
           (equal (BVMULT size z (BVAND size2 x y))
                  (BVMULT size z (BVAND size x y))))
  :hints (("Goal" :use (:instance bvmult-of-bvchop-arg3
                                  (x z)
                                  (y (BVAND size2 x y)))
           :in-theory (disable bvmult-of-bvchop-arg3))))

;use trim
(defthm bvmult-of-bvand-tighten-1
  (implies (and (< size size2)
                (natp size)
                (natp size2)
                (integerp z)
                (integerp x))
           (equal (BVMULT size (BVAND size2 x y) z)
                  (BVMULT size (BVAND size x y) z)))
  :hints (("Goal" :use (:instance bvmult-of-bvchop-arg3
                                  (x z)
                                  (y (BVAND size2 x y)))
           :in-theory (disable bvmult-of-bvchop-arg3 BVMULT-OF-BVAND-TIGHTEN-2))))

;use trim
(defthm bvmult-of-bvxor-tighten-2
  (implies (and (< size size2)
                (natp size)
                (natp size2)
                (integerp y)
                (integerp z)
                (integerp x))
           (equal (BVMULT size z (BVXOR size2 x y))
                  (BVMULT size z (BVXOR size x y))))
  :hints (("Goal" :use (:instance bvmult-of-bvchop-arg3
                                  (x z)
                                  (y (BVXOR size2 x y)))
           :in-theory (disable bvmult-of-bvchop-arg3))))

;use trim
(defthm bvmult-of-bvxor-tighten-1
  (implies (and (< size size2)
                (natp size)
                (natp size2)
                (integerp z)
                (integerp y)
                (integerp x))
           (equal (BVMULT size (BVXOR size2 x y) z)
                  (BVMULT size (BVXOR size x y) z)))
  :hints (("Goal" :use (:instance bvmult-of-bvchop-arg3
                                  (x z)
                                  (y (BVXOR size2 x y)))
           :in-theory (disable bvmult-of-bvchop-arg3 BVMULT-OF-BVXOR-TIGHTEN-2))))

;use trim
(defthm bvmult-of-bvor-tighten-2
  (implies (and (< size size2)
                (natp size)
                (natp size2)
                (integerp y)
                (integerp z)
                (integerp x))
           (equal (BVMULT size z (BVOR size2 x y))
                  (BVMULT size z (BVOR size x y))))
  :hints (("Goal" :use (:instance bvmult-of-bvchop-arg3
                                  (x z)
                                  (y (BVOR size2 x y)))
           :in-theory (disable bvmult-of-bvchop-arg3))))

;use trim
(defthm bvmult-of-bvor-tighten-1
  (implies (and (< size size2)
                (natp size)
                (natp size2)
                (integerp z)
                (integerp y)
                (integerp x))
           (equal (BVMULT size (BVOR size2 x y) z)
                  (BVMULT size (BVOR size x y) z)))
  :hints (("Goal" :use (:instance bvmult-of-bvchop-arg3
                                  (x z)
                                  (y (BVOR size2 x y)))
           :in-theory (disable bvmult-of-bvchop-arg3 BVMULT-OF-BVOR-TIGHTEN-2))))

;use trim
(defthm bvmult-of-bvcat-irrel-arg2
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


;use trim
(defthm bvmult-of-bvcat-irrel-arg1
  (implies (and (<= size2 size)
                (natp size2)
                (natp n)
                (integerp size))
           (equal (bvmult size2 (bvcat n z size y) x)
                  (bvmult size2 y x)))
  :hints (("Goal"
           :use (:instance bvmult-of-bvcat-irrel-arg2)
           :in-theory (disable bvmult-of-bvcat-irrel-arg2))))

;bozo simplify the rhs?
(defthm bvmult-of-bvcat-trim-arg1
  (implies (and (< size (+ highsize lowsize))
                (natp size))
           (equal (bvmult size (bvcat highsize highval lowsize lowval) x)
                  (bvmult size (bvchop size (bvcat highsize highval lowsize lowval)) x)))
  :hints (("Goal"
           :use (:instance BVMULT-OF-BVCHOP-arg2
                           (size size)
                           (x (bvcat highsize highval lowsize lowval))
                           (y x))
           :in-theory (e/d ( ;bvmult
                            ) (BVMULT-OF-BVCHOP-arg2)))))

;bozo simplify the rhs?
(defthm bvmult-of-bvcat-trim-arg2
  (implies (and (< size (+ highsize lowsize))
                (natp size))
           (equal (bvmult size x (bvcat highsize highval lowsize lowval))
                  (bvmult size x (bvchop size (bvcat highsize highval lowsize lowval)))))
  :hints (("Goal"
           :use (:instance BVMULT-OF-BVCHOP-arg2
                           (size size)
                           (x (bvcat highsize highval lowsize lowval))
                           (y x))
           :in-theory (e/d ( ;bvmult
                            ) (BVMULT-OF-BVCHOP-arg2)))))

(defthm bvchop-of-bvminus
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2))
           (equal (bvchop size1 (bvminus size2 y z))
                  (bvminus size1 y z)))
  :hints (("Goal" :in-theory (enable bvminus ;bvchop-bvchop
                                   ))))

(defthm bvplus-bound-2
  (implies (and (<= (expt 2 size) k)
                (natp size))
           (< (bvplus size x y) k))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-bvplus (n size) (m size))
           :in-theory (disable unsigned-byte-p-of-bvplus))))

(defthm bvchop-bound-2
  (implies (and (<= (expt 2 size) k)
                (natp size))
           (< (bvchop size x) k)))

;fixme
(defthmd logxor-logapp-24
  (equal (logxor x (logapp 24 y z))
         (logapp 24
                 (logxor x y)
                 (logxor (logtail 24 x) z))))

(defthmd logxor-logapp-16
  (equal (logxor x (logapp 16 y z))
         (logapp 16
                 (logxor x y)
                 (logxor (logtail 16 x) z))))

(defthmd logxor-logapp-8
  (equal (logxor x (logapp 8 y z))
         (logapp 8
                 (logxor x y)
                 (logxor (logtail 8 x) z))))

(defthm logtail-logapp-24-8
   (implies (and (integerp x)
                 (integerp y))
            (equal (logtail 8 (logapp 24 x y))
                   (logapp 16 (logtail 8 x) y))))

(defthm logtail-logapp-16-8
   (implies (and (integerp x)
                 (integerp y))
            (equal (logtail 8 (logapp 16 x y))
                   (logapp 8 (logtail 8 x) y))))

(defthm logtail-logapp-24-16
   (implies (and (integerp x)
                 (integerp y))
            (equal (logtail 16 (logapp 24 x y))
                   (logapp 8 (logtail 16 x) y))))

(defthm logapp-equal-rewrite-24
   (equal (equal (logapp 24 x y) z)
          (and (integerp z)
               (equal (bvchop 24 z)
                      (bvchop 24 x))
               (equal (ifix y) (logtail 24 z)))))

(defthm logapp-equal-rewrite-16
   (equal (equal (logapp 16 x y) z)
          (and (integerp z)
               (equal (bvchop 16 z)
                      (bvchop 16 x))
               (equal (ifix y) (logtail 16 z)))))

(defthm logapp-equal-rewrite-8
   (equal (equal (logapp 8 x y) z)
          (and (integerp z)
               (equal (bvchop 8 z)
                      (bvchop 8 x))
               (equal (ifix y) (logtail 8 z)))))

(defthm <-of-minus-x-and-x
  (implies (rationalp x)
           (equal (< (- x) x)
                  (< 0 x)))
  :hints (("Goal" :cases ((equal x 0)(< x 0)))))

(defthm ubp8-logtail16
   (equal (unsigned-byte-p 8 (logtail 16 x))
          (or (not (integerp x))
              (unsigned-byte-p 24 x))))


(defthm ubp8-logtail24
  (equal (unsigned-byte-p 8 (logtail 24 x))
         (or (not (integerp x))
             (unsigned-byte-p 32 x))))

(defthm ubp8-logtail8
  (equal (unsigned-byte-p 8 (logtail 8 x))
         (or (not (integerp x))
             (unsigned-byte-p 16 x))))

(defthm logtail-of-logapp-8-24
   (equal (logtail 24 (logapp 8 v x))
          (logtail 16 x)))

(defthm logtail-of-logapp-16-24
   (equal (logtail 24 (LOGAPP 16 v x))
          (logtail 8 x)))

(defthm logtail-of-logapp-8-16
   (equal (logtail 16 (LOGAPP 8 v x))
          (logtail 8 x)))

(defthm shift-compare-hack
   (< (logtail '8
               (BVCHOP 16 x))
      '256)
   :hints (("Goal" :in-theory (disable LOGTAIL-OF-BVCHOP-BECOMES-SLICE))))

(defthm shift-compare-hack-24-16
   (< (logtail 16
               (BVCHOP 24 x))
      256)
      :hints (("Goal" :in-theory (disable LOGTAIL-OF-BVCHOP-BECOMES-SLICE))))

;; ;deprecating in favor of power-of-2p
;; (defun pow2p (x)
;;   (equal x (expt 2 (+ -1 (integer-length x)))))

(DEFTHM LOGBITP-OF-SHIFT-constant-version
  (IMPLIES (AND (syntaxp (quotep k))
                (power-of-2p k)
                (NATP N)
                (NATP (+ -1 (integer-length k)))
                (<= (+ -1 (integer-length k)) N)
                (INTEGERP X))
           (EQUAL (LOGBITP N (* k X))
                  (IF (EQUAL 0 N)
                      (LOGBITP 0 X)
                      (LOGBITP (- N (+ -1 (integer-length k))) X))))
  :hints (("Goal" :use (:instance LOGBITP-OF-SHIFT (m (+ -1 (integer-length k))))
           :in-theory (e/d (power-of-2p) ( LOGBITP-OF-SHIFT)))))

;bozo gen
(defthm logext-of-logapp-2
   (implies (and (integerp x)
                 (natp k)
                 (< 2 k) ;was (< 0 k)
                 )
            (equal (LOGEXT k (LOGAPP 2 0 x))
                   (logapp 2 0 (logext (+ -2 k) x))))
   :hints (("Goal"
            :use (:instance INTEGERP-OF-EXPT-when-natp (r 2) (i (- k 3)))
            :in-theory (e/d (logext logapp
                                    ;expt-hack
                                    EXPT-OF-+)
                            (LOGBITP-IFF-GETBIT INTEGERP-OF-EXPT-when-natp)))))

(defthm bvor-of-slice-tighten
   (implies (and (<= size (- high low))
                 (natp size)
                 (< 0 size)
                 (natp low)
                 (natp high)
                 (integerp x)
                 (integerp y)
                 )
            (equal (bvor size x (slice high low y))
                   (bvor size x (slice (+ low size -1) low y))))
   :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-of-slice-tighten-alt
   (implies (and (<= size (- high low))
                 (natp size)
                 (< 0 size)
                 (natp low)
                 (natp high)
                 (integerp x)
                 (integerp y)
                 )
            (equal (bvor size (slice high low y) x)
                   (bvor size (slice (+ low size -1) low y) x)))
   :hints (("Goal" :in-theory (enable bvor))))

(defthm bvcat-of-logext-same
   (implies (and (natp size)
                 (< 0 size)
;               (equal 8 size)
                 (integerp x))
            (equal (bvcat highsize y size (logext size x))
                   (bvcat highsize y size x)))
   :hints (("Goal" :in-theory (e/d (bvcat ;bvchop-logapp
                                    ) ()))))

(defthm logapp-of-logext
   (implies (and (natp size2)
                 (integerp x)
                 (integerp y))
            (equal (logapp size2 (logext size2 x) y)
                   (logapp size2 x y))))

(defthm bvor-of-slice-tighten-2
  (implies (and (< size (+ 1 high (- low)))
                (< 0 size)
                (natp size)
                (natp low)
                (natp high)
                (integerp x)
                (integerp y))
           (equal (bvor size y (slice high low x))
                  (bvor size y (slice (+ low size -1) low x))))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-of-slice-tighten-1
   (implies (and (< size (+ 1 high (- low)))
                 (< 0 size)
                 (natp size)
                 (natp low)
                 (natp high)
                 (integerp x)
                 (integerp y))
            (equal (bvor size (slice high low x) y)
                   (bvor size (slice (+ low size -1) low x) y)))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvchop-of-minus-of-bvchop-gen
  (implies (and (<= size size2)
                (integerp size2)
                )
           (equal (bvchop size (- (bvchop size2 x)))
                  (bvchop size (- x))))
  :hints (("Goal" :use ((:instance bvchop-of-minus-of-bvchop (x x))
                        (:instance bvchop-of-minus-of-bvchop (x (bvchop size2 x))))
           :in-theory (disable bvchop-of-minus-of-bvchop))))

(defthm bvchop-of-minus-of-logext-gen
  (implies (and (<= size size2)
                (natp size2)
                (natp size))
           (equal (bvchop size (- (logext size2 x)))
                  (bvchop size (- x))))
  :hints (("Goal" :use ((:instance bvchop-of-minus-of-bvchop (x x))
                        (:instance bvchop-of-minus-of-bvchop (x (logext size2 x))))
           :in-theory (disable bvchop-of-minus-of-bvchop))))



(defthm bvchop-bound-other
  (implies (and (syntaxp (and (quotep k) (quotep n)))
                (integerp k)
                (<= (+ -1 (expt 2 n)) k))
           (not (< k (bvchop n x)))))

(defthm slice-bound-hack
  (not (> (slice 31 27 x) 32))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-slice-gen (x x) (low 27) (high 31) (n 5))
           :in-theory (disable unsigned-byte-p-of-slice-gen))))

(defthm slice-bound-hack2
  (< (slice 31 27 x) 32)
  :hints (("Goal" :use (:instance unsigned-byte-p-of-slice-gen (x x) (low 27) (high 31) (n 5))
           :in-theory (disable unsigned-byte-p-of-slice-gen))))

(defthm slice-bound-hack3
  (not (> (slice 31 27 x) 31))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-slice-gen (x x) (low 27) (high 31) (n 5))
           :in-theory (disable unsigned-byte-p-of-slice-gen unsigned-byte-p-of-slice))))

(defthm slice-of-bitxor-too-high
  (implies (and (<= 1 low)
                (integerp low))
           (equal (slice high low (bitxor x y))
                  0))
  :hints (("Goal" :in-theory (e/d (bitxor slice-too-high-is-0)
                                  (bvxor-1-becomes-bitxor)))))

;;We'd like BVNOT to be invisible when commuting BVXOR nests.  But BVNOT is not
;;unary, so I don't think ACL2's built-in notion of invisible-fns will work.
;;So we implement our own version here for BVXOR calls.

;TODO: Move to bv-syntax file?
;fixme should we check the size of the bvnot call?
(defun strip-off-bvnot-call (term)
  (declare (xargs :guard t))
  (if (and (consp term)
           (eq 'bvnot (car term))
           (consp (cdr term))
           (consp (cddr term)))
      (farg2 term)
    term))

;ffixme don't mess up associativity - see should-commute-args and make a non-dag version?
(defund smaller-bvxor-arg (term1 term2)
; (declare (xargs :guard t)) ;todo add a guard
  (smaller-termp (strip-off-bvnot-call term1)
                 (strip-off-bvnot-call term2)))

(defthm bvxor-commutative-alt
  (implies (syntaxp (smaller-bvxor-arg b a))
           (equal (bvxor size a b)
                  (bvxor size b a)))
  :rule-classes ((:rewrite :loop-stopper nil ;((a b bvxor))
                           ))
  :hints (("Goal" :in-theory (enable bvxor))))

(in-theory (disable bvxor-commutative))
(theory-invariant (incompatible (:rewrite bvxor-commutative) (:rewrite bvxor-commutative-alt)))

(defthm bvxor-commutative-2-alt
  (implies (syntaxp (smaller-bvxor-arg a b))
           (equal (bvxor size b (bvxor size a c))
                  (bvxor size a (bvxor size b c))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable bvxor))))

(in-theory (disable bvxor-commutative-2))
(theory-invariant (incompatible (:rewrite bvxor-commutative-2) (:rewrite bvxor-commutative-2-alt)))

;use trim?
(defthm bitxor-of-slice-arg1
  (implies (and (<= low high)
                (natp low)
                (natp high))
           (equal (bitxor (slice high low x) y)
                  (bitxor (getbit low x) y)))
  :hints (("Goal" :in-theory (e/d (bitxor) (BVXOR-1-BECOMES-BITXOR)))))

;use trim?
;bozo analogue for bvand?
(defthm bitxor-of-slice-arg2
  (implies (and (<= low high)
                (natp low)
                (natp high))
           (equal (bitxor y (slice high low x))
                  (bitxor y (getbit low x))))
  :hints (("Goal" :in-theory (e/d (bitxor) (BVXOR-1-BECOMES-BITXOR)))))

;bozo think about these...
(defthm bvcat-bvxor-neighbors-hack
  (implies (and (equal n+1 (+ 1 n))
                (natp n)
                )
           (equal (bvcat 1
                         (BVXOR 1 (GETBIT n+1 y) (GETBIT n+1 x)) 1
                         (BVXOR 1 (GETBIT n y) (GETBIT n x)))
                  (bvxor 2 (slice n+1 n y)
                         (slice n+1 n x))))
  :hints (("Goal" :in-theory (enable BITXOR-COMMUTATIVE))))

(defthm bvcat-bvxor-neighbors-hack2
  (implies (and (equal n+1 (+ 1 n))
                (equal k (+ high (- n)))
                (natp n)
                (natp high)
                (<= n+1 high)
                )
           (equal (bvcat
                   k
                   (BVXOR k (slice high n+1 y) (slice high n+1 x)) 1
                   (BVXOR 1 (GETBIT n y) (GETBIT n x)))
                  (bvxor (+ 1 high (- n))
                         (slice high n y)
                         (slice high n x))))
  :hints (("Goal" :in-theory (enable bitxor-commutative))))

(defthm getbit-0-of-logapp
  (implies (and (integerp x)
                (integerp y))
           (equal (getbit 0 (logapp 1 y x))
                  (getbit 0 y)))
  :hints (("Goal" :in-theory (e/d (getbit ;logapp
                                   ) (slice-becomes-getbit bvchop-1-becomes-getbit)))))

(defthm logand-even-of-logapp-1
  (implies (and ;(evenp k) ;drop somehow?
                (natp x)
                (natp k))
            (equal (binary-logand k (logapp 1 0 x))
                   ;had / instead of floor below:
                   (logapp 1 0 (binary-logand (floor k 2) x))))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :expand ((LOGTAIL 1 K))
            :in-theory (enable LOGCDR LOGAND))))

(defthmd logtail-when-bound
  (implies (and (integerp x)
                (< x 0)
                (<= -128 x))
           (equal (logtail 7 x)
                  -1))
  :hints (("Goal" :in-theory (enable logtail))))

;rewrite (EQUAL (LOGEXT 8 X) (BVCHOP 7 X))

(defthmd multiply-both-sides-hack
  (implies (and (integerp x) (integerp y)
                (rationalp z) (< 0 z))
           (equal (< x y)
                  (< (* x z) (* y z)))))

(defthm small-int-hack
  (implies (and (< 0 small)
                (< small 1)
                (integerp i)
                (integerp j)
                (rationalp small))
           (equal (< (+ i small) j)
                  (< i j))))

(defthm bvchop-divided-hack
  (< (* (/ (EXPT 2 N)) (BVCHOP N A)) 1))

(defthm bvchop-equal-expt-2-hack
  (not (EQUAL (BVCHOP N A) (EXPT 2 N))))

(defthm integer-of-bvchop-divided-by-expt
  (equal (INTEGERP (* (/ (EXPT 2 N)) (BVCHOP N A)))
         (equal 0 (BVCHOP N A)))
  :hints (("Goal" :in-theory (disable |0-1-SPLIT-CHEAP|)
           :use (:instance integer-squeeze-0-1 (x (* (/ (EXPT 2 N)) (BVCHOP N A)))))))

(defthm integerp-power2-hack
  (implies (and (integerp m)
                (integerp n))
           (equal (INTEGERP (* 1/2 (EXPT 2 M) (/ (EXPT 2 N))))
                  (< n m)))
  :hints (("Goal"
           :in-theory (e/d (expt-of-+) (INTEGERP-OF-EXPT-when-natp))
           :use (:instance INTEGERP-OF-EXPT-when-natp (r 2) (i (+ -1 m (- n)))))))

;; (defthm signed-byte-p-of-logapp
;;   (implies (and (integerp b)
;;                 (< n m)
;;                 (natp m)
;;                 (natp n))
;;            (equal (signed-byte-p m (LOGAPP n a b))
;;                   (signed-byte-p (- m n) b)))
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (enable signed-byte-p logapp))))


;;   :otf-flg t
;;   :hints ( ("Goal" :use ((:instance integer-squeeze-0-1 (x (* (/ (EXPT 2 N)) (BVCHOP N A))))
;;                          (:instance multiply-both-sides-hack (x (+ (BVCHOP N A) (* B (EXPT 2 N)))) (y (EXPT 2 (+ -1 M))) (z (/ (expt 2 n))))
;;                          (:instance multiply-both-sides-hack (x (+ (BVCHOP N A) (* B (EXPT 2 N)))) (y (- (EXPT 2 (+ -1 M)))) (z (/ (expt 2 n))))
;;                          (:instance multiply-both-sides-hack (x b) (y (- (* 1/2 (EXPT 2 M) (/ (EXPT 2 N))))) (z (expt 2 n)))
;;                          (:instance multiply-both-sides-hack (x (* (/ (EXPT 2 N)) (BVCHOP N A))) (y (* 1/2 (EXPT 2 M) (/ (EXPT 2 N)))) (z (expt 2 n)))
;;                          (:instance EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1 (r 2) (i n) (j (- m 1)))
;;                          )
;;             :cases ((and (EQUAL (BVCHOP N A) '0) (<= 0 b)))
;;             :in-theory (e/d (logapp expt-of-+
;;                                     signed-byte-p) (<-*-/-RIGHT-COMMUTED <-*-/-left-COMMUTED <-*-LEFT-CANCEL
;;                                     <-*-/-LEFT
;;                                     <-*-/-right
;;                                     )))))


(defthm logtail-of-logorc1
  (IMPLIES (NATP N)
           (EQUAL (LOGTAIL N (LOGORC1 A B))
                  (LOGORC1 (LOGTAIL N A) (LOGTAIL N B))))
  :hints (("Goal" :in-theory (enable LOGORC1))))

(defthm logtail-of-logeqv
  (IMPLIES (NATP N)
           (EQUAL (LOGTAIL N (LOGEQV A B))
                  (LOGEQV (LOGTAIL N A) (LOGTAIL N B))))
  :hints (("Goal" :in-theory (enable LOGEQV))))

(defthm add-bvchops-to-equality-of-sbps-1
  (implies (and (syntaxp (and (equal (car x) 'logext)
                              (equal (cadr x) ''1) ;looped without this (see comment just above)
                              ))
                (signed-byte-p 1 x)
                (signed-byte-p 1 y))
           (equal (equal x y)
                  (equal (bvchop 1 x)
                         (bvchop 1 y)))))

(defthm signed-byte-p-of-logtail-hack
  (IMPLIES (AND (EQUAL (FLOOR X (EXPT 2 M))
                       (- (* 1/2 (EXPT 2 N))))
                (POSP M)
                (INTEGERP X)
                (POSP N))
           (NOT (< X (- (* 1/2 (EXPT 2 M) (EXPT 2 N))))))
  :hints (("Goal" ;:do-not '(generalize eliminate-destructors)
           :use (:instance multiply-both-sides-hack (x x) (y (- (* 1/2 (EXPT 2 M) (EXPT 2 N)))) (z (expt 2 m))))))

(defthm signed-byte-p-of-logtail
  (implies (and (integerp x)
                (posp n)
                (posp m)
                )
           (equal (signed-byte-p n (logtail m x))
                  (signed-byte-p (+ n m) x)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use ((:instance FLOOR-WEAK-MONOTONE (i1 (- (EXPT 2 (+ -1 M N)))) (i2 x) (j (expt 2 m)))
                 (:instance FLOOR-WEAK-MONOTONE (i2 (- (EXPT 2 (+ -1 M N)))) (i1 x) (j (expt 2 m)))
                 (:instance FLOOR-WEAK-MONOTONE (i1 (EXPT 2 (+ -1 M N))) (i2 x) (j (expt 2 m)))
                 (:instance FLOOR-WEAK-MONOTONE (i2 (EXPT 2 (+ -1 M N))) (i1 x) (j (expt 2 m))))
           :in-theory (e/d (signed-byte-p logtail expt-of-+) (FLOOR-WEAK-MONOTONE)))))

;fixme kill these??

;; (defthmd sbp-32-logapp-24
;;   (implies (and (integerp x)
;;                 (integerp v))
;;            (equal (signed-byte-p '32 (logapp '24 v x))
;;                   (signed-byte-p 8 x))))

;; (defthmd sbp-32-logapp-8
;;   (implies (and (integerp x)
;;                 (integerp v))
;;            (equal (signed-byte-p '32 (logapp 8 v x))
;;                   (signed-byte-p 24 x))))

;; (defthmd sbp-32-logapp-16
;;   (implies (and (integerp x)
;;                 (integerp v))
;;            (equal (signed-byte-p '32 (logapp 16 v x))
;;                   (signed-byte-p 16 x))))

;kill?
;; (defthm sbp-of-logapp
;;    (implies (and (natp n)
;;                  (natp lowsize)
;;                  (< lowsize n)
;;                  (integerp lowval)
;;                  (integerp highval))
;;             (equal (signed-byte-p n (logapp lowsize lowval highval))
;;                    (signed-byte-p (- n lowsize) highval)))
;;    :otf-flg t
;;    :hints (("Goal" :in-theory (enable))))

(defthm bvxor-1-equal-0
  (equal (equal (bvxor 1 x y) 0)
         (xor (mynot (equal 0 (getbit 0 x)))
              (equal 0 (getbit 0 y))))
  :hints (("Goal" :in-theory (e/d (xor mynot bitxor bvxor) (BVXOR-1-BECOMES-BITXOR)))))


;gen the 1
;drop, since bvxor should go to bitxor first?
(defthmd bvxor-1
  (equal (bvxor 1 1 x)
         (bvnot 1 x))
  :hints (("Goal"
           :cases ((equal 0 (getbit 0 x)))
           :use ((:instance BVCHOP-LOGNOT-BVCHOP-1))
           :in-theory (e/d (bvxor bvnot bitxor ;LOGXOR*
    ;                                          bvchop
    ;lognot getbit
                                  )
                           (SLICE-BECOMES-GETBIT
                            GETBIT-WHEN-NOT-0
                            BVCHOP-LOGNOT-BVCHOP-1
    ;BVCHOP-1-BECOMES-GETBIT
                            BVXOR-1-BECOMES-BITXOR)))))

;we should either prefer xors to nots, or vice versa (weird 4 rule loop if we are not careful)
(theory-invariant (incompatible (:rewrite bvxor-1) (:rewrite bitnot-becomes-bitxor-with-1)))

;bozo how can we decide which branch to move the lognot into?
(defthmd bvnot-of-bvxor-1
  (equal (bvnot 1 (bvxor 1 x y))
         (bvxor 1 (bvnot 1 x) y))
  :hints (("Goal" :in-theory (enable bitxor-split))))

(defthm bvnot-of-bvxor-1-back
   (equal (bvxor 1 (bvnot 1 x) y)
          (bvnot 1 (bvxor 1 x y)))
   :hints (("Goal" :use (:instance bvnot-of-bvxor-1))))

(defthm bvnot-of-bvxor-1-back-alt
  (equal (bvxor 1 y (bvnot 1 x))
         (bvnot 1 (bvxor 1 y x)))
  :hints (("Goal" :use (:instance bvnot-of-bvxor-1-back)
           :in-theory (e/d (BITXOR-COMMUTATIVE BITXOR-COMMUTATIVE-2) ( bvnot-of-bvxor-1-back)))))

;(local (in-theory (enable BITXOR-COMMUTATIVE BITXOR-COMMUTATIVE-2))) ;hope these don't loop

;gen the size!  or use bitnot
(defthm bvxor-of-x-and-bvnot-x
  (equal (bvxor 1 (bvnot 1 x) x)
         1))

(defthm bvxor-of-x-and-bvnot-x-alt
  (equal (bvxor 1 x (bvnot 1 x))
         1)
  :hints (("Goal" :in-theory (e/d (bitxor-commutative-2)
                                  (equal-of-0-and-bitxor)))))

(defthm bvxor-of-x-and-bvnot-x-alt-3terms
  (equal (bvxor 1 x (bvxor 1 (bvnot 1 x) y))
         (bvnot 1 y))
  :hints (("Goal" :in-theory (enable bitxor-commutative-2))))

(defthm bvxor-of-x-and-bvnot-x-3terms
  (equal (bvxor 1 (bvnot 1 x) (bvxor 1 x y))
         (bvnot 1 y)))

(defthm getbit-lognot-getbit
  (equal (getbit 0 (lognot (getbit 0 x)))
         (getbit 0 (lognot x)))
  :hints (("Goal"
           :use ((:instance bvchop-lognot-bvchop-1))
           :in-theory (e/d ( getbit) ( slice-becomes-getbit bvchop-1-becomes-getbit)))))

(defthm bvnot-equal-0-rewrite
  (equal (equal 0 (bvnot 1 x))
         (mynot (equal 0 (getbit 0 x))))
  :hints (("Goal" :in-theory (e/d (bitnot) (BITNOT-BECOMES-BITXOR-WITH-1 ;bozo
                                        )))))

(defthm bvxor-of-bvnot-1
  (equal (bvxor 1 (bvnot 1 x) y)
         (bvnot 1 (bvxor 1 x y))))

(defthm bvxor-of-bvnot-2
  (equal (bvxor 1 y (bvnot 1 x))
         (bvnot 1 (bvxor 1 y x)))
  :hints (("Goal" :in-theory (enable bitxor-commutative-2))))

;;
;; bool-to-bit - do we translate this op to stp?
;;

(defthm getbit-0-of-bool-to-bit
  (equal (getbit 0 (bool-to-bit x))
         (bool-to-bit x))
  :hints (("Goal" :in-theory (enable bool-to-bit))))

(defthm bvif-lognot-size-1
  (equal (bvif 1 test (bvnot 1 x) x)
         (bvxor 1 (bool-to-bit test)
                x))
  :hints (("Goal" :in-theory (enable bitnot bool-to-bit bvif))))

(defthm bvif-lognot-size-1-alt
  (equal (bvif 1 test x (bvnot 1 x))
         (bvxor 1 (bvnot 1 (bool-to-bit test))
                x))
  :hints (("Goal" :in-theory (enable bool-to-bit bvif))))

;use bitxor?
(defthm bool-to-bit-of-xor
  (equal (bool-to-bit (xor x y))
         (bvxor 1 (bool-to-bit x)
                  (bool-to-bit y)))
  :hints (("Goal" :in-theory (enable bool-to-bit xor))))

;use bitnot?
(defthm bool-to-bit-of-equal-0-getbit-1
  (equal (bool-to-bit (equal 0 (getbit n x)))
         (bvnot 1 (getbit n x)))
  :hints (("Goal" :in-theory (enable bool-to-bit))))

;use bitnot?
(defthm bool-to-bit-of-equal-0-getbit-2
  (equal (bool-to-bit (equal (getbit n x) 0))
         (bvnot 1 (getbit n x)))
  :hints (("Goal" :in-theory (enable bool-to-bit))))

(defthm bvif-0-1
  (equal (bvif 1 test 0 1)
         (bvnot 1 (bool-to-bit test)))
  :hints (("Goal" :in-theory (enable bool-to-bit bvif myif))))

(defthm bvchop-of-bvnot
  (implies (and (<= n size)
                (natp n)
                (natp size))
           (equal (bvchop n (bvnot size val))
                  (bvnot n val)))
  :hints (("Goal" :in-theory (enable bvnot))))


;; (thm
;;  (equal (BVNOT LOWSIZE (BVCAT HIGHSIZE HIGHVAL LOWSIZE LOWVAL))
;;         (bvchop HIGHSIZE HIGHVAL))
;;  :hints (("Goal" :in-theory (enable bvnot))))

(defthm getbit-of-logior
  (equal (getbit n (logior a b))
         (logior (getbit n a)
                 (getbit n b)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (getbit slice) (BVCHOP-OF-LOGTAIL-BECOMES-SLICE SLICE-BECOMES-GETBIT BVCHOP-1-BECOMES-GETBIT)))))

;drop in favor of trim rules?
(defthm slice-of-bvxor-tighten
  (implies (and (< (+ 1 highbit) size)
;                (<= lowbit highbit)
                (integerp size)
                (< 0 size)
                (natp lowbit)
                (natp highbit)
                (integerp x)
                (integerp y))
           (equal (slice highbit lowbit (bvxor size x y))
                  (slice highbit lowbit (bvxor (+ 1 highbit) x y))))
  :hints (("Goal" :cases ((<= lowbit highbit))
          :in-theory (e/d (slice bvxor natp) (BVCHOP-OF-LOGTAIL-BECOMES-SLICE slice-becomes-bvchop)))))

;drop in favor of trim rules?
(defthm slice-of-bvand-tighten
  (implies (and (< (+ 1 highbit) size)
;                (<= lowbit highbit)
                (integerp size)
                (< 0 size)
                (natp lowbit)
                (natp highbit)
                (integerp x)
                (integerp y))
           (equal (slice highbit lowbit (bvand size x y))
                  (slice highbit lowbit (bvand (+ 1 highbit) x y))))
  :hints (("Goal" :cases ((<= lowbit highbit))
          :in-theory (e/d (slice bvand natp) ( slice-becomes-bvchop
                                               BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

;drop in favor of trim rules?
(defthm slice-of-bvmult-tighten
  (implies (and (< (+ 1 highbit) size)
    ;                (<= lowbit highbit)
                (integerp size)
                (< 0 size)
                (natp lowbit)
                (natp highbit)
                (integerp x)
                (integerp y))
           (equal (slice highbit lowbit (bvmult size x y))
                  (slice highbit lowbit (bvmult (+ 1 highbit) x y))))
  :hints (("Goal" :cases ((<= lowbit highbit))
           :in-theory (e/d (slice bvor natp bvmult) ( slice-becomes-bvchop BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

(defthm bvxor-of-bvxor-tighten
  (implies (and (< size1 size2)
                (integerp z)
                (natp size1)
                (natp size2))
           (equal (bvxor size1 (bvxor size2 x y) z)
                  (bvxor size1 (bvxor size1 x y) z)))
  :hints (("Goal" :in-theory (enable bvxor bvand))))

(defthm bvxor-of-bvxor-tighten-alt
  (implies (and (< size1 size2)
                (integerp z)
                (natp size1)
                (natp size2))
           (equal (bvxor size1 z (bvxor size2 x y))
                  (bvxor size1 z (bvxor size1 x y))))
  :hints (("Goal" :in-theory (enable bvxor bvand))))

;use trim
(defthm bvor-of-bvxor-tighten
  (implies (and (< size1 size2)
                (integerp z)
                (natp size1)
                (natp size2))
           (equal (bvor size1 (bvxor size2 x y) z)
                  (bvor size1 (bvxor size1 x y) z)))
  :hints (("Goal" :in-theory (enable bvor bvxor bvand))))

;use trim
(defthm bvor-of-bvxor-tighten-alt
  (implies (and (< size1 size2)
                (integerp z)
                (natp size1)
                (natp size2))
           (equal (bvor size1 z (bvxor size2 x y))
                  (bvor size1 z (bvxor size1 x y))))
  :hints (("Goal" :in-theory (enable bvor bvxor bvand))))

(defthm slice-of-bvand
  (implies (and (< highbit size)
                (integerp size)
                (<= 0 size)
                (natp lowbit)
                (natp highbit)
                )
           (equal (slice highbit lowbit (bvand size x y))
                  (bvand (+ 1 highbit (- lowbit))
                           (slice highbit lowbit x)
                           (slice highbit lowbit y))))
  :hints (("Goal" :cases ((natp (+ 1 highbit (- lowbit))))
           :in-theory (e/d (slice bvand natp) (slice-becomes-bvchop
                                               bvchop-of-logtail-becomes-slice)))))


;use trim
(defthm bvor-of-bvmult-tighten-2
  (implies (and (< size1 size2)
                (natp size1)
                (natp size2)
                (integerp x)
                (integerp y)
                (integerp z))
           (equal (bvor size1 x (bvmult size2 y z))
                  (bvor size1 x (bvmult size1 y z))))
  :hints (("Goal" :in-theory (enable bvor))))

;use trim
(defthm bvor-of-bvmult-tighten-1
  (implies (and (< size1 size2)
                (natp size1)
                (natp size2)
                (integerp x)
                (integerp y)
                (integerp z))
           (equal (bvor size1 (bvmult size2 y z) x)
                  (bvor size1 (bvmult size1 y z) x)))
  :hints (("Goal" :in-theory (enable bvor))))

;use trim
(defthm bvxor-of-bvmult-tighten-2
  (implies (and (< size1 size2)
                (natp size1)
                (natp size2)
                (integerp x)
                (integerp y)
                (integerp z))
           (equal (bvxor size1 x (bvmult size2 y z))
                  (bvxor size1 x (bvmult size1 y z))))
  :hints (("Goal" :in-theory (enable bvxor))))

;use trim
(defthm bvxor-of-bvmult-tighten-1
  (implies (and (< size1 size2)
                (natp size1)
                (natp size2)
                (integerp x)
                (integerp y)
                (integerp z))
           (equal (bvxor size1 (bvmult size2 y z) x)
                  (bvxor size1 (bvmult size1 y z) x)))
  :hints (("Goal" :in-theory (enable bvxor))))

;use trim
;newly disabled
(defthmd bvand-of-bvmult-tighten-2
  (implies (and (< size1 size2)
                (natp size1)
                (natp size2)
                (integerp x)
                (integerp y)
                (integerp z))
           (equal (bvand size1 x (bvmult size2 y z))
                  (bvand size1 x (bvmult size1 y z))))
  :hints (("Goal" :in-theory (enable bvand))))

;use trim
;newly disabled
(defthmd bvand-of-bvmult-tighten-1
  (implies (and (< size1 size2)
                (natp size1)
                (natp size2)
                (integerp x)
                (integerp y)
                (integerp z))
           (equal (bvand size1 (bvmult size2 y z) x)
                  (bvand size1 (bvmult size1 y z) x)))
  :hints (("Goal" :in-theory (enable bvand))))

;use trim
(defthm bvcat-of-bvand-tighten-2
  (implies (and (< size1 size2)
                (natp size1)
                (natp size2)
                (integerp x)
                (integerp z)
                (integerp y))
           (equal (bvcat size1 (bvand size2 z y) lowsize x)
                  (bvcat size1 (bvand size1 z y) lowsize x)))
  :hints (("Goal" :in-theory (e/d (bvcat) ()))))

;use trim
(defthm bvcat-of-bvor-tighten-2
  (implies (and (< size1 size2)
                (natp size1)
                (natp size2)
                (integerp x)
                (integerp z)
                (integerp y))
           (equal (bvcat size1 (bvor size2 z y) lowsize x)
                  (bvcat size1 (bvor size1 z y) lowsize x)))
  :hints (("Goal" :in-theory (e/d (bvcat) ()))))

;i'll leave this off, since it gets rid of bvand and is sort of scary
;bozo do i want to open from the top or the bottom?  which one is faster?
;rename
(defthmd bvand-open-to-logapp
  (implies (and (natp size)
                (< 1 size))
           (equal (bvand size x y)
                  (bvcat 1
                         (bvand 1 (getbit (+ -1 size) x) (getbit (+ -1 size) y))
                         (+ -1 size)
                         (bvand (+ -1 size)  x y))))
  :hints (("Goal" :cases ((and (integerp x) (integerp y))
                          (and (integerp x) (not (integerp y)))
                          (and (not (integerp x)) (integerp y))))))

(defthmd bvand-open-to-logapp-when-constant
  (implies (and (syntaxp (quotep x))
                (natp size)
                (< 1 size))
           (equal (bvand size x y)
                  (bvcat 1 (bvand 1 (getbit (+ -1 size) x) (getbit (+ -1 size) y))
                         (+ -1 size) (bvand (+ -1 size)  x y))))
  :hints (("Goal" :in-theory (enable bvand-open-to-logapp))))

(defthm bvand-of-bvcat
  (implies (and (equal size (+ lowsize highsize))
                (integerp lowval)
                (integerp highval)
                (integerp lowsize)
                (integerp highsize)
                (<= 0 lowsize)
                (<= 0 highsize)
                (integerp x))
           (equal (bvand size x (bvcat highsize highval lowsize lowval))
                  (bvcat
                   highsize
                   (bvand highsize (slice (+ -1 size) lowsize x)
                          highval) lowsize
                   (bvand lowsize (bvchop lowsize x)
                          lowval))))
  :hints (("Goal" :in-theory (e/d (bvcat bvand slice)
                                  (bvchop-of-logtail-becomes-slice)))))

;(local (in-theory (disable LOGAPP-0-NEW2)));why?

(defthm bvor-of-bvcat-gen
   (implies (and (integerp x)
                 (integerp y)
                 (integerp z)
                 (natp size)
                 (natp size2)
                 (<= (+ -1 size2) size)
                 (natp lowsize)
                 (< lowsize size2)
                 (< 0 lowsize)
                 )
            (equal (bvor size2 (bvcat size y lowsize x) z)
                   (bvcat (- size2 lowsize)
                            (bvor (- size2 lowsize) y (slice (+ -1 size2) lowsize z))
                            lowsize
                            (bvor lowsize x z))))
   :hints (("Goal" :in-theory (enable bvor ;bvchop-bvchop
                                      ))))

(defthmd bvxor-of-bvcat-better
  (implies (and (>= size (+ lowsize highsize))
                (natp size)
                (integerp lowval)
                (integerp highval)
                (integerp lowsize)
                (integerp highsize)
                (<= 0 lowsize)
                (< 0 highsize) ;bozo
                ;(integerp x)
                )
           (equal (bvxor size x (bvcat highsize highval lowsize lowval))
                  (bvcat ;drop drop the bvchop?
                   (- size lowsize)
                   (bvxor (- size lowsize) (slice (+ -1 size) lowsize x) (bvchop highsize highval)) lowsize
                   (bvxor lowsize (bvchop lowsize x) lowval)))) ;could tighetn the slice?
  :hints (("Goal" :in-theory (e/d (                              ;bvcat bvxor
                                   ) ( )))))

;fixme what does repeatbit do if not given a bit??

;; (DEFTHM SLICE-WHEN-high-IS-NEGATIVE
;;   (IMPLIES (AND (< high 0)
;; ;                (natp LOW)
;;                 (INTEGERP HIGH))
;;            (EQUAL (SLICE HIGH LOW X)
;;                   0))
;;   :HINTS (("Goal" :IN-THEORY (E/d (SLICE natp) (BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

(defthm slice-of-bvchop-low-gen-better
  (implies (and (natp high)
                (natp low)
          ;      (natp n)
                )
           (equal (slice high low (bvchop n x))
                  (if (and ;(natp high)
                           (natp n))
                  (if (< high n)
                      (slice high low x)
                    (if (and (<= n high)
                             (<= low n))
                        (slice (+ -1 n) low x)
                      0))
                  0)))
  :hints (("Goal" :in-theory (enable natp))))

(defthm slice-of-bvnot
  (implies (and (< highbit size)
                (<= lowbit highbit)
                (natp size)
                (natp lowbit)
                (natp highbit))
           (equal (slice highbit lowbit (bvnot size x))
                  (bvnot (+ 1 highbit (- lowbit)) (slice highbit lowbit x))))
  :hints (("Goal"
           :use ((:instance bvchop-lognot-bvchop (n (+ 1 highbit (- lowbit))) (x (logtail lowbit x)))
                 (:instance bvchop-of-mask-gen (size2 (+ 1 highbit (- lowbit)))
                            (size1 (- size lowbit))))
           :cases ((integerp x)
                   (not (integerp x))
                   )
           :in-theory (e/d (bvnot slice ;logtail-bvchop
                                  lognot-of-logtail
                                  bvchop-of-mask-gen
                                  ) (bvchop-of-logtail-becomes-slice
                                  bvchop-of-minus
                                  logtail-of-lognot
                                  ;LOGNOT-OF-LOGTAIL
                                  bvchop-lognot-bvchop
;bvchop-of-logtail
                                  logtail-of-bvchop-becomes-slice)))))

;gen!
(defthm bvnot-equal-1-rewrite
  (equal (equal (bvnot 1 x) 1)
         (equal (getbit 0 x) 0))
  :hints (("Goal" :in-theory (e/d (bitnot) (BITNOT-BECOMES-BITXOR-WITH-1)))))

;fixme make a trim theory for bitnot (and all other operators!)
(defthm bitnot-of-slice
  (implies (and (< low high) ;no longer allow = (would loop if we're opening up slice
                (natp low)
                (natp high)
                )
           (equal (bitnot (slice high low x))
                  (bitnot (getbit low x))))
  :hints (("Goal" :in-theory (enable bitnot))))

;make a rule to substitute?
(defthm getbits-same-when-bvchops-same
  (implies (and (equal (bvchop free x) (bvchop free y))
                (< n free)
                (natp free)
                (natp n)
                )
           (equal (equal (getbit n x) (getbit n y))
                  t))
  :hints (("Goal" :use ((:instance GETBIT-OF-BVCHOP (m n) (n free) (x x))
                        (:instance GETBIT-OF-BVCHOP (m n) (n free) (x y)))
           :in-theory (disable GETBIT-OF-BVCHOP))))

(defthm bvchops-same-when-bvchops-same
  (implies (and (equal (bvchop free x) (bvchop free y))
                (<= n free)
                (natp free)
                (natp n)
                )
           (equal (equal (bvchop n x) (bvchop n y))
                  t))
  :hints (("Goal" :use ((:instance BVCHOP-OF-BVCHOP (size1 n) (size free) (i x))
                        (:instance BVCHOP-OF-BVCHOP (size1 n) (size free) (i y)))
           :in-theory (disable BVCHOP-OF-BVCHOP))))

(defthm slices-same-when-slices-same
  (implies (and (equal (bvchop free x) (bvchop free y))
                (< high free)
                (natp free)
                (natp high)
                (natp low)
                )
           (equal (equal (slice high low x) (slice high low y))
                  t))
  :hints (("Goal" :use ((:instance SLICE-OF-bvchop-low (n free) (x x))
                        (:instance SLICE-OF-bvchop-low (n free) (x y)))
           :in-theory (disable SLICE-OF-SLICE))))

;can this loop?
(defthm equal-of-bvchop-and-bvchop-when-smaller-bvchops-equal
  (implies (and (equal (bvchop free x) (bvchop free y))
                (<= free n)
                (posp n)
                (natp free)
                )
           (equal (equal (bvchop n x) (bvchop n y))
                  (equal (slice (+ -1 n) free x)
                         (slice (+ -1 n) free y))))
  :hints (("Goal"
           :in-theory (disable BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE)
           :use ((:instance split-bv (n n) (m free) (y (bvchop n x)))
                 (:instance split-bv (n n) (m free) (y (bvchop n y)))))))

(defthm equal-of-bvsx-and-bvsx
  (implies (and (< lowsize n)
                (posp lowsize)
                (integerp n))
           (equal (equal (bvsx n lowsize x) (bvsx n lowsize y))
                  (equal (bvchop lowsize x)
                         (bvchop lowsize y))))
  :hints (("Goal"
           :in-theory (enable bvsx))))

;bozo
(defthmd blast-bvxor-32-into-8
  (equal (bvxor 32 a b)
         (bvcat2 8 (bvxor 8 (slice 31 24 a) (slice 31 24 b))
                 8 (bvxor 8 (slice 23 16 a) (slice 23 16 b))
                 8 (bvxor 8 (slice 15  8 a) (slice 15  8 b))
                 8 (bvxor 8 (slice  7  0 a) (slice  7  0 b))))
  :hints (("Goal" :in-theory (enable slice-when-val-is-not-an-integer)
           :cases ((and (integerp a) (integerp b))
                   (and (not (integerp a)) (integerp b))
                   (and (integerp a) (not (integerp b)))))))

;bozo
(defthmd blast-bvor-32-into-8
  (equal (bvor 32 a b)
         (bvcat2 8 (bvor 8 (slice 31 24 a) (slice 31 24 b))
                 8 (bvor 8 (slice 23 16 a) (slice 23 16 b))
                 8 (bvor 8 (slice 15  8 a) (slice 15  8 b))
                 8 (bvor 8 (slice  7  0 a) (slice  7  0 b))))
  :hints (("Goal" :in-theory (enable slice-when-val-is-not-an-integer)
           :cases ((and (integerp a) (integerp b))
                   (and (not (integerp a)) (integerp b))
                   (and (integerp a) (not (integerp b)))))))

;bozo
(defthmd blast-bvand-32-into-8
  (equal (bvand 32 a b)
         (bvcat2 8 (bvand 8 (slice 31 24 a) (slice 31 24 b))
                 8 (bvand 8 (slice 23 16 a) (slice 23 16 b))
                 8 (bvand 8 (slice 15  8 a) (slice 15  8 b))
                 8 (bvand 8 (slice  7  0 a) (slice  7  0 b))))
  :hints (("Goal" :in-theory (enable slice-when-val-is-not-an-integer
                                     bvchop-when-i-is-not-an-integer)
           :cases ((and (integerp a) (integerp b))
                   (and (not (integerp a)) (integerp b))
                   (and (integerp a) (not (integerp b)))))))

(defthm bvminus-of-bvcat-irrel-arg2
   (implies (and (<= size2 size)
                 (natp size2)
  ;               (integerp x)
   ;              (integerp y)
                 (integerp size)
                 )
            (equal (bvminus size2 x (bvcat n z size y))
                   (bvminus size2 x y)))
   :hints (("Goal"
            :use ((:instance bvchop-of-minus-of-bvchop
                            (size size2)
                            (x (bvcat n z size (ifix y))))
                  (:instance bvchop-of-minus-of-bvchop
                            (size size2)
                            (x y)))
            :in-theory (e/d (bvminus bvplus bvchop-when-i-is-not-an-integer) (bvchop-of-minus-of-bvchop bvchop-of-minus-of-bvchop-gen)))))

(defthm bvminus-of-bvcat-irrel-arg1
  (implies (and (<= size2 size)
                (natp size2)
;                (integerp x)
 ;               (integerp y)
                (integerp size)
                )
           (equal (bvminus size2 (bvcat n z size y) x)
                  (bvminus size2 y x)))
  :hints (("Goal" :in-theory (enable bvminus bvplus bvchop-when-i-is-not-an-integer))))

(defthm bvplus-of-logext-gen-arg1
   (implies (and (<= size1 size2)
;               (integerp x)
;                (integerp y)
                 (< 0 size2)
                 (natp size1)
                 (natp size2))
            (equal (bvplus size1 (logext size2 x) y)
                   (bvplus size1 x y)))
   :hints (("Goal"
            :use (:instance bvchop-sum-drop-bvchop (m size1) (n size1) (z y) (y (logext size2 x)))
            :in-theory (e/d (bvplus)
                            (bvchop-sum-drop-bvchop)))))

(defthm bvplus-of-logext-gen-arg2
  (implies (and (<= size1 size2)
;               (integerp x)
;                (integerp y)
                (< 0 size2)
                (natp size1)
                (natp size2))
           (equal (bvplus size1 y (logext size2 x))
                  (bvplus size1 y x)))
  :hints (("Goal" :use (:instance bvplus-of-logext-gen-arg1)
           :in-theory (enable bvplus-of-logext-gen-arg1))))

(defthm bvif-of-logext-gen-arg1
   (implies (and (<= size1 size2)
;               (integerp x)
;                (integerp y)
                 (< 0 size2)
                 (natp size1)
                 (natp size2))
            (equal (bvif size1 test (logext size2 x) y)
                   (bvif size1 test x y)))
   :hints (("Goal" :in-theory (enable bvif myif))))

(defthm bvif-of-logext-gen-arg2
   (implies (and (<= size1 size2)
;               (integerp x)
;                (integerp y)
                 (< 0 size2)
                 (natp size1)
                 (natp size2))
            (equal (bvif size1 test y (logext size2 x))
                   (bvif size1 test y x)))
   :hints (("Goal" :in-theory (enable bvif myif))))

(defthmd bvxor-8-bit-blast
  (equal (bvxor 8 x y)
         (bvcat2 1 (bvxor 1 (getbit 7 x) (getbit 7 y))
                 1 (bvxor 1 (getbit 6 x) (getbit 6 y))
                 1 (bvxor 1 (getbit 5 x) (getbit 5 y))
                 1 (bvxor 1 (getbit 4 x) (getbit 4 y))
                 1 (bvxor 1 (getbit 3 x) (getbit 3 y))
                 1 (bvxor 1 (getbit 2 x) (getbit 2 y))
                 1 (bvxor 1 (getbit 1 x) (getbit 1 y))
                 1 (bvxor 1 (getbit 0 x) (getbit 0 y)))))

;BOZO gen these!
(defthmd bvxor-7-bit-blast
  (equal (bvxor 7 x y)
         (bvcat2 1 (bvxor 1 (getbit 6 x) (getbit 6 y))
                 1 (bvxor 1 (getbit 5 x) (getbit 5 y))
                 1 (bvxor 1 (getbit 4 x) (getbit 4 y))
                 1 (bvxor 1 (getbit 3 x) (getbit 3 y))
                 1 (bvxor 1 (getbit 2 x) (getbit 2 y))
                 1 (bvxor 1 (getbit 1 x) (getbit 1 y))
                 1 (bvxor 1 (getbit 0 x) (getbit 0 y)))))

(defthmd bvand-8-bit-blast
  (equal (bvand 8 x y)
         (bvcat2 1 (bvand 1 (getbit 7 x) (getbit 7 y))
                 1 (bvand 1 (getbit 6 x) (getbit 6 y))
                 1 (bvand 1 (getbit 5 x) (getbit 5 y))
                 1 (bvand 1 (getbit 4 x) (getbit 4 y))
                 1 (bvand 1 (getbit 3 x) (getbit 3 y))
                 1 (bvand 1 (getbit 2 x) (getbit 2 y))
                 1 (bvand 1 (getbit 1 x) (getbit 1 y))
                 1 (bvand 1 (getbit 0 x) (getbit 0 y)))))

;bozo same for slice?  what other rules needed?
(defthm getbit-of-bvif-too-high
  (implies (and (<= size n)
                (natp n)
                (natp size))
           (equal (getbit n (bvif size test x y))
                  0))
  :hints (("Goal" :in-theory (enable bvif getbit-too-high))))

(defthm bvif-of-bvcat-arg2
  (implies (and (<= size lowsize)
                (natp size)
                (natp lowsize))
           (equal (bvif size test x (bvcat highsize highval lowsize lowval))
                  (bvif size test x lowval)))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm bvif-of-bvcat-arg1
  (implies (and (<= size lowsize)
                (natp size)
                (natp lowsize))
           (equal (bvif size test (bvcat highsize highval lowsize lowval) x)
                  (bvif size test lowval x)))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm bvif-of-bvcat-tighten-arg1
  (implies (and (< (+ highsize lowsize) size)
                (unsigned-byte-p (+ highsize lowsize) x)
                (natp size)
                (natp highsize)
                (natp lowsize)
                )
           (equal (bvif size test (bvcat highsize highval lowsize lowval) x)
                  (bvif (+ highsize lowsize) test (bvcat highsize highval lowsize lowval) x)))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm bvif-of-bvcat-tighten-arg2
  (implies (and (< (+ highsize lowsize) size)
                (unsigned-byte-p (+ highsize lowsize) x)
                (natp size)
                (natp highsize)
                (natp lowsize)
                )
           (equal (bvif size test x (bvcat highsize highval lowsize lowval))
                  (bvif (+ highsize lowsize) test x (bvcat highsize highval lowsize lowval))))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm slice-of-bvif-too-high
  (implies (and (<= n low)
                (natp low)
                (natp n))
           (equal (slice high low (bvif n test x y))
                  0))
  :hints (("Goal" :in-theory (enable BVIF myif SLICE-TOO-HIGH-IS-0))))

(defthm unsigned-byte-p-of-expt-2-n
  (implies (natp n)
           (unsigned-byte-p (+ 1 n) (expt 2 n)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p logapp))))

(defthm unsigned-byte-p-of-expt-2-n-gen
  (implies (and (<= (+ 1 n) m)
                (natp n)
                (natp m))
           (unsigned-byte-p m (expt 2 n)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p logapp))))

(defthm unsigned-byte-p-of-bvmult-from-bound
  (implies (and (< (* x y) (expt 2 n))
                (natp x)
                (natp y)
                (natp n))
           (unsigned-byte-p n (bvmult m x y)))
  :hints (("Goal" :in-theory (enable bvmult))))

(defthm bvplus-of-bvminus-same
  (implies (and (natp n)
                (integerp x)
                (integerp k2))
           (equal (bvplus n k2 (bvminus n x k2))
                  (bvchop n x)))
  :hints (("Goal" :in-theory (enable bvminus bvplus))))

;bozo analogue for bvand?
(defthm bitand-of-slice-arg1
  (implies (and (<= low high)
                (natp low)
                (natp high))
           (equal (bitand (slice high low x) y)
                  (bitand (getbit low x) y)))
  :hints (("Goal" :in-theory (enable bitand bvand))))

;bozo analogue for bvand?
(defthm bitand-of-slice-arg2
  (implies (and (<= low high)
                (natp low)
                (natp high))
           (equal (bitand y (slice high low x))
                  (bitand y (getbit low x))))
  :hints (("Goal" :in-theory (enable bitand bvand))))

(defthm logtail-of-logext
  (implies (and (natp size)
                (natp size2)
                (< size2 size))
           (equal (logtail size2 (logext size x))
                  (logext (- size size2) (slice (+ -1 size) size2 x))))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (e/d (logext bvchop-of-logtail slice)
                           (;anti-slice
;LOGEXT-OF-LOGTAIL-BECOMES-LOGEXT-OF-SLICE
;                                    BVCHOP-OF-LOGTAIL-BECOMES-SLICE ;bozo add to anit-slice?
                            bvchop-of-logtail-becomes-slice)))))

(defthm bitxor-commutative-alt
  (implies (syntaxp (smaller-bvxor-arg b a))
           (equal (bitxor a b)
                  (bitxor b a)))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable bitxor-commutative))))

(in-theory (disable bitxor-commutative))
(theory-invariant (incompatible (:rewrite bitxor-commutative) (:rewrite bitxor-commutative-alt)))

(defthm bitxor-commutative-2-alt
  (implies (syntaxp (smaller-bvxor-arg a b))
           (equal (bitxor b (bitxor a c))
                  (bitxor a (bitxor b c))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable bitxor-commutative-2))))

(in-theory (disable bitxor-commutative-2))
(theory-invariant (incompatible (:rewrite bitxor-commutative-2) (:rewrite bitxor-commutative-2-alt)))

;same for bitnot?
(defthm equal-bvnot-1-getbit-0
  (not (equal (bvnot 1 y) (getbit 0 y)))
  :hints (("Goal" :in-theory (e/d (bitnot bvnot-1-becomes-bitnot-better)
                                  (bitnot-becomes-bitxor-with-1 ;bozo
                                   )))))

;rewrite to have bitnot in lhs?
(defthm bitor-x-not-x
  (equal (bitor x (bvnot 1 x))
         1)
  :hints (("Goal" :cases ((equal (bvchop 1 x) 1)
                          (equal (bvchop 1 x) 0))
           :in-theory (e/d (bitor bvor
                                  getbit
                                  bitxor
                                  bvxor
                                  bitnot
                                  )
                           (bvchop-1-becomes-getbit
                            slice-becomes-getbit
                            bvxor-1-becomes-bitxor)))))

;rewrite to have bitnot in lhs?
(defthm bitor-x-not-x-alt
  (equal (bitor (bvnot 1 x) x)
         1)
  :hints (("Goal" :use (:instance bitor-x-not-x)
           :in-theory (disable bitor-x-not-x))))

;or go to bitnot
(defthm bitxor-x-not-x
   (equal (bitxor x (bvnot 1 x))
          1)
   :hints (("Goal" :in-theory (e/d (bitnot) (equal-of-0-and-bitxor)))))

(defthm bitxor-x-not-x-alt
   (equal (bitxor (bvnot 1 x) x)
          1)
   :hints (("Goal" :in-theory (enable bitnot))))

;bozo gen the 1 and eventually the bvnot
(defthm getbit-of-bvnot-too-high
  (equal (getbit 1 (bvnot 1 x))
         0)
  :hints (("Goal" :in-theory (enable bitnot))))

;this showed up in the unrolled aes spec
(defthm bvif-1-equal-1-y-x-bitxor-1-x
  (implies (unsigned-byte-p 1 y)
           (equal (bvif 1 (equal 1 y) x (bitxor 1 x))
                  (bitxor 1 (bitxor x y))))
  :hints (("Goal" :in-theory (enable bvif myif
                                     bitnot ;bozo
                                     ))))

(defthm bvif-1-equal-1-y-bitxor-1-x-x
  (implies (unsigned-byte-p 1 y)
           (equal (bvif 1 (equal 1 y) (bitxor 1 x) x)
                  (bitxor x y)))
  :hints (("Goal" :in-theory (enable bvif myif
                                     bitnot ;bozo
                                     ))))

(defthm bvif-1-equal-0-y-x-bitxor-1-x
  (implies (unsigned-byte-p 1 y)
           (equal (bvif 1 (equal 0 y) x (bitxor 1 x))
                  (bitxor x y)))
  :hints (("Goal" :in-theory (enable bvif myif
                                     bitnot ;bozo
                                     ))))

(defthm bvif-1-equal-0-y-bitxor-1-x-x
  (implies (unsigned-byte-p 1 y)
           (equal (bvif 1 (equal 0 y) (bitxor 1 x) x)
                  (bitxor 1 (bitxor x y))))
  :hints (("Goal" :in-theory (enable bvif myif
                                     bitnot ;bozo
                                     ))))

;might be nice to do this in 2 steps, but this might be faster?
(defthm bvnot-1-becomes-bitxor-1
  (implies (unsigned-byte-p 1 x)
           (equal (bvnot 1 x)
                  (bitxor 1 x)))
  :hints (("Goal" :cases ((equal 0 x))
           :in-theory (enable bitnot))))

(defthm bitor-x-bitxor-1-x
  (implies (unsigned-byte-p 1 x)
           (equal (bitor x (bitxor 1 x))
                  1))
  :hints (("Goal" :cases ((equal 0 x))
           :in-theory (enable bitnot))))

(in-theory (disable bvnot-1-becomes-bitxor-1)) ;fixme looped

(defthm bitor-x-bitxor-1-x-alt
  (implies (unsigned-byte-p 1 x)
           (equal (bitor (bitxor 1 x) x)
                  1))
  :hints (("Goal" :cases ((equal 0 x))
           :in-theory (enable bitnot))))

(theory-invariant (incompatible (:rewrite BITNOT-BECOMES-BITXOR-WITH-1) (:rewrite BITXOR-1)))

(defthmd bvuminus-becomes-flip-bits-and-add-one
  (implies (and (natp n)
                (integerp x))
           (equal (bvuminus n x)
                  (bvplus n 1 (bvnot n x))))
  :hints (("Goal" :in-theory (enable bvuminus bvminus bvplus bvnot lognot))))

(defthm bvif-equal-1-usb1-gen
  (implies (unsigned-byte-p 1 x)
           (equal (bvif 1 (equal 1 x) y 0)
                  (bitand x y)))
  :hints (("Goal" :in-theory (e/d (bvif myif bool-to-bit) ( bitnot-becomes-bitxor-with-1)))))

(defthm bvif-equal-1-usb1-2-gen
  (implies (unsigned-byte-p 1 x)
           (equal (bvif 1 (equal 1 x) 0 y)
                  (bitand y (bitnot x))))
  :hints (("Goal" :in-theory (e/d (bvif myif bool-to-bit) ( bitnot-becomes-bitxor-with-1)))))

(defthm bvand-of-logext
  (implies (and (<= size1 size2)
                (< 0 size2)
                (natp size1)
                (natp size2)
                ;(integerp x)
                ;(integerp y)
                )
           (equal (BVAND size1 (LOGEXT size2 x) y)
                  (BVAND size1 x y)))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bvand-of-logext-alt
  (implies (and (<= size1 size2)
                (< 0 size2)
                (natp size1)
                (natp size2)
                ;(integerp x)
                ;(integerp y)
                )
           (equal (BVAND size1 y (LOGEXT size2 x))
                  (BVAND size1 x y)))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm bitand-of-logext-arg2
  (implies (and (< 0 n) ;bozo would it be faster to write these as a single hyp since usually it will be executed?
                (integerp n))
           (equal (bitand x (logext n y))
                  (bitand x y)))
  :hints (("Goal" :in-theory (enable bitand))))

(defthm bitand-of-logext-arg1
  (implies (and (< 0 n) ;bozo would it be faster to write these as a single hyp since usually it will be executed?
                (integerp n))
           (equal (bitand (logext n y) x)
                  (bitand y x)))
  :hints (("Goal" :in-theory (enable bitand))))

(defthm bitxor-of-logext-arg2
  (implies (and (< 0 n) ;bozo would it be faster to write these as a single hyp since usually it will be executed?
                (integerp n))
           (equal (bitxor x (logext n y))
                  (bitxor x y)))
  :hints (("Goal" :in-theory (e/d (bitxor) (BVXOR-1-BECOMES-BITXOR)))))

(defthm bitxor-of-logext-arg1
  (implies (and (< 0 n) ;bozo would it be faster to write these as a single hyp since usually it will be executed?
                (integerp n))
           (equal (bitxor (logext n y) x)
                  (bitxor y x)))
  :hints (("Goal" :in-theory (e/d (bitxor) (BVXOR-1-BECOMES-BITXOR)))))

;fixme
(defthmd introduce-bvsx-25-7
  (equal (bvcat '25 (repeatbit '25 (getbit '7 x)) '7 x)
         (bvsx 32 8 x))
  :hints (("Goal" :in-theory (enable bvsx))))

;gen?
(defthm expt-combine-hack2
  (implies (integerp n)
           (equal (* (EXPT 2 N)
                     (/ (EXPT 2 (+ -1 N)))
                     x)
                  (* 2 x)))
  :hints (("Goal" :in-theory (enable expt-of-+))))

;drop the y?
(defthm additive-inverse-hack
  (implies (and (integerp x)
                (integerp y))
           (equal (+ y (- x) x)
                  y)))

(defthm bvchop-hack1
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (bvchop 32 (+ x (* 2 (bvchop 31 y))))
                  (bvchop 32 (+ x (* 2 y)))))
  :hints (("Goal" :use (;(:instance BVCHOP-+-BVCHOP (J (* 2 Y)) (I X) (SIZE 32))
                        ))))

(defthm bvchop-hack1b
 (implies (and (integerp x)
               (integerp y)
               (integerp z))
          (equal (bvchop 32 (+ x (* 2 (logext 31 y))))
                 (bvchop 32 (+ x (* 2 y)))))
 :hints (("Goal" :in-theory (disable)
          :use (;(:instance BVCHOP-+-BVCHOP (J (* 2 Y)) (I X) (SIZE 32))
                ))))

(defthm bvchop-times-logext
  (implies (and (<= size n)
                (integerp x)
                (integerp y)
                (integerp n))
           (equal (bvchop size (* (logext n x) y))
                  (bvchop size (* x y))))
  :hints (("Goal" :in-theory (disable bvchop-of-*-of-bvchop
                                      bvchop-times-cancel-better)
           :use ((:instance bvchop-times-cancel-better
                            (x (logext n x))
                            (m size))
                 (:instance bvchop-times-cancel-better
                            (x x)
                            (m size))))))

(defthm bvchop-times-logext-alt
  (implies (and (<= size n)
                (integerp x)
                (integerp y)
                (integerp n))
           (equal (BVCHOP size (* y (LOGEXT n x)))
                  (BVCHOP size (* y x))))
  :hints (("Goal" :use (:instance bvchop-times-logext)
           :in-theory (disable bvchop-times-logext))))

;this is basically about sign-extension
;bbozo gen!
(defthm high-slice-of-logext-31-7-8-hack
  (implies (integerp x)
           (equal (SLICE 31 7 (LOGEXT 8 X))
                  (repeatbit 25 (getbit 7 x))))
  :hints (("Goal" :in-theory (e/d (slice LOGEXT) ( BVCHOP-OF-LOGTAIL BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

;bozo move hyps to conclusion?
(defthm unsigned-byte-p-of-BVOR2
  (implies (and (unsigned-byte-p n a)
                (unsigned-byte-p n b)
                (natp n)
                (natp size)
                )
           (unsigned-byte-p n (BVOR size a b)))
  :hints (("Goal" :in-theory (enable BVOR))))

;kind of a weird rule..
(defthm unsigned-byte-p-of-BVOR3
  (implies (and (natp n)
                (< n size)
                (natp size)
                )
           (equal (unsigned-byte-p n (BVOR size a b))
                  (and (unsigned-byte-p n (bvchop size a))
                       (unsigned-byte-p n (bvchop size b)))))
  :hints (("Goal" :in-theory (enable BVOR))))

(defthm high-slice-of-logext-31-7-8
  (implies (integerp x)
           (equal (slice 31 7 (logext 8 x))
                  (bvsx 25 1 (getbit 7 x))))
  :hints (("Goal" :in-theory (e/d (slice LOGEXT) (BVCHOP-OF-LOGTAIL-BECOMES-SLICE BVCHOP-OF-LOGTAIL)))))

;fixme
(defthm bvchop-32-logext-8
  (implies (integerp x)
           (equal (bvchop 32 (logext 8 x))
                  (bvsx 32 8 x)))
  :hints (("Goal" :in-theory (enable bvsx))))

;; ;bozo gen
(defthm bvplus-of-logext-arg1-32-8
  (implies (integerp y)
           (equal (bvplus 32 (logext 8 y) x)
                  (bvplus 32 (bvsx 32 8 y)
                          x
                          )))
  :hints (("Goal" :in-theory (enable bvplus bvsx))))

(defthm unsigned-byte-p-pow2-hack
  (implies (and (integerp high)
                (integerp low)
                (<= low high)
                )
           (UNSIGNED-BYTE-P (+ 1 HIGH (- LOW))
                            (+ -1
                               (* 2 (EXPT 2 HIGH) (/ (EXPT 2 LOW))))))

  :hints (("Goal"
;           :use (:instance EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1 (r 2) (i 0) (j (+ 1 high (- low))))
           :in-theory (e/d (UNSIGNED-BYTE-P expt-of-+) (;EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1
                                              ;EXPONENTS-ADD
                                              )))))

(defthm high-slice-of-logext
  (implies (and (<= (+ -1 n) low)
                (posp n)
                (natp low)
                (integerp high))
           (equal (slice high low (logext n x))
                  (bvsx (+ 1 high (- low))
                        1
                        (getbit (+ -1 n) x))))
  :hints (("Goal" :in-theory (e/d (slice logext repeatbit bvsx) (BVCHOP-OF-LOGTAIL-BECOMES-SLICE BVCHOP-OF-LOGTAIL)))))

;BOZO do this for all ops
(defthm bvminus-bound-2
  (implies (and (<= (expt 2 size) k)
                (natp size))
           (< (bvminus size x y) k))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-bvminus-gen-better (size size) (size1 size) (i x) (j y))
           :in-theory (disable unsigned-byte-p-of-bvminus-gen-better))))

(defthm bvminus-becomes-bvplus-of-bvuminus
;;   (implies (and ;(natp size)
;; ;                (integerp x)
;; ;               (integerp y)
;;                 )
           (equal (bvminus size x y)
                  (bvplus size x (bvuminus size y))
                  ;)
                  )
  :hints (("Goal" :cases ((natp size))
           :in-theory (e/d (natp bvminus bvplus bvuminus) (bvchop-of-minus  BVCHOP-WHEN-I-IS-NOT-AN-INTEGER)))))

(in-theory (disable bvuminus)) ;move up
(theory-invariant (incompatible (:rewrite bvminus-becomes-bvplus-of-bvuminus) (:definition bvuminus)))

(defthm bvuminus-of-bvplus
  (equal (bvuminus size (bvplus size x y))
         (bvplus size (bvuminus size x) (bvuminus size y)))
  :hints (("Goal" :in-theory (e/d (bvuminus bvplus bvminus)
                                  (bvminus-becomes-bvplus-of-bvuminus
                                   BVCHOP-OF-MINUS ;bozo
                                   )))))

(defthm bvminus-1-0
  (implies (unsigned-byte-p 1 x) ;drop
           (equal (bvminus 1 0 x)
                  (getbit 0 x)))
  :hints (("Goal" :cases ((equal 0 x) (equal 1 x))
           :in-theory (e/d (bvminus getbit bvchop-when-i-is-not-an-integer)
                           (bvchop-1-becomes-getbit slice-becomes-getbit)))))


(defthm bvuminus-1
  (equal (bvuminus 1 x)
         (getbit 0 x))
  :hints (("Goal" :cases ((equal 0 x) (equal 1 x))
           :in-theory (e/d (bvminus bvuminus getbit)
                           (bvchop-1-becomes-getbit
                            slice-becomes-getbit BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

(defthm getbit-too-high-cheap-free
  (implies (and (unsigned-byte-p free x) ;free variable
                (<= free n)
                (natp free)
                (integerp n))
           (equal (getbit n x)
                  0))
  :hints (("Goal" :use (:instance getbit-too-high))))

;bozo
(defthm natp-32-bvminus-5
  (natp (+ 32 (- (bvminus 5 0 amt))))
  :hints (("Goal" :in-theory (e/d (bvminus)( BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))


;; for des encrypt:

;drop these?
(defthm bvor-disjoint-ones-arg2
  (implies (and (< size2 size)
                (equal 0 (bvchop size2 x))
                (natp size)
                (natp size2))
           (equal (bvor size x (bvchop size2 y)) ;bozo gen the bvchop
                  (bvcat (- size size2) (slice (+ -1 size) size2 x) size2 y)))
  :hints (("Goal" :in-theory (enable BVOR))))

;drop these?
(defthm bvor-disjoint-ones-arg1
  (implies (and (< size2 size)
                (equal 0 (bvchop size2 x))
                (natp size)
                (natp size2))
           (equal (bvor size (bvchop size2 y) x) ;bozo gen the bvchop
                  (bvcat (- size size2) (slice (+ -1 size) size2 x) size2 y)))
  :hints (("Goal" :in-theory (enable BVOR))))

(defthm bound-when-usb2
  (implies (and (unsigned-byte-p n x) ;n is a free variable
                (<= (expt 2 n) k)
                (integerp k)
                (natp n))
           (< x k)))

(defthm bvplus-of-bvuminus-same-2
  (implies (natp size)
           (equal (bvplus size x (bvplus size (bvuminus size x) y))
                  (bvchop size y)))
  :hints (("Goal" :in-theory (e/d (bvplus bvminus bvuminus bvchop-when-i-is-not-an-integer)
                                  (bvminus-becomes-bvplus-of-bvuminus bvchop-of-minus)))))

(defthm bvplus-of-bvuminus-same-2-alt
  (implies (natp size)
           (equal (bvplus size (bvuminus size x) (bvplus size x y))
                  (bvchop size y)))
  :hints (("Goal" :use (:instance bvplus-of-bvuminus-same-2)
           :in-theory (disable bvplus-of-bvuminus-same-2))))

;stuff for rc6 recursive equivalence proof

;bozo or just use SLICE-TOO-HIGH-IS-0 - which is cheaper?
;or just pass slice through?
(defthm slice-of-bvxor-too-high
  (implies (and (<= n low)
                (integerp low)
                (natp n))
           (equal (slice high low (bvxor n x y))
                  0))
  :hints (("Goal" :in-theory (enable slice-too-high-is-0))))

(defthm slice-of-bvand-too-high
  (implies (and (<= n low)
                (integerp low)
                (natp n))
           (equal (slice high low (bvand n x y))
                  0))
  :hints (("Goal" :in-theory (enable slice-too-high-is-0))))

;drop?
(defthmd slice-8-0-bvxor-9
  (equal (slice 8 0 (bvxor 9 x y))
         (bvxor 9 x y))
  :hints (("Goal" :in-theory (disable ;hide-bvxor
                              )))  )

;how does logtail even get introduced?
;bbozo
;drop or gen
(defthm get-rid-of-logtail
  (equal (logtail 7 (bvcat 8 x 24 y))
         (bvcat 8 x 17 (slice 23 7 y)))
  :hints (("Goal" :in-theory (disable))))

(defthm bvor-of-logext-1
  (implies (and (integerp size)
                (< 0 size)
                (integerp x)
                (integerp y))
           (equal (bvor size (logext size x) y)
                  (bvor size x y)))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-of-logext-2
  (implies (and (integerp size)
                (< 0 size)
                (integerp x)
                (integerp y))
           (equal (bvor size y (logext size x))
                  (bvor size y x)))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-of-logext
  (implies (and (<= size size2)
                (natp size2)
                (natp size)
;                (integerp x)
                ;(integerp y)
                )
           (equal (bvor size x (logext size2 y))
                  (bvor size x y)))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm bvor-of-logext-2-gen
  (implies (and (<= size size2)
                (natp size2)
                (natp size)
                ;(integerp x)
                ;(integerp y)
                )
           (equal (bvor size (logext size2 y) x)
                  (bvor size y x)))
  :hints (("Goal" :in-theory (enable bvor))))

;gen!
(defthm bvand-128-hack
  (implies (integerp x)
           (equal (bvand 8 128 x)
                  (bvcat 1 (getbit 7 x) 7 0))))

;what if the some bits of the slice get thrown away?
(defthm slice-of-bvif
  (implies (and; (<= size (+ 1 high (- low))) ;bozo
                (< high size)
                (<= low high)
                (natp size)
                (natp high)
                (natp low))
           (equal (slice high low (bvif size test a b))
                  (bvif size test (slice high low a) (slice high low b))))
  :hints (("Goal" :in-theory (enable bvif myif))))

;bbozo gen
(defthm usb-33-of-one-more
  (implies (and (< 0 x)
                (unsigned-BYTE-P '33 X))
           (unsigned-BYTE-P '33 (+ '-1 X)))
  :hints (("Goal" :in-theory (enable unsigned-BYTE-P))))

;bbozo gen
(defthm sbp-32-when-non-neg
  (implies (<= 0 x)
           (equal (signed-byte-p 32 x)
                  (unsigned-byte-p 31 x)))
  :hints (("Goal" :in-theory (enable signed-byte-p unsigned-byte-p))))

;bozo gen
(defthm getbit-33-of-minus-1
  (implies (and (signed-byte-p 32 x)
                (< 0 x))
           (equal (getbit 33 (+ -1 x))
                  0))
  :hints (("Goal" :in-theory (enable getbit-too-high))))

(defthm usb-of-one-more-when-usb
  (implies (UNSIGNED-BYTE-P 31 x)
           (equal (UNSIGNED-BYTE-P 31 (+ 1 x))
                  (not (equal x #x7fffffff))))
  :hints (("Goal" :in-theory (enable UNSIGNED-BYTE-P))))

;logapp-equal-rewrite and equal-*-/-2 seemed to loop
;bozo gen
(defthm truncate-4-hack
  (implies (natp x)
           (equal (truncate x 4)
                  (logtail 2 x)))
  :hints (("Goal" :in-theory (enable truncate logtail ifloor floor))))

;bozo when exactly do we want to do this? whenever the thing being shifted is a bit vector function?
;see rule fro slice below, we use the size info...
(defthm times-4-becomes-logapp
  (implies (natp x)
           (equal (* 4 (LOGTAIL n x))
                  (logapp 2 0 (logtail n x))))
  :hints (("Goal" :in-theory (enable logapp))))

(defthm times-4-of-slice-becomes-logapp
  (implies (and (natp x)
                (<= low high) ;bozo
                (natp high)
                (natp low))
           (equal (* 4 (slice high low x))
                  (bvcat (+ high 1 (- low)) (slice high low x) 2 0)))
  :hints (("Goal" :in-theory (e/d (logapp bvcat) ()))))

;I don't think this is needed now, because of the built in rule SIGNED-BYTE-P-FORWARD-TO-INTEGERP
;; (defthm sbp-forward-to-integerp
;;   (implies (signed-byte-p n x)
;;            (integerp x))
;;   :rule-classes (;(:type-prescription)
;;                  (:forward-chaining :match-free :all)))

(defthm bvor-of-bvcat-appending-idiom
  (implies (and (equal k (+ m n)) ;gen?
                (unsigned-byte-p n y)
                (<= 0 n)
                (integerp n)
                (natp m)
                (< 0 m)
                ;(integerp x)
                ;(integerp y)
                )
           (equal (bvor k (bvcat m x n 0) y)
                  (bvcat m x n y)))
  :hints (("Goal" :in-theory (e/d (SLICE-TOO-HIGH-IS-0) (SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE)))))

(defthm bvor-of-bvcat-appending-idiom-alt
  (implies (and (equal k (+ m n))
                (unsigned-byte-p n y)
                (<= 0 n)
                (integerp n)
                (natp m)
                (< 0 m))
           (equal (bvor k y (bvcat m x n 0))
                  (bvcat m x n y)))
  :hints (("Goal" :use (:instance bvor-of-bvcat-appending-idiom)
           :in-theory (e/d (;natp
                            ) ( bvor-of-bvcat-appending-idiom)))))

;BOZO gen this series...
(defthm bvand-64-hack
  (implies (and (integerp x)
                (< 6 n)
                (natp n))
           (equal (bvand n 64 x)
                  (bvcat
                   1 (getbit 6 x) 6 0
                   ))))

(defthm bvand-32-hack
  (implies (and (integerp x)
                (< 5 n)
                (natp n))
           (equal (bvand n 32 x)
                  (bvcat
                   1 (getbit 5 x) 5 0
                   ))))

(defthm bvand-16-hack
  (implies (and (integerp x)
                (< 4 n)
                (natp n))
           (equal (bvand n 16 x)
                  (bvcat
                           1 (getbit 4 x) 4 0
                           ))))

(defthm bvand-8-hack
  (implies (and (integerp x)
                (< 3 n)
                (natp n))
           (equal (bvand n 8 x)
                  (bvcat
                           1 (getbit 3 x) 3 0
                           ))))

(defthm bvand-4-hack
  (implies (and (integerp x)
                (< 2 n)
                (natp n))
           (equal (bvand n 4 x)
                  (bvcat
                           1 (getbit 2 x) 2 0
                           ))))

(defthm bvand-2-hack
  (implies (and (integerp x)
                (< 1 n)
                (natp n))
           (equal (bvand n 2 x)
                  (bvcat
                           1 (getbit 1 x) 1 0
                           ))))

;gen?
(defthm bvor-large-of-getbit
  (implies (and (integerp y) ;bozo
                (< 1 m)
                (natp m))
           (equal (bvor m (getbit n x) ;gen
                        y)
                  (bvcat
                   (+ -1 m) (slice (+ -1 m) 1 y) 1 (bvor 1 (getbit n x) (getbit 0 y))))))



;make an -alt version?
(defthm bvor-of-bvcat-and-bvcat-constant-version
  (implies (and (syntaxp (and (quotep j) (quotep k)))
                (< lowsize2 lowsize1)
                (<= (+ 1 lowsize1) n) ;bozo
                (natp n)
                (natp lowsize1)
                (natp lowsize2)
                )
           (equal (bvor n
                        (bvcat 1 x lowsize1 j)
                        (bvcat 1 y lowsize2 k))
                  (bvcat (- n lowsize2)
                         (bvor (- n lowsize2)
                               (bvcat 1 x (- lowsize1 lowsize2) (slice (+ -1 lowsize1) lowsize2 j))
                               (bvchop 1 y))
                         lowsize2
                         (bvor lowsize2 j k)))))

(defthm bvor-of-bvcat-and-bvcat-constant-version-alt
  (implies (and (syntaxp (and (quotep j) (quotep k)))
                (< lowsize2 lowsize1)
                (<= (+ 1 lowsize1) n) ;bozo
                (natp n)
                (natp lowsize1)
                (natp lowsize2)
                )
           (equal (bvor n
                           (bvcat 1 y lowsize2 k)
                           (bvcat 1 x lowsize1 j))
                  (bvcat (- n lowsize2)
                         (bvor (- n lowsize2)
                                  (bvcat 1 x (- lowsize1 lowsize2) (slice (+ -1 lowsize1) lowsize2 j))
                                  (bvchop 1 y))
                         lowsize2
                         (bvor lowsize2 j k)))))

(defthm bvand-with-256
  (implies (and (integerp x)
                (natp n)
                (<= 9 n))
           (equal (BVAND n 256 x)
                  (bvcat 1 (getbit 8 x)
                         8 0))))



;reduces the number of mentions of x
;BOZO prove more like this
(defthm bvif-of-bvxor-same
  (implies (and (natp n)
                (< 0 n))
           (equal (BVIF n test (BVXOR n k x) x)
                  (bvxor n (bvif n test k 0) x)))
  :hints (("Goal" :in-theory (enable bvif myif))))

;this does increase the number of mentions of test, but I hope the test will often be small
;helps for AESLightEngine2.inv_mcol.lisp
(defthm bvif-of-bvcat-bvcat
  (implies (and (equal size (+ lowsize highsize))
                (natp highsize)
                (natp lowsize))
           (equal (bvif size test (bvcat highsize highval1 lowsize lowval1)  (bvcat highsize highval2 lowsize lowval2))
                  (bvcat highsize
                         (bvif size test highval1 highval2)
                         lowsize
                         (bvif size test lowval1 lowval2))))
  :hints (("Goal" :in-theory (enable bvif myif))))

;just moved this- hope that's ok
;reiterating this here so it fires before getbit-indentity
;; weird loop:
;; we have a rule that put a bvchop 1 around a bvchop 3 (because the bvchop 3 was in a 1-bit field of a bvcat)
;; but the bvchop 1 became a getbit 1 which then went away due to getbit-identity (because apparently we could prove that the argument was a usb 1).   bvchop identity must be off... - or maybe not!
;; so to prevent this we want GETBIT-OF-BVCHOP to fire before GETBIT-identity, i guess.
;; yeah, for speed, we probably want slow rules like that to be tried later any way - how much speed can we gain by reordering rules? -- DOES HAVING TRIM FIX ALL THIS?

;; (defthm getbit-of-bvchop2
;;   (implies (and (< m n)
;;                 (integerp m)
;;                 (<= 0 m)
;;                 (integerp n))
;;            (equal (getbit m (bvchop n x))
;;                   (getbit m x))))

(defthm logext-of-logtail-becomes-logext-of-slice
  (implies (and (natp size1)
                (< 0 size1)
                (natp size2)
                )
           (equal (logext size1 (logtail size2 x))
                  (logext size1 (slice (+ -1 size1 size2) size2 x))))
  :hints
  (("Goal" :in-theory (e/d (slice logtail-of-bvchop) (slice-becomes-bvchop bvchop-of-logtail logext-of-logtail BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))


;bozo gen to any usb1
(defthm bvmult-of-getbit
  (implies (and (integerp k)
                (natp size))
           (equal (BVMULT size k (GETBIT n x))
                  (bvif size (equal 1 (getbit n x))
                         k
                         0)))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm bvplus-of-logext
  (implies (and; (integerp x) ;bozo
                (natp n)
                ;(integerp y)
                )
           (equal (bvplus n x (logext n y))
                  (bvplus n x y)))
  :hints (("Goal"
           :cases ((integerp x))
           :in-theory (enable bvplus bvchop-when-i-is-not-an-integer))))

(defthm bvplus-of-logext-arg1
  (implies (and ; (integerp x) ;bozo
            (natp n)
     ;(integerp y)
            )
           (equal (bvplus n (logext n y) x)
                  (bvplus n y x)))
  :hints (("Goal" :use (:instance bvplus-of-logext)
           :in-theory (disable bvplus-of-logext))))

(defthm slice-of-repeatbit
   (implies (and (< high size)
                 (<= low high)
                 (natp low)
                 (natp high)
                 (natp size))
            (equal (slice high low (repeatbit size bit))
                   (repeatbit (+ 1 high (- low)) bit)))
   :hints (("Goal" :do-not '(preprocess)
            :use (:instance BVCHOP-OF-MASK-OTHER
                            (size2 (+ 1 HIGH (- LOW)))
                            (size1 (- size low))
                            )
            :in-theory (e/d (repeatbit slice
                             ;bvplus bvchop logtail
                                       )
                            (;anti-slice BVPLUS-RECOLLAPSE
                             BVCHOP-OF-LOGTAIL-BECOMES-SLICE
                             BVCHOP-OF-MASK-OTHER
                                        )))))

(defthm bvchop-hack1b2
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (bvchop 32 (+ x (* 2 z (logext 31 y))))
                  (bvchop 32 (+ x (* 2 z y))))))

(defthm bvchop-hack2
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (SLICE 31 27 (+ x (* 2 y (BVCHOP 31 z))))
                  (SLICE 31 27 (+ x (* 2 y z))))))

(defthm bvchop-hack3
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (SLICE 31 27 (+ x (* 2 y (LOGext 31 z))))
                  (SLICE 31 27 (+ x (* 2 y z)))))
)

(defthm gross-helper
  (implies (and (equal (bvchop 32 x)
                       (bvchop 32 y))
                (natp k))
           (equal (equal (slice 26 k x)
                         (slice 26 k y))
                  t))
  :hints (("Goal" :use ((:instance SLICE-OF-BVCHOP-LOW (X X) (N 32) (LOW K) (HIGH 26))
                        (:instance SLICE-OF-BVCHOP-LOW (X y) (N 32) (LOW K) (HIGH 26)))
           :in-theory (disable SLICE-OF-BVCHOP-LOW SLICE-OF-BVCHOP-LOW-GEN))))

(defthm slice-logext-lemma
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (natp k))
           (equal (SLICE 26 k (+ x (* 2 y (LOGEXT 31 z))))
                  (SLICE 26 k (+ x (* 2 y z))))))

;FIXME gen or drop
(defthm slice-linear-31-27
  (<= (slice 31 27 x)
      31)
  :rule-classes :linear)

(defthm sbp-ubp-hack
  (implies (unsigned-byte-p 31 x)
           (signed-byte-p 32 (+ -1 x)))
  :hints (("Goal" :in-theory (enable signed-byte-p unsigned-byte-p))))

;make a version with x a constant
(defthm <-of-constant-and-bvcat-with-low-constant
  (implies (and (syntaxp (and (quotep k1) (quotep k2) (quotep lowsize)))
                (natp highsize)
                (natp lowsize)
                (rationalp k1)
                (rationalp k2))
           (equal (< k1 (bvcat highsize x lowsize k2))
                  (< (/ (- k1 (bvchop lowsize k2)) (expt 2 lowsize)) ;this gets computed
                     (bvchop highsize x))))
  :hints (("Goal" :in-theory (e/d (bvcat logapp bvchop)
                                  (;<-*-left-cancel
                                   ))
           ;; :use (:instance <-*-left-cancel
           ;;                 (x (* (/ (expt 2 lowsize)) k1))
           ;;                 (y (+ (bvchop highsize x) (* (/ (expt 2 lowsize)) k2)))
           ;;                 (z (expt 2 lowsize))
           ;;                 )
           )))

(defthm <-of-bvcat-with-low-constant-and-constant
  (implies (and (syntaxp (and (quotep k1) (quotep k2) (quotep lowsize)))
                (natp highsize)
                (natp lowsize)
                (rationalp k1)
                (rationalp k2))
           (equal (< (bvcat highsize x lowsize k2) k1)
                  (< (bvchop highsize x)
;this gets computed:
                     (/ (- k1 (bvchop lowsize k2)) (expt 2 lowsize)))))
  :hints (("Goal" :in-theory (e/d (bvcat logapp bvchop)
                                  (;<-*-left-cancel
                                   ))
           ;; :use (:instance <-*-left-cancel
           ;;                 (y (+ (* K1 (/ (EXPT 2 LOWSIZE)))
           ;;                       (- (* (/ (EXPT 2 LOWSIZE))
           ;;                             (BVCHOP LOWSIZE K2)))))
           ;;                 (x (BVCHOP HIGHSIZE X))
           ;;                 (z (expt 2 lowsize))
           ;;                 )
           )))





(defthm signed-byte-p-of-myif
  (implies (and (signed-byte-p n a)
                (signed-byte-p n b))
           (signed-byte-p n (myif test a b)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm logxor-myif-hack
  (implies (and (integerp a)
                (integerp b)
                (integerp c))
           (equal (logxor (myif test1 a b) (myif test2 a b) c)
                  (logxor (myif (boolxor test1 test2) (logxor a b) 0) c)))
  :hints (("Goal" :in-theory (enable myif boolxor))))

(defthm logxor-myif-hack-2
  (implies (and (integerp a)
                (integerp b))
           (equal (logxor (myif test1 a b) (myif test2 a b))
                  (myif (boolxor test1 test2) (logxor a b) 0)))
  :hints (("Goal" :in-theory (enable myif boolxor))))

;gross proof?
(defthm not-unsigned-byte-p-of-one-less-than-integer-length
  (not (unsigned-byte-p (+ -1 (integer-length k)) k))
  :hints (("Goal" :in-theory (enable unsigned-byte-p integer-length))))

(defthm getbit-of-one-less-than-integer-length
  (implies (posp k)
           (equal (getbit (+ -1 (integer-length k)) k)
                  1))
  :hints (("Goal" :in-theory (e/d (getbit slice) ( slice-becomes-getbit bvchop-1-becomes-getbit
                                                                    logtail-of-bvchop-becomes-slice
                                                                    bvchop-of-logtail-becomes-slice)))))

(defthm bvand-of-expt
  (implies (and (equal k (expt 2 (+ -1 (integer-length k)))) ;check for power-of-2
                (<= (integer-length k) size)
                (natp size)
                (natp k))
           (equal (bvand size k x)
                  (bvcat 1
                         (getbit (+ -1 (integer-length k)) x)
                         (+ -1 (integer-length k))
                         0))))

;make a bvxor version
;subsumes the versions for 0 and 1
;the remaining 1 here isn't too bad, since 0 will be dropped and anything else will be trimmed
(defthm equal-of-constant-and-bitxor-1
  (implies (syntaxp (quotep k))
           (equal (equal k (bitxor 1 x))
                  (and (unsigned-byte-p 1 k)
                       (equal (getbit 0 x) (bitnot k)))))
  :hints (("Goal"
           :cases ((equal 0 (GETBIT 0 X))
                   (equal 1 (GETBIT 0 X)))
           :in-theory (e/d (bitnot-becomes-bitxor-with-1)
                           (BITXOR-OF-1-BECOMES-BITNOT-ARG1 bvxor-1-becomes-bitxor)))))

(defthm equal-of-bvmult-and-*
  (implies (and (integerp x)
                (integerp y)
                (natp size))
           (equal (equal (bvmult size x y) (binary-* x y))
                  (unsigned-byte-p size (binary-* x y))))
  :hints (("Goal" :in-theory (enable bvmult))))

(defthm equal-of-bvmult-and-*-alt
  (implies (and (integerp x)
                (integerp y)
                (natp size))
           (equal (equal (binary-* x y) (bvmult size x y))
                  (unsigned-byte-p size (binary-* x y))))
  :hints (("Goal" :in-theory (enable bvmult))))

;move
(defthmd bvchop-of-*
  (implies (and (integerp x)
                (integerp y))
           (equal (bvchop size (binary-* x y))
                  (bvmult size x y)))
  :hints (("Goal" :in-theory (enable bvmult))))

(theory-invariant (incompatible (:rewrite bvchop-of-*) (:definition bvmult)))

;gen one of the sizes
(defthm bvmult-of-expt
  (implies (natp size)
           (equal (bvmult size (expt 2 size) x)
                  0))
  :hints (("Goal" :in-theory (e/d (bvmult) (bvchop-of-*)))))

(defthm bvmult-of-expt-alt
  (implies (natp size)
           (equal (bvmult size x (expt 2 size))
                  0))
  :hints (("Goal" :use (:instance bvmult-of-expt)
           :in-theory (disable bvmult-of-expt))))




;fixme use GETBIT-WHEN-NOT-0 instead of the cases rule?

;don't need if we have polarity?
(defthm bitxor-subst-arg2-one-version
  (implies (and (not (equal (getbit 0 x) free)) ;we expect free to be 0
                (syntaxp (equal free ''0))
                (equal 0 free))
           (equal (bitxor y x)
                  (bitxor y 1)))
  :hints (("Goal" :in-theory (enable bitxor-split))))

;don't need if we have polarity?
(defthm bitxor-subst-arg1-one-version
  (implies (and (not (equal (getbit 0 x) free)) ;we expect free to be 0
                (syntaxp (equal free ''0))
                (equal 0 free))
           (equal (bitxor x y)
                  (bitxor 1 y)))
  :hints (("Goal" :use (:instance bitxor-subst-arg2-one-version))))

(defthm bvchop-of-lognot-all-ones
  (implies (natp n)
           (equal (bvchop n (lognot (+ -1 (expt 2 n))))
                  0))
  :hints (("Goal" :in-theory (enable lognot))))

(defthmd expt-move-hack
  (equal (equal (expt 2 y)
                (* 2 x))
         (equal (* 1/2 (expt 2 y))
                x)))

;drop the y?
(defthm collect-hack ;bozo gen
  (equal (+ y (* 1/2 x) (* 1/2 x))
         (+ y x)))

;rename
;also a 0-1 rule?
(defthm bvif-1-1-0
  (implies (posp size)
           (equal (bvif size test 1 0)
                  (bool-to-bit test)))
  :hints (("Goal" :in-theory (enable bvif BOOL-TO-BIT))))

;this is for powers of 2 (nicer theorem because we don't have to worry about the product getting chopped
;(chopping a number doesn't change whether it's a multiple of a small power of 2)
(defthm bvmod-of-bvmult-of-expt
  (implies (and (posp n)
                (natp size)
                (integerp x))
           (equal (bvmod size (bvmult size (expt 2 n) x) (expt 2 n))
                  0))
  :hints (("Goal" :in-theory (e/d (bvmult bvmod)
                                  (BVCHOP-OF-*
                                   ;BVLT-OF-*-ARG3
                                   ;*-OF-2-BECOMES-BVMULT
                                   ;MOD-BECOMES-BVMOD-BETTER
                                   )))))

(defthm bvmod-of-bvmult-of-expt-constant-version
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                (posp k) ;;)(natp k) ?
                (natp size))
           (equal (bvmod size (bvmult size k x) k)
                  0))
  :hints (("Goal"
;           :cases ((equal 0 k) (not (integerp k)))
           :use (:instance bvmod-of-bvmult-of-expt (n (lg k)))
           :in-theory (disable bvmod-of-bvmult-of-expt
                               mod-=-0
                               ))))

;move this stuff?
(defthm unsigned-byte-p-forced-of-bvchop
  (equal (unsigned-byte-p-forced size (bvchop size x))
         (natp size))
  :hints (("Goal"
           :in-theory (enable bvchop-when-i-is-not-an-integer natp)
           :cases ((integerp size)))))

(defthm unsigned-byte-p-forced-of-bvand
  (equal (unsigned-byte-p-forced size (bvand size x y))
         (natp size))
  :hints (("Goal" :in-theory (enable bvand))))

(defthm unsigned-byte-p-forced-of-bvor
  (equal (unsigned-byte-p-forced size (bvor size x y))
         (natp size))
  :hints (("Goal" :in-theory (enable bvor))))

(defthm unsigned-byte-p-forced-of-bvxor
  (equal (unsigned-byte-p-forced size (bvxor size x y))
         (natp size))
  :hints (("Goal" :in-theory (enable bvxor))))

(defthm unsigned-byte-p-forced-of-bvnot
  (equal (unsigned-byte-p-forced size (bvnot size x))
         (natp size))
  :hints (("Goal" :in-theory (enable bvnot))))

(defthm unsigned-byte-p-forced-of-bvplus
  (equal (unsigned-byte-p-forced size (bvplus size x y))
         (natp size))
  :hints (("Goal" :in-theory (enable bvplus natp))))

(defthm unsigned-byte-p-forced-of-bvmult
  (equal (unsigned-byte-p-forced size (bvmult size x y))
         (natp size))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced natp))))

(defthm unsigned-byte-p-forced-of-bvdiv
  (equal (unsigned-byte-p-forced size (bvdiv size x y))
         (natp size))
  :hints (("Goal" :in-theory (enable bvdiv natp))))

(defthm unsigned-byte-p-forced-of-bvmod
  (equal (unsigned-byte-p-forced size (bvmod size x y))
         (natp size))
  :hints (("Goal" :in-theory (enable bvmod natp))))

(defthm unsigned-byte-p-forced-of-bvminus
  (equal (unsigned-byte-p-forced size (bvminus size x y))
         (natp size))
  :hints (("Goal" :in-theory (enable bvminus))))

(defthm unsigned-byte-p-forced-of-bvuminus
  (equal (unsigned-byte-p-forced size (bvuminus size x))
         (natp size))
  :hints (("Goal" :in-theory (e/d (bvuminus) (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

(defthm unsigned-byte-p-forced-of-bvif
  (equal (unsigned-byte-p-forced size (bvif size test x y))
         (natp size))
  :hints (("Goal" :in-theory (enable bvif))))

(defthm unsigned-byte-p-forced-of-if
  (equal (unsigned-byte-p-forced size (if test x y))
         (if test
             (unsigned-byte-p-forced size x)
           (unsigned-byte-p-forced size y))))

(defthm unsigned-byte-p-forced-of-slice
  (implies (and (equal size (+ 1 high (- low)))
                (integerp low)
                (integerp high))
           (equal (unsigned-byte-p-forced size (slice high low x))
                  (natp size)))
  :hints (("Goal"
           :in-theory (enable SLICE-OUT-OF-ORDER natp)
           :cases ((integerp size)))))

(defthm unsigned-byte-p-forced-of-bvcat
  (implies (and (equal size (+ highsize lowsize))
                (natp lowsize)
                (natp highsize))
           (unsigned-byte-p-forced size (bvcat highsize highval lowsize lowval)))
  :hints (("Goal"
           :in-theory (enable SLICE-OUT-OF-ORDER natp)
           :cases ((integerp size)))))

;will we really be trimming a 1-bit quantitiy down to 0 bits? maybe the trim rule can be simplified and sped up. fixme
(defthm unsigned-byte-p-forced-of-getbit
  (unsigned-byte-p-forced 1 (getbit n x)))

(defthm unsigned-byte-p-forced-of-bitnot
  (unsigned-byte-p-forced 1 (bitnot x)))

(defthm unsigned-byte-p-forced-of-bitor
  (unsigned-byte-p-forced 1 (bitor x y)))

(defthm unsigned-byte-p-forced-of-bitxor
  (unsigned-byte-p-forced 1 (bitxor x y)))

(defthm unsigned-byte-p-forced-of-bitand
  (unsigned-byte-p-forced 1 (bitand x y)))

(defthm unsigned-byte-p-forced-of-bvsx
  (implies (and (posp oldsize) ;gen?
                (<= oldsize size)
                (natp size))
           (unsigned-byte-p-forced size (bvsx size oldsize x)))
  :hints (("Goal" :cases ((equal 0 size))
           :in-theory (enable unsigned-byte-p-forced bvsx))))

;we want this disabled for user proofs but not for library proofs.... hm...
;fixme add the rest of the unsigned-byte-p-forced rules!
(in-theory (disable unsigned-byte-p-forced))

;justifies adding unsigned-byte-p-forced to the list of known predicates
(defthm booleanp-of-unsigned-byte-p-forced
  (booleanp (unsigned-byte-p-forced size x)))

;; ;not true?
;; (defthm bvchop-of-bvdiv2
;;   (implies (and (<= size1 size2)
;;                 (natp size2)
;;                 (natp size1))
;;            (equal (bvchop size1 (bvdiv size2 x y))
;;                   (bvdiv size1 x y)))
;;   :hints (("Goal" :in-theory (enable bvdiv))))

;; ;not true?
;; (defthm trim-of-bvdiv
;;   (implies (and (<= size1 size2)
;;                 (natp size2)
;;                 (natp size1))
;;            (equal (trim size1 (bvdiv size2 x y))
;;                   (bvdiv size1 x y)))
;;   :hints (("Goal" :in-theory (enable))))


(defthmd logtail-becomes-slice-bind-free
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize x) (newsize))
                (integerp newsize)
                (unsigned-byte-p-forced newsize x)
                (natp n)
                (<= n newsize)
                )
           (equal (logtail n x)
                  (slice (+ -1 newsize) n x)))
  :hints (("Goal" :in-theory (e/d (slice unsigned-byte-p-forced)
                                  (SLICE-BECOMES-BVCHOP BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

(theory-invariant (incompatible (:rewrite logtail-becomes-slice-bind-free) (:definition slice)))

;TODO: use defruleset instead...
(deftheory anti-slice '(bvchop-1-becomes-getbit ;why?
                        slice-becomes-bvchop ;why?
                        slice-becomes-getbit ;why?
                        logtail-of-bvchop-becomes-slice
                        logtail-becomes-slice
                        bvchop-of-logtail-becomes-slice
                        logtail-becomes-slice-bind-free)
  :redundant-okp t)

(defthm bvchop-of-sum-of-logext
  (implies (and (<= size size2)
                (natp size)
                (natp size2)
                (integerp x)
                (integerp y)
                )
           (equal (bvchop size (+ x (logext size2 y)))
                  (bvchop size (+ x y)))))

(defthm bvchop-of-sum-of-logext-alt
  (implies (and (<= size size2)
                (natp size)
                (natp size2)
                (integerp x)
                (integerp y)
                )
           (equal (bvchop size (+ (logext size2 y) x))
                  (bvchop size (+ x y)))))

;BOZO these subst rules may have been a problem before...
(defthm bvmult-subst
  (implies (and (equal (bvchop size2 x) (bvchop size2 y))
                (syntaxp (smaller-termp y x))
                (<= size size2)
                (natp size2)
                (natp size))
           (equal (bvmult size x z)
                  (bvmult size y z)))
  :hints (("Goal"
           :use ((:instance bvmult-of-bvchop-1-better (x x) (y z))
                 (:instance bvmult-of-bvchop-1-better (x y) (y z)))
           :in-theory (disable bvmult-of-bvchop-arg2
                               bvmult-of-bvchop-1-better
                               bvmult-of-bvchop-arg3))))

(defthm bvmult-subst-alt
  (implies (and (equal (bvchop size2 x) (bvchop size2 y))
                (syntaxp (smaller-termp y x))
                (<= size size2)
                (natp size2)
                (natp size))
           (equal (bvmult size z x)
                  (bvmult size z y)))
  :hints (("Goal" :use (:instance bvmult-subst)
           :in-theory (disable bvmult-subst))))

(defthm bvmult-subst2
  (implies (and (equal (bvchop size2 x) y)
                (syntaxp (smaller-termp y x))
                (<= size size2)
                (natp size2)
                (natp size))
           (equal (bvmult size x z)
                  (bvmult size y z)))
  :hints (("Goal" :use ((:instance bvmult-of-bvchop-1-better (x x) (y z))
                        (:instance bvmult-of-bvchop-1-better (x y) (y z)))
           :in-theory (disable bvmult-of-bvchop-arg2
                               bvmult-of-bvchop-1-better
                               bvmult-of-bvchop-arg3))))

(defthm bvmult-subst2-alt
  (implies (and (equal (bvchop size2 x) y)
                (syntaxp (smaller-termp y x)) ;would like to use smaller-termp in dag rules..
                (<= size size2)
                (natp size2)
                (natp size))
           (equal (bvmult size z x)
                  (bvmult size z y)))
  :hints (("Goal" :use (:instance bvmult-subst2)
           :in-theory (disable bvmult-subst2
                               BVMULT-OF-BVCHOP-1-BETTER))))

(defthm bvmult-subst2-constant-version
  (implies (and (equal (bvchop size2 x) y)
                (syntaxp (and (quotep y)
                              (not (quotep x))))
                (<= size size2)
                (natp size2)
                (natp size))
           (equal (bvmult size x z)
                  (bvmult size y z))))

(defthm bvmult-subst2-alt-constant-version
  (implies (and (equal (bvchop size2 x) y)
                (syntaxp (and (quotep y)
                              (not (quotep x))))
                (<= size size2)
                (natp size2)
                (natp size))
           (equal (bvmult size z x)
                  (bvmult size z y))))

;fffixme add a full subst theory (e.g., for bvcat)

;gen!
(defthm bvmult-of-power-of-2-subst-9-8
  (implies (and (equal (bvchop 6 x) k)
                (syntaxp (quotep k)))
           (equal (bvmult 9 8 x)
                  (bvmult 9 8 k)))
  :hints (("Goal" :in-theory (e/d (bvmult) (bvchop-of-*)))))

;gen this somehow?
(defthm equal-of-0-when-bvlt
  (implies (bvlt size free x)
           (not (equal 0 x))))

(defthm bool-to-bit-equal-0-rewrite
  (implies (booleanp x)
           (equal (equal 0 (bool-to-bit x))
                  (equal nil x))))

(defthm bool-to-bit-equal-1-rewrite
  (implies (booleanp x)
           (equal (equal 1 (bool-to-bit x))
                  (equal t x))))

(defthm unsigned-byte-p-of-floor-25-64
  (implies (natp x)
           (equal (unsigned-byte-p '25 (floor x '64))
                  (unsigned-byte-p '31 x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm slice-bound-hack-31-64-6
  (implies (unsigned-byte-p 31 x)
           (< (- x 64) (* 64 (SLICE 30 6 X))))
  :hints (("Goal" :in-theory (e/d (slice logtail) (anti-slice)))))

;bozo think more about this...
(defthmd bvxor-with-smaller-arg-1-special
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize y) (newsize))
                (syntaxp (quotep newsize))
                (syntaxp (not (quotep n)))
                (<= newsize n) ;even when they are equal we prefer to apply this rule?
                (natp newsize)
                (posp n)
                (force (unsigned-byte-p-forced newsize y))
                )
           (equal (BVXOR n y x)
                  (bvcat (- n newsize)
                         (slice (+ -1 n) newsize x)
                          newsize
                         (bvxor newsize x y))))
  :hints (("Goal"
  :cases ((equal n newsize))
  :in-theory (enable SLICE-TOO-HIGH-IS-0 unsigned-byte-p-forced))))

;fixme these are superseded by the trim rules?

(defthmd bvxor-tighten-arg1
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize x) (newsize))
                (syntaxp (quotep size))
                (< size newsize)
                (natp size))
           (equal (bvxor size x y)
                  (bvxor size (bvchop size x) y)))
  :hints (("Goal" :in-theory (enable bvxor))))

(defthmd bvxor-tighten-arg2
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize y) (newsize))
                (syntaxp (quotep size))
                (< size newsize)
                (natp size))
           (equal (bvxor size x y)
                  (bvxor size x (bvchop size y))))
  :hints (("Goal" :in-theory (enable bvxor))))

;bozo more like this?
(defthm bvxor-with-smaller-arg-2
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize y) (newsize))
                (< newsize n)
                (natp newsize)
                (natp n)
                (force (unsigned-byte-p-forced newsize y))
                )
           (equal (BVXOR n x y)
                  (bvcat (- n newsize)
                         (slice (+ -1 n) newsize x) newsize
                         (bvxor newsize x y))))
  :hints (("Goal" :cases ((equal n 0))
           :in-theory (enable SLICE-TOO-HIGH-IS-0 unsigned-byte-p-forced))))

(defthm bvxor-with-smaller-arg-1
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize y) (newsize))
                (< newsize n)
                (natp newsize)
                (natp n)
                (force (unsigned-byte-p-forced newsize y))
                )
           (equal (BVXOR n y x)
                  (bvcat
                           (- n newsize)
                           (slice (+ -1 n) newsize x) newsize
                           (bvxor newsize x y))))
  :hints (("Goal" :cases ((equal n 0))
           :in-theory (enable SLICE-TOO-HIGH-IS-0 unsigned-byte-p-forced))))

(defthm bvcat-tighten-upper-size
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize highval) (newsize))
                (< newsize highsize)
                (natp newsize)
                (natp highsize)
                (force (unsigned-byte-p-forced newsize highval)))
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat newsize highval lowsize lowval)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (bvcat unsigned-byte-p-forced)
                           ( ;bozo add t-i
                            )))))

(defthm getbit-too-high-cheap
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize x) (newsize))
                ;;make sure it's not nil:
                ;drop this hyp:
                (natp newsize) ;newsize continues to be a bad name for uses like this...
                (<= newsize n)
                (integerp n)
                (force (unsigned-byte-p-forced newsize x)))
           (equal (getbit n x)
                  0))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced)
           :use (:instance getbit-too-high))))

;add
(DEFTHM SLICE-TIGHTEN-TOP-free
  (IMPLIES (AND (UNSIGNED-BYTE-P free X)
                (<= free HIGH)
                (NATP LOW)
                (NATP free)
                (NATP HIGH))
           (EQUAL (SLICE HIGH LOW X)
                  (SLICE (+ -1 free) LOW X)))
  :HINTS (("Goal" :CASES ((EQUAL 0 LOW)
                          (<= LOW free))
           :IN-THEORY (E/D (SLICE)
                           (ANTI-SLICE)))))

(DEFTHM SLICE-TIGHTEN-TOP-quotep
  (IMPLIES (AND (syntaxp (quotep x))
                (syntaxp (not (quotep HIGH)))
                (UNSIGNED-BYTE-P (integer-length x) X)
                (<= (+ -1 (integer-length x)) HIGH)
                (NATP LOW)
                (NATP (integer-length x))
                (NATP HIGH))
           (EQUAL (SLICE HIGH LOW X)
                  (SLICE (+ -1 (integer-length x))
                               LOW X)))
  :HINTS (("Goal" :CASES ((EQUAL 0 LOW)
                          (<= LOW (integer-length x)))
           :IN-THEORY (E/D (SLICE)
                           (ANTI-SLICE)))))

;improver? require constant y?
(defthm use-<=-bound-to-drop-<=-hyp
  (implies (and (<= x k) ;won't match?
                (syntaxp (quotep k))
                (<= k y))
           ;; this says x <= y but matches better
           (not (< y x))))

;BOZO lots more rules like this
;rename?
(defthm bvxor-trim-arg1
  (implies (and (bind-free (bind-var-to-unsigned-term-size-if-trimmable 'innersize x) (innersize))
                (> innersize outersize) ;only fire if strictly greater
                (natp outersize)
                (integerp x)
                (integerp y)
                )
           (equal (bvxor outersize x y)
                  (bvxor outersize (trim outersize x) y)))
  :hints (("Goal" :in-theory (enable bvxor trim))))

;rename?
(defthm bvxor-trim-arg2
  (implies (and (bind-free (bind-var-to-unsigned-term-size-if-trimmable 'innersize y) (innersize))
                (> innersize outersize) ;only fire if strictly greater
                (natp outersize)
                (integerp x)
                (integerp y)
                )
           (equal (bvxor outersize x y)
                  (bvxor outersize x (trim outersize y))))
  :hints (("Goal" :in-theory (enable bvxor trim))))

(defthm bvif-trim-arg1
  (implies (and (bind-free (bind-var-to-unsigned-term-size-if-trimmable 'innersize x) (innersize)) ;bozo newsize is a bad name
                (> innersize outersize) ;only fire if strictly greater
                (natp outersize)
                (integerp x)
                (integerp y)
                )
           (equal (bvif outersize test x y)
                  (bvif outersize test (trim outersize x) y)))
  :hints (("Goal" :in-theory (enable bvif trim))))

(defthm bvif-trim-arg2
  (implies (and (bind-free (bind-var-to-unsigned-term-size-if-trimmable 'innersize y) (innersize)) ;bozo newsize is a bad name
                (> innersize outersize) ;only fire if strictly greater
                (natp outersize)
                (integerp x)
                (integerp y)
                )
           (equal (bvif outersize test x y)
                  (bvif outersize test x (trim outersize y))))
  :hints (("Goal" :in-theory (enable bvif trim))))

;; these should have 'trim' in the name:

;watch out for loops
(defthm bvcat-tighten-high-arg
  (implies (and (bind-free (bind-var-to-unsigned-term-size-if-trimmable 'newsize highval) (newsize))
                (syntaxp (quotep highsize))
                (< highsize newsize)
                (natp highsize)
                (natp newsize)
                (integerp lowval)
                (integerp highval)
                (integerp lowval)
                (natp lowsize)
                )
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize (trim highsize highval) lowsize lowval)))
  :hints (("Goal" :in-theory (enable bvcat-of-bvchop-high trim))))

(defthm bvcat-tighten-low-arg
  (implies (and (bind-free (bind-var-to-unsigned-term-size-if-trimmable 'newsize lowval) (newsize))
                (syntaxp (quotep lowsize))
                (< lowsize newsize)
                (natp highsize)
                (natp newsize)
                (integerp lowval)
                (integerp highval)
                (integerp lowval)
                (natp lowsize)
                )
           (equal (bvcat highsize highval lowsize lowval)
                  (bvcat highsize highval lowsize (trim lowsize lowval))))
  :hints (("Goal" :in-theory (enable bvcat-of-bvchop-low trim))))

;gross proof?
(defthmd bit-blast-peel-off-low
  (implies (and (equal free1 free2)
                (equal free1 (getbit 0 x))
                (equal free2 (getbit 0 y))
                (integerp x)
                (integerp y))
           (equal (equal x y)
                  (equal (logtail 1 x) (logtail 1 y))))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 1 1 nil nil)))
  :hints (("Goal" :in-theory (e/d (logtail getbit bvchop) (BVCHOP-1-BECOMES-GETBIT
                                                            ;mod-of-expt-of-2-constant-version
                                                            mod-of-expt-of-2
                                                            SLICE-BECOMES-GETBIT)))))


(defthm equal-of-getbit-same
  (equal (equal (getbit 0 x) x)
         (unsigned-byte-p 1 x))
  :hints (("Goal" :in-theory (enable getbit-identity))))

;should always bit blast as a last resort?
(defthmd bit-blast-3
  (implies (and (syntaxp (and (member-eq (car x) *trimmable-operators*)
;                               (member-eq (car y) *trimmable-operators*)
                              (equal 3 (unsigned-term-size x))
;(equal 8 (unsigned-term-size y))
                              ))
                (unsigned-byte-p 3 x)
                (unsigned-byte-p 3 y))
           (equal (equal x y)
                  (and (equal (getbit 0 x) (getbit 0 y))
                       (equal (getbit 1 x) (getbit 1 y))
                       (equal (getbit 2 x) (getbit 2 y)))))
  :hints (("Goal" :in-theory (enable bit-blast-peel-off-low))))

; helps DES proofs a lot...
;try to keep more bit-blast rules on; maybe that's what we want - we've already rewritten to RHS and LHS separately...
(defthmd bit-blast-4
  (implies (and (syntaxp (and (member-eq (car x) *trimmable-operators*)
                              (equal 4 (unsigned-term-size x))
                              ))
                (force (unsigned-byte-p-forced 4 x)))
           (equal (equal x y)
                  (and (unsigned-byte-p 4 y)
                       (equal (getbit 0 x) (getbit 0 y))
                       (equal (getbit 1 x) (getbit 1 y))
                       (equal (getbit 2 x) (getbit 2 y))
                       (equal (getbit 3 x) (getbit 3 y)))))
  :hints (("Goal" :in-theory (enable bit-blast-peel-off-low unsigned-byte-p-forced))))

;bozo only do this in the top level goal!
(defthmd bit-blast-8
  (implies (and (syntaxp (and (member-eq (car x) *trimmable-operators*)
                              (member-eq (car y) *trimmable-operators*)
                              (equal 8 (unsigned-term-size x))
                              (equal 8 (unsigned-term-size y))))
                (unsigned-byte-p 8 x)
                (unsigned-byte-p 8 y))
           (equal (equal x y)
                  (and (equal (getbit 0 x) (getbit 0 y))
                       (equal (getbit 1 x) (getbit 1 y))
                       (equal (getbit 2 x) (getbit 2 y))
                       (equal (getbit 3 x) (getbit 3 y))
                       (equal (getbit 4 x) (getbit 4 y))
                       (equal (getbit 5 x) (getbit 5 y))
                       (equal (getbit 6 x) (getbit 6 y))
                       (equal (getbit 7 x) (getbit 7 y)))))
  :hints (("Goal" :in-theory (enable bit-blast-peel-off-low))))

(defthmd bit-blast-31
  (implies (and (syntaxp (and (member-eq (car x) *trimmable-operators*)
                              (member-eq (car y) *trimmable-operators*)
                              (equal 31 (unsigned-term-size x))
                              (equal 31 (unsigned-term-size y))))

                (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (equal x y)
                  (and (equal (getbit 0 x) (getbit 0 y))
                       (equal (getbit 1 x) (getbit 1 y))
                       (equal (getbit 2 x) (getbit 2 y))
                       (equal (getbit 3 x) (getbit 3 y))
                       (equal (getbit 4 x) (getbit 4 y))
                       (equal (getbit 5 x) (getbit 5 y))
                       (equal (getbit 6 x) (getbit 6 y))
                       (equal (getbit 7 x) (getbit 7 y))
                       (equal (getbit 8 x) (getbit 8 y))
                       (equal (getbit 9 x) (getbit 9 y))
                       (equal (getbit 10 x) (getbit 10 y))
                       (equal (getbit 11 x) (getbit 11 y))
                       (equal (getbit 12 x) (getbit 12 y))
                       (equal (getbit 13 x) (getbit 13 y))
                       (equal (getbit 14 x) (getbit 14 y))
                       (equal (getbit 15 x) (getbit 15 y))
                       (equal (getbit 16 x) (getbit 16 y))
                       (equal (getbit 17 x) (getbit 17 y))
                       (equal (getbit 18 x) (getbit 18 y))
                       (equal (getbit 19 x) (getbit 19 y))
                       (equal (getbit 20 x) (getbit 20 y))
                       (equal (getbit 21 x) (getbit 21 y))
                       (equal (getbit 22 x) (getbit 22 y))
                       (equal (getbit 23 x) (getbit 23 y))
                       (equal (getbit 24 x) (getbit 24 y))
                       (equal (getbit 25 x) (getbit 25 y))
                       (equal (getbit 26 x) (getbit 26 y))
                       (equal (getbit 27 x) (getbit 27 y))
                       (equal (getbit 28 x) (getbit 28 y))
                       (equal (getbit 29 x) (getbit 29 y))
                       (equal (getbit 30 x) (getbit 30 y)))))
  :hints (("Goal" :in-theory (enable bit-blast-peel-off-low))))

(defthmd bit-blast-32
  (implies (and (syntaxp (and (member-eq (car x) *trimmable-operators*)
                              (member-eq (car y) *trimmable-operators*)
                              (equal 32 (unsigned-term-size x))
                              (equal 32 (unsigned-term-size y))))

                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (equal x y)
                  (and (equal (getbit 0 x) (getbit 0 y))
                       (equal (getbit 1 x) (getbit 1 y))
                       (equal (getbit 2 x) (getbit 2 y))
                       (equal (getbit 3 x) (getbit 3 y))
                       (equal (getbit 4 x) (getbit 4 y))
                       (equal (getbit 5 x) (getbit 5 y))
                       (equal (getbit 6 x) (getbit 6 y))
                       (equal (getbit 7 x) (getbit 7 y))
                       (equal (getbit 8 x) (getbit 8 y))
                       (equal (getbit 9 x) (getbit 9 y))
                       (equal (getbit 10 x) (getbit 10 y))
                       (equal (getbit 11 x) (getbit 11 y))
                       (equal (getbit 12 x) (getbit 12 y))
                       (equal (getbit 13 x) (getbit 13 y))
                       (equal (getbit 14 x) (getbit 14 y))
                       (equal (getbit 15 x) (getbit 15 y))
                       (equal (getbit 16 x) (getbit 16 y))
                       (equal (getbit 17 x) (getbit 17 y))
                       (equal (getbit 18 x) (getbit 18 y))
                       (equal (getbit 19 x) (getbit 19 y))
                       (equal (getbit 20 x) (getbit 20 y))
                       (equal (getbit 21 x) (getbit 21 y))
                       (equal (getbit 22 x) (getbit 22 y))
                       (equal (getbit 23 x) (getbit 23 y))
                       (equal (getbit 24 x) (getbit 24 y))
                       (equal (getbit 25 x) (getbit 25 y))
                       (equal (getbit 26 x) (getbit 26 y))
                       (equal (getbit 27 x) (getbit 27 y))
                       (equal (getbit 28 x) (getbit 28 y))
                       (equal (getbit 29 x) (getbit 29 y))
                       (equal (getbit 30 x) (getbit 30 y))
                       (equal (getbit 31 x) (getbit 31 y))
                       )))
    :hints (("Goal" :in-theory (enable bit-blast-peel-off-low))))

;bozo handle this in a more general way...
(defthmd bit-blast-7
  (implies (and (syntaxp (and (member-eq (car x) *trimmable-operators*)
                              (member-eq (car y) *trimmable-operators*)
                              (equal 7 (unsigned-term-size x))
                              (equal 7 (unsigned-term-size y))))
                (unsigned-byte-p 7 x)
                (unsigned-byte-p 7 y))
           (equal (equal x y)
                  (and (equal (getbit 0 x) (getbit 0 y))
                       (equal (getbit 1 x) (getbit 1 y))
                       (equal (getbit 2 x) (getbit 2 y))
                       (equal (getbit 3 x) (getbit 3 y))
                       (equal (getbit 4 x) (getbit 4 y))
                       (equal (getbit 5 x) (getbit 5 y))
                       (equal (getbit 6 x) (getbit 6 y))
                       )))
  :hints (("Goal" :in-theory (enable bit-blast-peel-off-low))))

(defthm getbit-of-bitand-all-cases
  (implies (natp n)
           (equal (getbit n (bitand x y))
                  (if (equal n 0)
                      (bitand x y)
                    0)))
  :hints (("Goal" :in-theory (enable bitand))))

;trying disabled.
(defthmd bvchop-of-minus-becomes-bvuminus
  (implies (and (natp n)
                (integerp x))
           (equal (bvchop n (- x))
                  (bvuminus n x)))
  :hints (("Goal" :in-theory (e/d (bvuminus bvminus) (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

(theory-invariant (incompatible (:rewrite bvchop-of-minus-becomes-bvuminus) (:definition bvuminus)))

;more rules for other ops?
(defthm slice-of-myif
  (implies (and (natp high)
                (natp low))
           (equal (slice high low (myif test x y))
                  (slice high low (bvif (+ 1 high) test x y))))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthmd bvif-of-+-arg3
  (implies (and (integerp x)
                (integerp y))
           (equal (bvif size test (+ x y) z)
                  (bvif size test (bvplus size x y) z)))
  :hints (("Goal" :in-theory (enable bvif bvplus))))

(defthmd bvif-of-+-arg4
  (implies (and (integerp x)
                (integerp y))
           (equal (bvif size test z (+ x y))
                  (bvif size test z (bvplus size x y))))
  :hints (("Goal" :in-theory (enable bvif bvplus))))

(defthmd bvif-of-minus-arg3
  (equal (bvif size test (- x) y)
         (bvif size test (bvuminus size x) y))
  :hints (("Goal" :in-theory (e/d (bvif bvuminus bvminus) (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

(defthmd bvif-of-minus-arg4
  (equal (bvif size test y (- x))
         (bvif size test y (bvuminus size x)))
  :hints (("Goal" :in-theory (e/d (bvif bvuminus bvminus) (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))



(defthm slice-of-times-of-expt
  (implies (and (<= j n) ;drop?
                (integerp x) ;drop?
                (natp n)
                (natp j)
                (natp m))
           (equal (slice m n (* (expt 2 j) x))
                  (slice (- m j) (- n j) x)))
  :hints (("Goal" :in-theory (e/d (slice logtail) (anti-slice
                                                   bvchop-of-*)))))

(defthm slice-of-times-of-expt-constant-version
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                (<= (lg k) n) ;drop?
                (integerp x) ;drop?
                (natp n)
                (natp m))
           (equal (slice m n (* k x))
                  (slice (- m (lg k)) (- n (lg k)) x)))
  :hints (("Goal" :in-theory (enable POWER-OF-2P lg)
           :use (:instance slice-of-times-of-expt (j (lg k))))))

;drop the non-gen? and any other specific versions
(defthm slice-of-bvmult-of-expt-gen
  (implies (and	(<= m low) ;gen?
                (<= (+ 1 high) size) ;gen?
                (<= low high)
                (natp low)
                (natp m)
                (integerp size)
                (integerp high))
           (equal (slice high low (bvmult size (expt 2 m) x))
                  (slice (- high m) (- low m) x)))
  :hints (("Goal" :in-theory (e/d (bvmult SLICE-WHEN-VAL-IS-NOT-AN-INTEGER) (bvchop-of-*)))))

(defthm slice-of-bvmult-of-expt-gen-alt
  (implies (and	(<= m low) ;gen?
                (<= (+ 1 high) size) ;gen?
                (<= low high)
                (natp low)
                (natp m)
                (integerp size)
                (integerp high))
           (equal (slice high low (bvmult size x (expt 2 m)))
                  (slice (- high m) (- low m) x)))
  :hints (("Goal" :use (:instance slice-of-bvmult-of-expt-gen)
           :in-theory (disable slice-of-bvmult-of-expt-gen))))

;kill SLICE-OF-BVMULT-33-9-34-8
(defthm slice-of-bvmult-of-expt-gen-constant-version
  (implies (and	(syntaxp (quotep k))
                (power-of-2p k)
                (<= (lg k) low)      ;gen?
                (<= (+ 1 high) size) ;gen?
                (<= low high)
                (natp low)
                (natp (lg k))
                (integerp size)
                (integerp high))
           (equal (slice high low (bvmult size k x))
                  (slice (- high (lg k)) (- low (lg k)) x)))
  :hints (("Goal" :use (:instance slice-of-bvmult-of-expt-gen (m (lg k)))
           :in-theory (e/d (power-of-2p) ( slice-of-bvmult-of-expt-gen)))))

;new:
(in-theory (disable BVCHOP-OF-*))

;kill the special purpose versions
;rename bvmult-of-expt and use that name for this:
(defthm bvmult-of-expt2
  (implies (and (natp n)
                (natp size))
           (equal (bvmult size (expt 2 n) x)
                  (bvcat (- size n) x n 0)))
  :hints (("Goal" :in-theory (enable bvmult bvcat))))

(defthm bvmult-of-expt2-constant-version
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                (natp (lg k))
                (natp size))
           (equal (bvmult size k x)
                  (bvcat (- size (lg k)) x (lg k) 0)))
  :hints (("Goal" :use (:instance bvmult-of-expt2 (n (lg k)))
           :in-theory (disable bvmult-of-expt2))))

(defthm equal-of-getbit-of-0-and-bitnot
  (not (equal (getbit 0 x) (bitnot x)))
  :hints (("Goal" :in-theory (e/d (bitnot) (BITNOT-BECOMES-BITXOR-WITH-1)))))

(defthm equal-of-getbit-of-0-and-bitnot-alt
  (not (equal (bitnot x) (getbit 0 x)))
  :hints (("Goal" :use (:instance equal-of-getbit-of-0-and-bitnot)
           :in-theory (disable equal-of-getbit-of-0-and-bitnot))))

(defthm equal-of-getbit-of-0-and-bitxor-of-1
  (not (equal (getbit 0 x) (bitxor 1 x)))
  :hints (("Goal" :in-theory (e/d (bitxor-of-1-becomes-bitnot-arg1) (bitnot-becomes-bitxor-with-1)))))

(defthm equal-of-getbit-of-0-and-bitxor-of-1-alt
  (not (equal (bitxor 1 x) (getbit 0 x)))
  :hints (("Goal" :use (:instance equal-of-getbit-of-0-and-bitxor-of-1)
           :in-theory (disable equal-of-getbit-of-0-and-bitxor-of-1))))

(defthm equal-of-getbit-and-bitxor-same
  (equal (equal (getbit 0 x) (bitxor x y))
         (equal 0 (getbit 0 y)))
  :hints (("Goal"
           :use (:instance BITXOR-OF-GETBIT-ARG2) ;do we have the complete set of these?
           :in-theory (e/d (                      ;bitxor bvxor
                            ) ( ;BVXOR-1-BECOMES-BITXOR LOGXOR-BVCHOP-BVCHOP
                            BITXOR-OF-GETBIT-ARG2
                            )))))


(defthm equal-of-getbit-and-bitxor-same-alt2
  (equal (equal (getbit 0 x) (bitxor y x)) ;x might appear in other positions as well...
         (equal 0 (getbit 0 y)))
  :hints (("Goal"
           :use (:instance BITXOR-OF-GETBIT-ARG2) ;do we have the complete set of these?
           :in-theory (e/d (                      ;bitxor bvxor
                            ) ( ;BVXOR-1-BECOMES-BITXOR LOGXOR-BVCHOP-BVCHOP
                            BITXOR-OF-GETBIT-ARG2
                            )))))


(defthm equal-of-getbit-and-bitxor-same-alt
  (equal (equal (bitxor x y) (getbit 0 x))
         (equal 0 (getbit 0 y)))
  :hints (("Goal" :use (:instance equal-of-getbit-and-bitxor-same)
           :in-theory (disable equal-of-getbit-and-bitxor-same))))

(defthm equal-of-getbit-and-bitxor-same-alt3
  (equal (equal (bitxor y x) (getbit 0 x))
         (equal 0 (getbit 0 y)))
  :hints (("Goal" :use (:instance equal-of-getbit-and-bitxor-same)
           :in-theory (disable equal-of-getbit-and-bitxor-same))))

(defthm equal-of-bvxor-and-bvxor-same-7
  (equal (equal (bvxor size zw (bvxor size x z)) (bvxor size y (bvxor size x zu)))
         (equal (bvxor size zw z) (bvxor size y zu)))
  :hints (("Goal" :in-theory (e/d (;bvxor
                                   )
                                  (;bvxor-1-becomes-bvxor size
                                   )))))

(defthm equal-of-bvxor-and-bvxor-same-8
  (equal (equal (bvxor size zw x) (bvxor size y (bvxor size x zu)))
         (equal (bvchop size zw) (bvxor size y zu)))
  :hints (("Goal" :in-theory (e/d (;bvxor
                                   )
                                  (;bvxor-1-becomes-bvxor size
                                   )))))

(defun floor-2-sub-1-induct (i n)
  (if (zp n)
      (list i n)
    (floor-2-sub-1-induct (floor i 2) (+ -1 n))))

; a mask with mostly 1s but 0s in the low bits
(defthm logand-of---of-expt
  (implies (unsigned-byte-p size x)
           (equal (logand (- (EXPT 2 SIZE))
                          x)
                  0))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (floor-2-sub-1-induct x size)
           :in-theory (e/d (logand expt zip)
                           (expt-hack
                            ;EXPT-COLLECT-HACK
                            )))))

;we currently prefer bvnot for mutli-bit opens and bitxor with 1 for single bit ops <- a bit weird
;not sure that's a good choice..  bvnot can interfere with the bvxor cancel rules..
(defthmd bvxor-all-ones-helper
  (equal (bvxor size (+ -1 (expt 2 size)) x)
         (bvnot size x))
  :hints (("Goal" :in-theory (e/d (bvnot ;mine for lemmas!
                                   bvxor
                                   LOGEQV
                                   logorc1
                                   ;;bvxor-blast
                                   logxor
                                   lognot-of-logand
                                   )
                                  (BITNOT-BECOMES-BITXOR-WITH-1
                                   ;;BITXOR-OF-1-BECOMES-BITNOT-ARG1 ;looped
                                   )))))

(defthmd bvxor-all-ones-helper-alt
  (equal (bvxor size x (+ -1 (expt 2 size)))
         (bvnot size x))
  :hints (("Goal" :use (:instance bvxor-all-ones-helper)
           :in-theory (disable bvxor-all-ones-helper))))

;we currently prefer bvnot for mutli-bit opens and bitxor with 1 for single bit ops <- a bit weird
;not sure that's a good choice..  bvnot can interfere with the bvxor cancel rules..
(defthmd bvxor-all-ones
  (implies (and (syntaxp (and (quotep mask)
                              (quotep size)))
                (equal mask (+ -1 (expt 2 size))) ;fixme allow the sizes to differ?
                )
           (equal (bvxor size mask x)
                  (bvnot size x)))
  :hints (("Goal" :use (:instance bvxor-all-ones-helper)
           :in-theory (disable bvxor-all-ones-helper))))

;repeatbit of 1 now gets simplified
(defthm bvxor-of-repeatbit-of-1
  (implies (and (natp n)
                (integerp x))
           (equal (bvxor n (repeatbit n 1) x)
                  (bvnot n x)))
  :hints (("Goal" :in-theory (enable bvxor bvnot REPEATBIT logxor logeqv logorc1 lognot-of-logand))))

;since it can be expensive to do this in general??...
(defthm getbit-of-bvxor-when-other-bit-is-0-arg1
  (implies (and (equal (getbit n x) 0)
                (< n size)
                (natp n)
                (natp size))
           (equal (getbit n (bvxor size x y))
                  (getbit n y)))
  :hints (("Goal" :in-theory (enable getbit-of-bvxor-core))))

;ffixme think these over
(defthm getbit-of-bvxor-when-other-bit-is-0-arg2
  (implies (and (equal (getbit n x) 0)
                (< n size)
                (natp n)
                (natp size))
           (equal (getbit n (bvxor size y x))
                  (getbit n y)))
  :hints (("Goal" :in-theory (enable getbit-of-bvxor-core))))

(defthmd bvand-of-bvnot-same-helper
  (implies (unsigned-byte-p size x)
           (equal (bvand size x (bvnot size x))
                  0))
  :hints (("Goal" :cases ((Natp size))
           :in-theory (e/d (bvand bvnot logand-of-bvchop)
                           (bvand-commutative)))))

(defthm bvand-of-bvnot-same
  (equal (bvand size x (bvnot size x))
         0)
  :hints (("Goal" :cases ((natp size))
           :use (:instance bvand-of-bvnot-same-helper (x (bvchop size x))))))

(defthm bvand-of-bvnot-same-alt
  (equal (bvand size (bvnot size x) x)
         0)
  :hints (("Goal" :use (:instance bvand-of-bvnot-same))))

;;(add-invisible-fns bvand bvnot)  ;;todo: it would be nice for this to work

(defthm bvand-of-bvand-of-bvnot-same
  (equal (bvand size x (bvand size (bvnot size x) y))
         0)
  :hints (("Goal" :use (:instance bvand-associative
                                  (y (bvnot size x))
                                  (z y)))))

(defthm bvand-of-bvand-of-bvnot-same-alt
  (equal (bvand size (bvnot size x) (bvand size x y))
         0)
  :hints (("Goal" :use (:instance bvand-of-bvand-of-bvnot-same)
           :in-theory (disable bvand-of-bvand-of-bvnot-same))))

(defthmd bvnot-becomes-bvxor
  (implies (and (syntaxp (quotep size)) ;drop?
;                (integerp x)
                (natp size))
           (equal (bvnot size x)
                  (bvxor size (+ -1 (expt 2 size)) x)))
  :hints (("Goal" :use (:instance bvxor-all-ones (mask (+ -1 (expt 2 size))))
           :in-theory (disable bvxor-all-ones))))

(theory-invariant (incompatible (:rewrite bvnot-becomes-bvxor) (:rewrite bvxor-all-ones)))

;bozo more like this, or a general rule with a syntaxp hyp?
(defthm getbit-of-bvand-too-high
  (implies (and (<= size n)
                (natp n)
                (natp size))
           (equal (getbit n (bvand size x y))
                  0))
  :hints (("Goal" :in-theory (enable getbit-too-high))))

(defthm bvand-of-bvxor-of-ones-same
  (implies (and (syntaxp (and (quotep k)            ;new
                              (quotep size)))
                (equal k (+ -1 (expt 2 size))))
           (equal (bvand size x (bvxor size k x))
                  0))
  :hints (("Goal" :in-theory (enable ;BVXOR-ALL-ONES-GEN
                              bvxor-all-ones-helper-alt))))

(defthm bvand-of-bvxor-of-ones-same-alt
  (implies (and (syntaxp (and (quotep k) ;new
                              (quotep size)))
                (equal k (+ -1 (expt 2 size))))
           (equal (bvand size (bvxor size k x) x)
                  0))
  :hints (("Goal" :in-theory (enable ;BVXOR-ALL-ONES-GEN
                              bvxor-all-ones-helper-alt))))

(defthm bvand-of-bvand-of-bvxor-of-ones-same
  (implies (equal k (+ -1 (expt 2 size)))
           (equal (bvand size x (bvand size (bvxor size k x) y))
                  0))
  :hints (("Goal" :use (:instance bvand-of-bvand-of-bvnot-same)
           :in-theory (e/d (BVXOR-ALL-ONES-HELPER-ALT) ( bvand-of-bvand-of-bvnot-same)))))

(defthm bvand-of-bvand-of-bvxor-of-ones-same-alt
  (implies (equal k (+ -1 (expt 2 size)))
           (equal (bvand size (bvxor size k x) (bvand size x y))
                  0))
  :hints (("Goal" :use (:instance bvand-of-bvand-of-bvnot-same)
           :in-theory (e/d (bvxor-all-ones-helper-alt) ( bvand-of-bvand-of-bvnot-same)))))

;may help when size is not a constant
(defthm bvand-of-bvxor-of-ones-same-another-alt
  (equal (bvand size x (bvxor size x (+ -1 (expt 2 size))))
         0)
  :hints
  (("Goal" :in-theory (enable bvxor-all-ones-helper-alt))))

(defthm bvxor-of-myif-1
  (equal (bvxor size (myif test a b) y)
         (bvxor size (bvif size test a b) y))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm bvxor-of-myif-2
  (equal (bvxor size y (myif test a b))
         (bvxor size y (bvif size test a b)))
  :hints (("Goal" :in-theory (enable bvif myif))))

;newly disabled
(defthmd logxor-bvchop-bvchop
  (implies (and (integerp x)
                (<= 0 size)
                (integerp size)
                (integerp y))
           (equal (LOGXOR (BVCHOP size x)
                          (BVCHOP size y))
                  (bvxor size x y)))
  :hints (("Goal" :in-theory (enable bvxor))))

(theory-invariant (incompatible (:definition bvxor) (:rewrite LOGXOR-BVCHOP-BVCHOP)))

(defthm bitxor-of-myif-arg1
  (equal (bitxor (myif test a b) y)
         (bitxor (bvif 1 test a b) y))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm bitxor-of-myif-arg2
  (equal (bitxor y (myif test a b))
         (bitxor y (bvif 1 test a b)))
  :hints (("Goal" :in-theory (enable bvif myif))))

(defthm bvnot-of-bvcat
  (implies (and (equal n (+ lowsize highsize))
                (natp lowsize)
                (posp highsize) ;was natp
                )
           (equal (bvnot n (bvcat highsize highval lowsize lowval))
                  (bvcat highsize (bvnot highsize highval) lowsize (bvnot lowsize lowval))))
  :hints (("Goal"
           :use ((:instance BVNOT-OF-BVCHOP (x (BVCAT HIGHSIZE HIGHVAL LOWSIZE LOWVAL))
                            (size lowsize)
                            (size2 lowsize))
                 (:instance BVNOT-OF-BVCHOP (x highval)
                            (size highsize)
                            (size2 highsize))
                 (:instance BVNOT-OF-BVCHOP (x lowval)
                            (size lowsize)
                            (size2 lowsize)))
           :in-theory (e/d ( ;bvnot ;bvcat
                            )
                           (BVNOT-OF-BVCHOP
                            BVNOT-OF-BVCHOP-same
;BVCAT-EQUAL-REWRITE-ALT
;BVCAT-EQUAL-REWRITE
                            )))))


;gen!
(defthm bvplus-of-floor-4-32
  (implies (integerp i)
           (equal (BVPLUS '4 x (FLOOR i '32))
                  (BVPLUS '4 x (slice 8 5 i))))
  :hints (("Goal" :in-theory (enable BVCHOP-OF-FLOOR-OF-EXPT-OF-2-CONSTANT-VERSION))))

;gen!
(defthm bvplus-of-floor-4-32-alt
  (implies (integerp i)
           (equal (BVPLUS '4 x (FLOOR i '32))
                  (BVPLUS '4 x (slice 8 5 i))))
  :hints (("Goal" :in-theory (enable BVCHOP-OF-FLOOR-OF-EXPT-OF-2-CONSTANT-VERSION))))

(defthm unsigned-byte-p-of-floor-of-expt-constant-version
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                (integerp x)
                (natp (lg k))
                (natp n))
           (equal (unsigned-byte-p n (floor x k))
                  (unsigned-byte-p (+ n (lg k)) x)))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-floor-of-expt (m (lg k)))
           :in-theory (disable unsigned-byte-p-of-floor-of-expt))))

;; (defthm getbit-0-of-myif
;;   (equal (getbit 0 (myif test a b))
;;          (bvif 1 test a b))
;;   :hints (("Goal" :in-theory (e/d (bvif myif) (slice-becomes-getbit)))))

(defthm getbit-of-myif
  (implies (natp n) ;drop?
           (equal (getbit n (myif test x y))
                  (getbit n (bvif (+ 1 n) test x y))))
  :hints (("Goal" :cases ((natp n))
           :in-theory (enable bvif myif))))

(defthm getbit-of-myif-lift
  (equal (getbit n (myif test x1 x2))
         (bvif 1 test (getbit n x1) (getbit n x2)))
  :hints (("Goal" :in-theory (enable bvif myif))))

;ffixme think about this..
;go to bvif!
(defthmd bvchop-of-myif-consant-branches
  (implies (syntaxp (and (quotep x)
                         (quotep y)
                         (quotep size)))
           (equal (bvchop size (myif test x y))
                  (myif test (bvchop size x) (bvchop size y))))
  :hints (("Goal" :in-theory (enable myif bvif))))

;combine these
(defthm trim-of-bvsx
  (implies (and (<= n new-size)
                (natp n)
                (natp new-size)
                (posp old-size))
           (equal (trim n (bvsx new-size old-size val))
                  (if (<= old-size n)
                      (bvsx n old-size val)
                    (bvchop N VAL))))
  :hints (("Goal" :in-theory (enable trim bvsx))))

(defthm trim-of-slice
  (implies (and (natp n)
                (natp high)
                (natp low))
           (equal (trim n (slice high low x))
                  (if (<= n (+ 1 (- high low)))
                      (slice (+ -1 n low) low x)
                    (slice high low x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthm trim-of-bvcat
  (implies (and (natp n)
                (natp lowsize)
                (natp highsize))
           (equal (trim n (bvcat highsize highval lowsize lowval))
                  (if (<= n lowsize)
                      (bvchop n lowval) ;don't want to leave a trim (e.g. around a variable)
                    (bvcat (min (binary-+ n (unary-- lowsize))
                                highsize)
                           highval lowsize lowval))))
  :hints (("Goal" :in-theory (enable trim))))

(defthm logtail-of-floor-of-expt
  (implies (and (integerp x)
                (natp pos)
                (natp n))
           (equal (logtail pos (floor x (expt 2 n)))
                  (logtail (+ pos n) x)))
  :hints (("Goal" :in-theory (enable logtail expt-of-+))))

(defthm logtail-of-floor-of-expt-constant-version
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                (integerp x)
                (natp pos)
                (natp (lg k)))
           (equal (logtail pos (floor x k))
                  (logtail (+ pos (lg k)) x)))
  :hints (("Goal" :use (:instance logtail-of-floor-of-expt (n (lg k)))
           :in-theory (disable logtail-of-floor-of-expt))))

(defthm slice-of-floor-of-expt
  (implies (and (integerp x)
                (natp low)
                (natp high)
                (natp n))
           (equal (slice high low (floor x (expt 2 n)))
                  (slice (+ high n) (+ low n) x)))
  :hints (("Goal" :in-theory (e/d (slice) (bvchop-of-logtail-becomes-slice)))))

(defthm slice-of-floor-of-expt-constant-version
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                (integerp x)
                (natp low)
                (natp high)
                (natp (lg k)))
           (equal (slice high low (floor x k))
                  (slice (+ high (lg k)) (+ low (lg k)) x)))
  :hints (("Goal" :use (:instance slice-of-floor-of-expt (n (lg k)))
           :in-theory (disable slice-of-floor-of-expt))))

(defthm integerp-when-unsigned-byte-p-size-arg
  (implies (unsigned-byte-p x free)
           (integerp x))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

;figure out how to restrict this case right
(defthm bvlt-when-bvlt-reverse
  (implies (and (bvlt size free x) ;free var helps restrict this rule to the case we care about?
                (equal free y))
           (not (bvlt size x y)))
  :hints (("Goal" :in-theory (enable bvlt))))

;add a bvlt and bvlt imply bvlt rule?

(defthm boolor-of-bvlt-of-constant-and-bvlt-of-constant
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)
                         (quotep size)))
           (equal (boolor (bvlt size x k1)
                          (bvlt size x k2))
                  (if (bvle size k1 k2) ;gets computed
                      (bvlt size x k2)
                    (bvlt size x k1))))
  :hints (("Goal" :in-theory (enable bvlt-transitive-core-1 bvlt-transitive-core-2))))

;fixme more like this?!
(defthm boolor-of-bvlt-of-constant-and-bvlt-of-constant-3-disjuncts
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)
                         (quotep size)))
           (equal (boolor (bvlt size x k1)
                          (boolor (bvlt size x k2)
                                  y))
                  (boolor (if (bvle size k1 k2) ;gets computed
                              (bvlt size x k2)
                            (bvlt size x k1))
                          y)))
  :hints (("Goal" :use (:instance boolor-of-bvlt-of-constant-and-bvlt-of-constant)
           :in-theory (enable boolor boolor-of-bvlt-of-constant-and-bvlt-of-constant))))

(defthm boolor-of-bvlt-of-constant-and-bvlt-of-constant-2
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)
                         (quotep size)))
           (equal (boolor (bvlt size k1 x)
                          (bvlt size k2 x))
                  (if (bvle size k2 k1) ;gets computed
                      (bvlt size k2 x)
                    (bvlt size k1 x))))
  :hints (("Goal" :in-theory (enable bvlt-transitive-core-1 bvlt-transitive-core-2))))

(defthm boolor-of-bvlt-of-constant-and-bvlt-of-constant-alt
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)
                              (quotep size)))
                (natp size)
                (natp k1))
           (equal (boolor (not (bvlt size k1 x))
                          (bvlt size x k2))
                  (if (bvlt size k1 k2) ;gets computed
                      (bvlt size x k2)
                    (not (bvlt size k1 x)))))
  :hints (("Goal" :in-theory (enable bvlt bvchop-of-sum-cases))))

(defthm boolor-of-bvlt-of-constant-and-bvlt-of-constant-alt2
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)
                              (quotep size)))
                (natp size)
                (natp k1))
           (equal (boolor (bvlt size x k2)
                          (not (bvlt size k1 x)))
                  (if (bvlt size k1 k2) ;gets computed
                      (bvlt size x k2)
                    (not (bvlt size k1 x)))))
  :hints (("Goal" :in-theory (enable bvlt bvchop-of-sum-cases))))

(defthm boolor-of-bvlt-of-constant-and-bvlt-of-constant-alt3
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)
                              (quotep size)))
                (natp size)
                (natp k1))
           (equal (boolor (not (bvlt size k2 x))
                          (not (bvlt size k1 x)))
                  (if (bvle size k1 k2) ;gets computed
                      (not (bvlt size k2 x))
                    (not (bvlt size k1 x)))))
  :hints (("Goal" :in-theory (enable bvlt bvchop-of-sum-cases))))


(defthm boolor-of-bvlt-of-constant-and-bvlt-of-constant-2-alt
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)
                         (quotep size)))
           (equal (boolor (bvlt size k1 x)
                          (not (bvlt size x k2)))
                  (if (bvle size k2 k1) ;gets computed
                      (not (bvlt size x k2))
                    (bvlt size k1 x))))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm boolor-of-bvlt-of-constant-and-bvlt-of-constant-2-alt2
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)
                         (quotep size)))
           (equal (boolor (not (bvlt size x k2))
                          (bvlt size k1 x))
                  (if (bvle size k2 k1) ;gets computed
                      (not (bvlt size x k2))
                    (bvlt size k1 x))))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm boolor-of-bvlt-of-constant-and-bvlt-of-constant-2-alt3
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)
                         (quotep size)))
           (equal (boolor (not (bvlt size x k2))
                          (not (bvlt size x k1)))
                  (if (bvle size k2 k1) ;gets computed
                      (not (bvlt size x k2))
                    (not (bvlt size x k1)))))
  :hints (("Goal" :in-theory (enable bvlt))))

;this looped before i put in the fakefree stuff (which is because the dag prover doesn have backchain limits)
(defthm bvlt-when-not-bvlt
  (implies (and (NOT (BVLT fakefreesize free x))
                (equal fakefreesize size) ;gross?
                (bvlt fakefreesize2 free k)
                (equal fakefreesize2 size) ;gross?
                )
           (equal (BVLT size x k)
                  t))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  )))))

;more like these? e.g., ones with just 2 conjuncts, bvlt versions, signed versions?
(defthm booland-combine-adjacent-bvles
  (implies (and (syntaxp (and (quotep low) (quotep high)))
                (bvle size low high)
                )
           (equal (booland (not (bvlt size x low)) (booland (not (bvlt size x high)) rest))
                  (booland (not (bvlt size x high)) rest))))

(defthm booland-combine-adjacent-bvles-alt
  (implies (and (syntaxp (and (quotep low) (quotep high)))
                (bvle size low high)
                )
           (equal (booland (not (bvlt size x high)) (booland (not (bvlt size x low)) rest))
                  (booland (not (bvlt size x high)) rest))))

;=== new stuff for ABC experiment:

;; ;if just myif
;; (defun ite (test x y)
;;   (if test
;;       x
;;     y))

(defthm bool-to-bit-of-boolif
  (implies (and (booleanp x)
                (booleanp y))
           (equal (bool-to-bit (boolif test x y))
                  (myif test (bool-to-bit x) (bool-to-bit y))))
  :hints (("Goal" :in-theory (enable myif bool-to-bit boolif))))

;just run the function!
(defthm bool-to-bit-of-nil
  (equal (bool-to-bit nil)
         0))

;just run the function!
(defthm bool-to-bit-of-t
  (equal (bool-to-bit t)
         1))

;fixme do we use this?
;the test is a bit, not a boolean
(defun bif (bit x y)
  (if (equal bit 0)
      (getbit 0 y)
    (getbit 0 x)))

(defthm myif-becomes-bif
  (implies (and (booleanp test)
                (unsigned-byte-p 1 x)
                (unsigned-byte-p 1 y))
           (equal (myif test x y)
                  (bif (bool-to-bit test) x y))))

(defthm bool-to-bit-of-equal
  (implies (and (unsigned-byte-p 1 x)
                (unsigned-byte-p 1 y))
           (equal (bool-to-bit (equal x y))
                  (bitxnor x y))))

(defthm bif-x-y-0
  (implies (and (unsigned-byte-p 1 x)
                (unsigned-byte-p 1 y))
           (equal (bif x y 0)
                  (bitand x y))))

(defthm bool-to-bit-of-not
  (equal (bool-to-bit (not x))
         (bitnot (bool-to-bit x)))
  :hints (("Goal" :in-theory (e/d (bool-to-bit) ( bitxor-of-1-becomes-bitnot-arg1))
           :do-not '(preprocess))))


(defthm bitxnor-of-getbit-0
  (equal (bitxnor (getbit 0 x) y)
         (bitxnor x y))
  :hints (("Goal" :in-theory (enable bitxnor))))

(defthm bitxnor-of-getbit-0-alt
  (equal (bitxnor y (getbit 0 x))
         (bitxnor y x))
  :hints (("Goal" :in-theory (enable bitxnor))))

(defthm bitxnor-of-1
  (equal (bitxnor 1 x)
         (getbit 0 x)))

(defthm bitxnor-of-1-arg2
  (equal (bitxnor x 1)
         (getbit 0 x)))


 ;bozo gen the 1
(defthm unsigned-byte-p-of-bif
  (unsigned-byte-p 1 (bif test x y)))

(defthm bif-of-getbit-0
  (equal (bif test y (getbit 0 x))
         (bif test y x))
  :hints (("Goal" :in-theory (enable bif))))

(defthm bif-of-getbit-0-alt
  (equal (bif test (getbit 0 x) y)
         (bif test x y))
  :hints (("Goal" :in-theory (enable bif))))

(defthm integer-length-all-ones-free
  (implies (and (equal x (expt 2 free))
                (natp free))
           (equal (integer-length (+ -1 x))
                  free)))

(defthmd bvxor-blast
  (implies (and (< 1 size)  ;would loop for size=1
                (integerp size))
           (equal (bvxor size x y)
                  (bvcat 1
                         (bvxor 1 (getbit (+ -1 size) x) (getbit (+ -1 size) y)) ;use bitXor?
                         (+ -1 size)
                         (bvxor (+ -1 size)
                                x ;(bvchop (+ -1 size) x) ;trying...
                                y ;(bvchop (+ -1 size) y) ;trying...
                                )))))

(defthmd bvand-blast
  (implies (and (< 1 size) ;would loop for size=1
                (integerp size))
           (equal (bvand size x y)
                  (bvcat 1
                         (bvand 1 (getbit (+ -1 size) x) (getbit (+ -1 size) y)) ;use bitand?
                         (+ -1 size)
                         (bvand (+ -1 size)
                                x ;(bvchop (+ -1 size) x)
                                y ;(bvchop (+ -1 size) y)
                                )))))

;fixme which way do we want to peel off the bits (high bits first or low bits first?).  depends on how we're normalizing bvcat nests
(defthmd bvor-blast
  (implies (and (< 1 size)  ;would loop for size=1
                (integerp size))
           (equal (bvor size x y)
                  (bvcat 1
                         (bvor 1 (getbit (+ -1 size) x) (getbit (+ -1 size) y)) ;use bitor?
                         (+ -1 size)
                         (bvor (+ -1 size)
                               x ;(bvchop (+ -1 size) x)
                               y ;(bvchop (+ -1 size) y)
                               )))))

;bozo gen!
(defthm logext-equal-0-rewrite-32
  (equal (equal 0 (logext 32 x))
         (equal 0 (bvchop 32 x)))
  :hints (("Goal" :in-theory (enable ADD-BVCHOPS-TO-EQUALITY-OF-SBPS-4))))

;should bvmult ifix its args?
(defthm bvmult-of-logext
  (implies (and (<= size size2)
                (integerp x) ;drop?
                (integerp y) ;drop?
                (natp size)
                (integerp size2)
		)
           (equal (bvmult size x (logext size2 y))
                  (bvmult size x y)))
  :hints (("Goal" :in-theory (e/d (bvmult) (bvchop-of-*)))))

;BOZO add to meta.lisp for bvmult and bvplus...??
(defthm bvmult-of-logext-alt
  (implies (and (<= size size2)
                (integerp x) ;drop?
                (integerp y) ;drop?
                (natp size)
                (integerp size2)
		)
           (equal (bvmult size (logext size2 y) x)
                  (bvmult size y x)))
  :hints (("Goal" :in-theory (e/d (bvmult) (bvchop-of-*)))))

;BOZO gen
(defthm bvplus-constant-equal-constant
  (implies (integerp x)
           (equal (equal (bvplus 32 1 x) 0)
                  (equal (bvchop 32 x)
                         (bvchop 32 -1))))
  :hints (("Goal"
;           :use (:instance bvchop-+-cancel (k 4294967295) (j x) (i 1) (size 32))
           :in-theory (e/d (bvplus bvchop mod-sum-cases)
                           (;bvchop-+-cancel
                            )))))

(defthm bvand-of-bvand-of-bvnot-same-xor-version
  (implies (AND (SYNTAXP (AND (QUOTEP MASK) (QUOTEP SIZE)))
                (EQUAL MASK (+ -1 (EXPT 2 SIZE))))
           (equal (bvand size x (bvand size (bvxor size mask x) y))
                  0))
  :hints (("Goal" :in-theory (disable BVAND-OF-BVAND-OF-BVNOT-SAME)
           :use (BVXOR-ALL-ONES
                 (:instance bvand-of-bvand-of-bvnot-same)))))

(defthm bvand-of-bvand-of-bvnot-same-alt-xor-version
  (implies (AND (SYNTAXP (AND (QUOTEP MASK) (QUOTEP SIZE)))
                (EQUAL MASK (+ -1 (EXPT 2 SIZE))))
           (equal (bvand size (bvxor size mask x) (bvand size x y))
                  0))
  :hints (("Goal" :in-theory (disable BVAND-OF-BVAND-OF-BVNOT-SAME-alt)
           :use (BVXOR-ALL-ONES
                 (:instance bvand-of-bvand-of-bvnot-same-alt)))))

(defthm equal-of-bvxor-ones-and-bvnot
  (implies (and (syntaxp (and (quotep mask) (quotep size)))
                (equal mask (+ -1 (expt 2 size))))
           (equal (equal (bvxor size mask x) (bvnot size x))
                  t))
  :hints (("Goal" :in-theory (enable bvxor-all-ones-helper))))

(defthm equal-of-bvnot-and-bvxor-ones
  (implies (and (syntaxp (and (quotep mask) (quotep size)))
                (equal mask (+ -1 (expt 2 size))))
           (equal (equal (bvnot size x) (bvxor size mask x))
                  t))
  :hints (("Goal" :use (:instance equal-of-bvxor-ones-and-bvnot)
           :in-theory (disable equal-of-bvxor-ones-and-bvnot))))



(defthm bitand-of-bitxor-of-1-same
  (equal (bitand x (bitxor 1 x))
         0)
  :hints (("Goal" :in-theory (e/d (bitand bitxor bitnot) (BVXOR-1-BECOMES-BITXOR)))))

(defthm bitand-of-bitxor-of-1-same-alt
  (equal (bitand x (bitand (bitxor 1 x) w)) ;yuck: replacing w with y fails due to alpha order
         0)
  :hints (("Goal" :in-theory (e/d (bitand bitxor bitnot) (BVXOR-1-BECOMES-BITXOR)))))

;fixme gen!
(defthm bvlt-of-floor-arg2
  (implies (integerp x)
           (equal (bvlt 4 (floor x 32) y)
                  (bvlt 4 (slice 8 5 x) y)))
  :hints (("Goal" :in-theory (enable bvlt
                                     bvchop-of-floor-of-expt-of-2-constant-version))))

;fixme gen!
(defthm bvlt-of-floor-arg3
  (implies (integerp x)
           (equal (bvlt 4 y (floor x 32))
                  (bvlt 4 y (slice 8 5 x))))
  :hints (("Goal" :in-theory (enable bvlt
                                     bvchop-of-floor-of-expt-of-2-constant-version))))

;BBOZO think more about this in the size > 1 case!! - do we want to push the getbit through?
;in the size=1 case (common when bit blasting) we do NOT want to push the GETBIT through - can be expensive!
(defthm getbit-of-bvand-eric-2
  (implies (and (< 0 size)
                (integerp size) ;drop?
                )
           (equal (getbit 0 (bvand size x y))
                  (bvand 1 x y)))
  :hints (("Goal" :cases ((integerp size)))))

(defthmd bvand-1-split
  (equal (bvand 1 x y)
         (if (equal 1 (getbit 0 y))
             (if (equal 1 (getbit 0 x)) 1 0)
           ;both branches are the same...:
           (if (equal 1 (getbit 0 x)) 0 0)))
  :hints (("Goal" :in-theory (enable bvand))))

;fixme we probably need a lot more rules like this to add sizes (we need sizes
;in the if nest, since there can be logexts to be gotten rid of at the leaves
;of the if nest)
;fixme what about using the trim mechanism for this?
(defthm bvand-of-myif-arg2
  (equal (bvand n x (myif test a b))
         (bvand n x (bvif n test a b)))
  :hints (("Goal" :in-theory (e/d (myif bvif bvand)
                                  ( ;BIT-BLAST-32-ALT
                                   BLAST-BVAND-32-INTO-8
                                   )))))

(defthm bvand-of-myif-arg1
  (equal (bvand n (myif test a b) x)
         (bvand n (bvif n test a b) x))
  :hints (("Goal" :in-theory (e/d (myif bvif bvand)
                                  ( ;BIT-BLAST-32-ALT
                                   BLAST-BVAND-32-INTO-8)))))



;add quotep hyp?
(defthm bvand-numeric-bound
  (implies (and (<= (expt 2 size) k)
                (natp size))
           (< (bvand size x y) k))
  :hints (("Goal" :use (:instance UNSIGNED-BYTE-P-OF-BVAND
                                  (Y Y) (X X) (n size) (SIZE size))
           :in-theory (disable UNSIGNED-BYTE-P-OF-BVAND UNSIGNED-BYTE-P-OF-BVAND-simple))))

(defthm logtail-of-bvand
  (implies (and (natp size)
                (natp n))
           (equal (logtail n (bvand size x y))
                  (slice (+ -1 size) n (bvand size x y))))
  :hints (("Goal"
           :use (:instance LOGTAIL-BECOMES-SLICE-BIND-FREE (x (bvand size x y))
                           (newsize size))
           :in-theory (disable LOGTAIL-BECOMES-SLICE-BIND-FREE))))

;use the non-bind-free one..
(defthm logtail-of-bvor
  (implies (and (natp size)
                (natp n))
           (equal (logtail n (bvor size x y))
                  (slice (+ -1 size) n (bvor size x y))))
  :hints (("Goal"
           :use (:instance LOGTAIL-BECOMES-SLICE-BIND-FREE (x (bvor size x y))
                           (newsize size))
           :in-theory (disable LOGTAIL-BECOMES-SLICE-BIND-FREE))))

;bozo adapt to bitxor, etc.
(defthm bitand-of-repeatbit-arg2
  (implies (and (< 0 n)
                (unsigned-byte-p 1 bit)
                (integerp n))
           (equal (bitand x (repeatbit n bit))
                  (bitand x bit)))
  :hints (("Goal" :in-theory (enable bitand bvand))))

;use trim
(defthm bitand-of-repeatbit-arg1
  (implies (and (< 0 n)
                (unsigned-byte-p 1 bit)
                (integerp n))
           (equal (bitand (repeatbit n bit) x)
                  (bitand bit x)))
  :hints (("Goal" :in-theory (enable bitand bvand))))

;use trim
(defthm bitand-of-bvsx-arg2
  (implies (and (< 0 old-size)
                (< 0 new-size)
                (integerp old-size)
                (integerp new-size)
                )
           (equal (bitand x (bvsx new-size old-size y))
                  (bitand x y)))
  :hints (("Goal"
           :cases ((equal 1 old-size))
           :in-theory (enable bvsx bitand bvand))))

(defthm bitand-of-bvsx-arg1
  (implies (and (< 0 old-size)
                (< 0 new-size)
                (integerp old-size)
                (integerp new-size)
                )
           (equal (bitand (bvsx new-size old-size y) x)
                  (bitand y x)))
  :hints (("Goal"
           :cases ((equal 1 old-size))
           :in-theory (enable bvsx bitand bvand))))

;why does logtail arise?
(defthmd bvand-logtail-arg1
  (implies (and (natp size)
                (< 0 size)
                (natp n))
           (equal (bvand size (logtail n x) y)
                  (bvand size (slice (+ -1 n size) n x) y)))
  :hints (("Goal" :in-theory (enable bvand bvchop-of-logtail-becomes-slice))))

;why does logtail arise?
(defthmd bvand-logtail-arg2
  (implies (and (natp size)
                (< 0 size)
                (natp n))
           (equal (bvand size y (logtail n x))
                  (bvand size y (slice (+ -1 n size) n x))))
  :hints (("Goal" :in-theory (enable bvand bvchop-of-logtail-becomes-slice))))

;why does logtail arise?
;can loop with defn slice?
(defthmd bvxor-logtail-arg1
  (implies (and (natp size)
                (< 0 size)
                (natp n))
           (equal (bvxor size (logtail n x) y)
                  (bvxor size (slice (+ -1 n size) n x) y)))
  :hints (("Goal" :in-theory (e/d (bvxor bvchop-of-logtail-becomes-slice)
                                  (LOGXOR-BVCHOP-BVCHOP)))))

;why does logtail arise?
;can loop with defn slice?
(defthmd bvxor-logtail-arg2
  (implies (and (natp size)
                (< 0 size)
                (natp n))
           (equal (bvxor size y (logtail n x))
                  (bvxor size y (slice (+ -1 n size) n x))))
  :hints (("Goal" :in-theory (e/d (bvxor bvchop-of-logtail-becomes-slice)
                                  (LOGXOR-BVCHOP-BVCHOP)))))

;add some of these?
(defthm leftrotate32-of-logext-32
  (equal (leftrotate32 amd (logext 32 x))
         (leftrotate32 amd x))
  :hints (("Goal" :in-theory (enable leftrotate32 leftrotate))))


(defthmd bvnot-blast
  (implies (and (< 1 size) ;for size=1 go to bitnot
                (INTEGERP X)
                (integerp size))
           (equal (bvnot size x)
                  (bvcat 1
                         (bitnot (getbit (+ -1 size) x))
                         (+ -1 size)
                         (bvnot (+ -1 size) x)
                         ))))

(defthm equal-constant-when-unsigned-byte-p
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p free x)
                (syntaxp (quotep free))
                (not (unsigned-byte-p free k)))
           (not (equal k x))))

(defthm equal-constant-when-unsigned-byte-p-alt
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p free x)
                (syntaxp (quotep free))
                (not (unsigned-byte-p free k)))
           (not (equal x k))))

(defthm bvchop-of-leftrotate-low
  (implies (and (<= size amount) ;this case
                (<= amount width)
                (natp size)
                (posp width)
                (natp amount))
           (equal (bvchop size (leftrotate width amount val))
                  (slice (+ -1 (- AMOUNT) SIZE WIDTH)
                         (+ (- AMOUNT) WIDTH)
                         val)))
  :hints (("Goal" :cases ((equal amount width))
           :in-theory (enable LEFTROTATE))))

;combine the cases?
(defthm bvchop-of-leftrotate-not-low
  (implies (and (< amount size)  ;this case
                (<= size width)
                (natp size)
                (posp width)
                (natp amount))
           (equal (bvchop size (leftrotate width amount val))
                  (bvcat (- size amount)
                         val
                         amount
                         (SLICE (+ -1 WIDTH)
                                (+ (- AMOUNT) WIDTH)
                                VAL) )))
  :hints (("Goal" ;:cases ((equal amount width))
           :in-theory (enable LEFTROTATE))))

;; is there a nicer way to comvine the cases?
(defthm bvchop-of-leftrotate-both
  (implies (and (<= size width)
                (<= amount width)
                (natp size)
                (posp width)
                (natp amount))
           (equal (bvchop size (leftrotate width amount val))
                  (if (< amount size)
                      (bvcat (- size amount)
                             val
                             amount
                             (SLICE (+ -1 WIDTH)
                                    (+ (- AMOUNT) WIDTH)
                                    VAL) )
                    (slice (+ -1 (- AMOUNT) SIZE WIDTH)
                           (+ (- AMOUNT) WIDTH)
                           val))))
  :hints (("Goal" :cases ((< amount size)))))

(defthmd bvchop-of-leftrotate32-both
  (implies (and (<= size 32)
                (<= amount 32)
                (natp size)
                (natp amount))
           (equal (bvchop size (leftrotate32 amount val))
                  (if (< amount size)
                      (bvcat (- size amount)
                             val
                             amount
                             (SLICE (+ -1 32)
                                    (+ (- AMOUNT) 32)
                                    VAL) )
                    (slice (+ -1 (- AMOUNT) SIZE 32)
                           (+ (- AMOUNT) 32)
                           val))))
  :hints (("Goal" :in-theory (enable leftrotate32))))

(defthm trim-of-leftrotate32
  (implies (and (<= size 32)
                (<= amount 32)
                (natp size)
                (natp amount))
           (equal (trim size (leftrotate32 amount val))
                  (if (< amount size)
                      (bvcat (- size amount)
                             val
                             amount
                             (SLICE (+ -1 32)
                                    (+ (- AMOUNT) 32)
                                    VAL) )
                    (slice (+ -1 (- AMOUNT) SIZE 32)
                           (+ (- AMOUNT) 32)
                           val))))
  :hints (("Goal" :in-theory (enable trim bvchop-of-leftrotate32-both))))

(defthm slice-of-leftrotate
  (implies (and (< highbit width) ;otherwise we can tighten the slice
                (<= lowbit highbit) ;otherwise we get 0?
                (natp lowbit)
                (natp highbit)
                (posp width)
                (natp amt))
           (equal (slice highbit lowbit (leftrotate width amt val))
                  (if (< highbit (mod amt width))
                      (slice (+ highbit width (- (mod amt width)))
                             (+ lowbit width (- (mod amt width)))
                             val)
                    (if (< lowbit (mod amt width))
                        (bvcat (+ highbit (- (mod amt width)) 1)
                               (slice (+ -1 width (- (mod amt width))) 0 val)
                               (- (mod amt width) lowbit)
                               (slice (+ -1 width)
                                      (+ lowbit width (- (mod amt width)))
                                      val))
                      (slice (+ highbit (- (mod amt width)))
                             (+ lowbit (- (mod amt width)))
                             val)))))
  :hints (("Goal" :in-theory (enable leftrotate natp))))

(defthm slice-of-leftrotate32
  (implies (and (< highbit 32) ;otherwise we can tighten the slice
                (<= lowbit highbit) ;otherwise we get 0?
                (natp lowbit)
                (natp highbit)
                (natp amt))
           (equal (slice highbit lowbit (leftrotate32 amt val))
                  (if (< highbit (mod amt 32))
                      (slice (+ highbit 32 (- (mod amt 32)))
                             (+ lowbit 32 (- (mod amt 32)))
                             val)
                    (if (< lowbit (mod amt 32))
                        (bvcat (+ highbit (- (mod amt 32)) 1)
                               (slice (+ -1 32 (- (mod amt 32))) 0 val)
                               (- (mod amt 32) lowbit)
                               (slice (+ -1 32)
                                      (+ lowbit 32 (- (mod amt 32)))
                                      val))
                      (slice (+ highbit (- (mod amt 32)))
                             (+ lowbit (- (mod amt 32)))
                             val)))))
  :hints (("Goal" :in-theory (enable leftrotate32 natp))))

(defthm bvif-of-logext-arg1
  (implies (and (<= n m)
                (integerp m)
                )
           (equal (bvif n test1 (logext m y) x)
                  (bvif n test1 y x)))
  :hints (("Goal" :in-theory (enable myif bvif))))

(defthm bvif-of-logext-arg2
  (implies (and (<= n m)
                (integerp m)
                )
           (equal (bvif n test1 x (logext m y))
                  (bvif n test1 x y)))
  :hints (("Goal" :in-theory (enable myif bvif bvif))))

;fixme rename
(defthm bvcat-of-logext-high-eric
  (implies (and (<= highsize size2)
                (integerp size2))
           (equal (bvcat highsize (logext size2 highval) lowsize lowval)
                  (bvcat highsize highval lowsize lowval)))
  :hints (("Goal" :in-theory (e/d (bvcat) ;yuck?
                                  ()))))

(defthm getbit-of-logext-high
  (implies (and (<= size n)
                (integerp size)
                (< 0 size)
                (natp n))
           (equal (getbit n (logext size x))
                  (getbit (+ -1 size) x)))
  :hints (("Goal" :in-theory (e/d (getbit-when-val-is-not-an-integer slice getbit
                                                                   logext)
                                  (slice-becomes-bvchop
                                   bvchop-of-logtail
                                   bvchop-of-logtail-becomes-slice
                                   logtail-of-bvchop-becomes-slice
;                                   bvchop-of-logtail-becomes-slice
                                   bvchop-1-becomes-getbit slice-becomes-getbit))
           :use (:instance usb-0-1 (x (slice (+ -1 size) (+ -1 size) x)))
           :cases ((integerp x)))))

(defthm bvshl-of-logext-arg2
  (implies (and (<= (+ (- shift-amount) width) m)
                (natp shift-amount)
                (natp m)
                )
           (equal (bvshl width (logext m x) shift-amount)
                  (bvshl width x shift-amount)))
  :hints (("Goal" :in-theory (enable bvshl))))

(defthm bvshr-of-logext-arg2
  (implies (and (<= WIDTH m)
                (posp width)
                (natp shift-amount)
                (posp m)
                )
           (equal (bvshr width (logext m x) shift-amount)
                  (bvshr width x shift-amount)))
  :hints (("Goal" :in-theory (enable bvshr))))

(DEFTHM bvminus-OF-LOGEXT-gen-arg2
  (IMPLIES (AND (<= SIZE1 SIZE2)
                (< 0 SIZE2)
                (NATP SIZE1)
                (NATP SIZE2))
           (EQUAL (bvminus SIZE1 Y (LOGEXT SIZE2 X))
                  (bvminus SIZE1 Y X)))
  :HINTS (("Goal" :IN-THEORY (enable bvminus))))

(DEFTHM bvminus-OF-LOGEXT-gen-arg1
  (IMPLIES (AND (<= SIZE1 SIZE2)
                (< 0 SIZE2)
                (NATP SIZE1)
                (NATP SIZE2))
           (EQUAL (bvminus SIZE1 (LOGEXT SIZE2 X) Y)
                  (bvminus SIZE1 X Y)))
  :HINTS (("Goal" :IN-THEORY (enable bvminus))))

;use trim?
(defthm bvuminus-of-logext
  (implies (and (<= size1 size2)
                (< 0 size2)
                (natp size1)
                (natp size2))
           (equal (bvuminus size1 (logext size2 x))
                  (bvuminus size1 x)))
  :hints (("Goal" :in-theory (e/d (bvuminus) (bvminus-becomes-bvplus-of-bvuminus)))))

(defthm bvmult-of-logext-gen-arg2
  (implies (and (<= size size2)
;                (integerp x)
 ;               (integerp y)
                (natp size)
                (integerp size2))
           (equal (bvmult size x (logext size2 y))
                  (bvmult size x y)))
  :hints (("Goal" :in-theory (e/d (bvmult) (bvchop-of-*)))))

(defthm bvmult-of-logext-gen-arg1
  (implies (and (<= size size2)
;                (integerp x)
 ;               (integerp y)
                (natp size)
                (integerp size2))
           (equal (bvmult size (logext size2 y) x)
                  (bvmult size y x)))
  :hints (("Goal" :use (:instance bvmult-of-logext-gen-arg2)
           :in-theory (disable bvmult-of-logext-gen-arg2))))

(defthmd equal-of-logext-and-logext
  (implies (and ;(integerp x)
                ;(integerp y)
                (posp size))
           (equal (equal (LOGEXT size x) (LOGEXT size y))
                  (equal (bvchop size x) (bvchop size y))))
  :hints (("Goal" :use (:instance ADD-BVCHOPS-TO-EQUALITY-OF-SBPS-4
                                  (newsize size)
                                  (y (LOGEXT size y))))))

;for when we prefer to know the logexts are equal (e.g., when we know signed-byte-p)
(defthmd equal-of-bvchop-and-bvchop
  (implies (posp n)
           (equal (equal (bvchop n x)
                         (bvchop n y))
                  (equal (logext n x)
                         (logext n y))))
  :hints (("Goal" :use (:instance equal-of-logext-and-logext (size n)))))

(defthm logext-of-+-of-bvchop
  (implies (and (integerp x)
                (integerp k))
           (equal (LOGEXT 32 (+ (bvchop 32 K) X))
                  (LOGEXT 32 (+ K X))))
  :hints (("Goal" :in-theory (enable equal-of-logext-and-logext))))

(defthmd signed-byte-p-when-unsigned-byte-p-one-less
  (implies (and (unsigned-byte-p (+ -1 n) x)
                (natp n)
                (< 0 n))
           (signed-byte-p n x))
  :hints (("Goal" :use (:instance backchain-signed-byte-p-to-unsigned-byte-p (size n) (i x))
           :in-theory (disable backchain-signed-byte-p-to-unsigned-byte-p))))

(defthm signed-byte-p-when-unsigned-byte-p
  (implies (and (unsigned-byte-p n x)
                (natp n)
                (< 0 n))
           (equal (signed-byte-p n x)
                  (unsigned-byte-p (+ -1 n) x)))
  :hints (("Goal" :in-theory (enable signed-byte-p-when-unsigned-byte-p-one-less))))

;fixme move
;restrict to constants?
(defthm logext-when-usb-cheap
  (implies (and (unsigned-byte-p free i)
                (<= free (+ -1 size))
                (natp size))
           (equal (logext size i)
                  i))
  :hints (("Goal" :use (:instance logext-identity))))

;or reorder the args to the bvplus (ignoring bvuminus)?
(defthm bvplus-of-bvplus-of-bvuminus
  (equal (bvplus size x (bvplus size y (bvuminus size x)))
         (bvchop size y))
  :hints (("Goal" :in-theory (e/d (bvuminus bvplus bvminus)
                                  (bvminus-becomes-bvplus-of-bvuminus
                                   ;anti-bvplus
                                   )))))

;-alt version?
;disable?
(defthm bvxor-tighten
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'newsize x) (newsize))
                (< newsize oldsize)
                (unsigned-byte-p-forced newsize x)
                (unsigned-byte-p newsize y)
                (natp newsize)
                (natp oldsize))
           (equal (bvxor oldsize x y)
                  (bvxor newsize x y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced bvxor))))

(defthm unsigned-byte-p-of-+-of-minus
  (implies (and (integerp x)
                (natp n)
                (integerp y))
           (equal (unsigned-byte-p n (+ x (- y)))
                  (booland (not (< x y))
                           (< (+ x (- y)) (expt 2 n)))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-of-+-of-minus-alt
  (implies (and (integerp x)
                (natp n)
                (integerp y))
           (equal (unsigned-byte-p n (+ (- y) x))
                  (booland (not (< x y))
                           (< (+ x (- y)) (expt 2 n)))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm bvcat-of-unary-minus-low
  (implies (and (integerp x)
                (natp highsize)
                (natp lowsize))
           (equal (bvcat highsize highval lowsize (unary-- x))
                  (bvcat highsize highval lowsize (bvuminus lowsize x))))
  :hints (("Goal" :in-theory (e/d (bvuminus bvminus) (bvminus-becomes-bvplus-of-bvuminus)))))

(defthm bvcat-of-unary-minus-high
  (implies (and (integerp x)
                (natp highsize)
                (natp lowsize))
           (equal (bvcat highsize (unary-- x) lowsize lowval)
                  (bvcat highsize (bvuminus highsize x) lowsize lowval)))
  :hints (("Goal" :in-theory (e/d (bvuminus bvminus) (bvminus-becomes-bvplus-of-bvuminus)))))

(defthm bitxor-of-unary-minus-arg1
  (implies (integerp x)
           (equal (bitxor (- x) y)
                  (bitxor (bvuminus 1 x) y)))
  :hints (("Goal" :in-theory (e/d (bvuminus bvminus) (bvminus-becomes-bvplus-of-bvuminus
                                                      BVUMINUS-1)))))

(defthm bitxor-of-unary-minus-arg2
  (implies (integerp y)
           (equal (bitxor x (- y))
                  (bitxor x (bvuminus 1 y))))
  :hints (("Goal" :use (:instance bitxor-of-unary-minus-arg1 (x y) (y x))
           :in-theory (disable bitxor-of-unary-minus-arg1))))

(defthm equal-constant-when-slice-equal-constant
  (implies (and (syntaxp (quotep const))
                (equal free (slice high low x))
                (syntaxp (and (quotep free)
                              (quotep high)
                              (quotep low)))
                ;;gets computed:
                (not (equal free (slice high low const)))
                )
           (not (equal const x))))

;version for bvchop?
(defthm equal-constant-when-not-slice-equal-constant
  (implies (and (syntaxp (quotep const))
                (not (equal free (slice high low x)))
                (syntaxp (and (quotep free)
                              (quotep high)
                              (quotep low)))
                ;;gets computed:
                (equal free (slice high low const))
                )
           (not (equal const x))))

;similar to UNSIGNED-BYTE-P-OF-BVCHOP-BIGGER2?
(defthmd slice-too-high-is-0-new
  (implies (and (unsigned-byte-p low (bvchop (+ 1 high) x))
                (integerp high))
           (equal (slice high low x) 0))
  :hints (("Goal" :in-theory (e/d (slice) (anti-slice)))))

(defthm slice-when-not-bvlt-free
  (implies (and (not (bvlt size free x))
                (syntaxp (and (quotep free)
                              (quotep size)))
                (equal size (+ 1 high))
                (bvlt size free (expt 2 low))
                (natp high) ;drop?
                (natp low)  ;drop?
                )
           (equal (slice high low x)
                  0))
  :hints (("Goal" :use (:instance slice-too-high-is-0-new)
           :in-theory (enable bvlt unsigned-byte-p))))

;gen
(defthm leftrotate-of-bvxor-32
  (equal (leftrotate 32 amt (bvxor 32 x y))
         (bvxor 32 (leftrotate 32 amt x)
                (leftrotate 32 amt y)))
  :hints (("Goal" :in-theory (enable leftrotate natp))))

(defthm leftrotate32-of-bvxor-32
  (equal (leftrotate32 amt (bvxor 32 x y))
         (bvxor 32 (leftrotate32 amt x)
                (leftrotate32 amt y)))
  :hints (("Goal" :in-theory (enable leftrotate32))))

;do we still need this?
(defthm bvmod-tighten
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'xsize x))
                (bind-free (bind-var-to-unsigned-term-size 'ysize y))
                (< (max xsize ysize) size)
                (force (unsigned-byte-p-forced xsize x))
                (force (unsigned-byte-p-forced ysize y))
                (natp size)
                (posp xsize))
           (equal (bvmod size x y)
                  (bvmod (max xsize ysize) x y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced bvmod))))

;rename
(defthm bvlt-of-bvmod-and-constant
  (implies (and (posp k)
                (natp size)
                (unsigned-byte-p size k))
           (bvlt size (bvmod size x k) k))
  :hints (("Goal" :in-theory (enable bvmod bvlt))))

(defthm <-of-constant-when-unsigned-byte-p-size-param
  (implies (and (syntaxp (quotep k))
                (<= k 0)
                (unsigned-byte-p size free))
           (not (< size k)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm bvdiv-and-bvmod-relationship-helper
  (implies (and (natp size)
;               (unsigned-byte-p size x)
                (unsigned-byte-p size y)
                )
           (equal (bvplus size (bvmult size y (bvdiv size x y)) (bvmod size x y))
                  (bvchop size x)))
  :hints (("Goal" :in-theory (enable mod bvdiv bvmod bvmult bvplus))))

(defthm bvdiv-and-bvmod-relationship
  (implies (unsigned-byte-p size x)
           (equal (bvplus size (bvmult size y (bvdiv size x y)) (bvmod size x y))
                  x))
  :hints (("Goal" :use (:instance bvdiv-and-bvmod-relationship-helper (y (bvchop size y))))))

(defthm bvdiv-and-bvmod-relationship-gen
  (equal (bvplus size (bvmult size y (bvdiv size x y)) (bvmod size x y))
         (bvchop size x))
  :hints (("Goal" :use (:instance bvdiv-and-bvmod-relationship-helper (y (bvchop size y))))))

(defthm logext-subst-constant-from-bvchop
  (implies (and (syntaxp (not (quotep x)))
                (equal (bvchop free x) k)
                (syntaxp (quotep k))
                (<= size free)
                (posp size)
                (integerp free)
                )
           (equal (logext size x)
                  (logext size k)))
  :hints (("Goal" :in-theory (e/d (logext) (;LOGBITP-BVCHOP
                                            )))))

(defthm getbit-when-slice-is-known-constant
  (implies (and (equal free (slice high low x)) ;reversed the equality
                (syntaxp (quotep free))
                (<= low n)
                (<= n high)
                (natp low)
                (integerp n)
                (integerp high))
           (equal (getbit n x)
                  (getbit (- n low) free))))

(defthmd rewrite-bv-equality-when-sizes-dont-match-core
  (implies (and (< x-size y-size)
                (unsigned-byte-p x-size x)
                (unsigned-byte-p y-size y)
                )
           (equal (equal x y)
                  (and (equal x (bvchop x-size y))
                       (equal (slice (+ -1 y-size) x-size y)
                              0))))
  :hints (("Goal" :in-theory (enable slice-too-high-is-0 usb-slice-helper))))

(defthm equal-of-slice-and-slice
  (implies (and (<= high1 high2)
                (<= low high1)
                (natp low)
                (natp high1)
                (natp high2))
           (equal (equal (slice high1 low x) (slice high2 low x))
                  (equal 0 (slice high2 (+ 1 high1) x))))
  :hints (("Goal"
           :in-theory (enable natp)
           :use (:instance rewrite-bv-equality-when-sizes-dont-match-core
                           (x (slice high1 low x))
                           (x-size (+ 1 (- high1 low)))
                           (y (slice high2 low x))
                           (y-size (+ 1 (- high2 low)))))))

(defthm equal-of-slice-and-slice-alt
  (implies (and (<= high1 high2)
                (<= low high1)
                (natp low)
                (natp high1)
                (natp high2))
           (equal (equal (slice high2 low x) (slice high1 low x))
                  (equal 0 (slice high2 (+ 1 high1) x))))
  :hints (("Goal" :use (:instance equal-of-slice-and-slice)
           :in-theory (disable equal-of-slice-and-slice))))

;move
(defthm not-equal-when-not-equal-bvchop
  (implies (and (syntaxp (quotep k))
                (not (equal free (bvchop size x)))
                (syntaxp (quotep free))
                (equal (bvchop size free) (bvchop size k)) ;gets computed
                (unsigned-byte-p size free)
                )
           (not (equal k x))))

;move
(defthm not-equal-bvchop-when-not-equal-bvchop
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (equal free (bvchop freesize x)))
                (syntaxp (and (quotep free)
                              (quotep freesize)))
                (<= freesize size)
                (equal (bvchop freesize free) (bvchop freesize k)) ;gets computed
                (unsigned-byte-p freesize free)
                (natp size)
                )
           (not (equal k (bvchop size x))))
  :hints (("Goal" :in-theory (enable BVCHOP-WHEN-SIZE-IS-NOT-NATP natp))))

;move
(defthm bvchop-of-sum-minus-expt-alt2
  (implies (and (integerp y)
                (natp size))
           (equal (bvchop size (+ (- (expt 2 size)) y))
                  (bvchop size y))))



;prove floor of one less?
(defthm logtail-of-one-less
  (implies (and (integerp x)
                (natp n))
           (equal (logtail n (+ -1 x))
                  (if (equal 0 (bvchop n x))
                      (+ -1 (logtail n x))
                    (logtail n x))))
  :hints (("Goal"
           :use (:instance FLOOR-PEEL-OFF-CONSTANT (k (+ -1 (expt 2 n))) (n x) (y (expt 2 n)))

           :in-theory (e/d (logtail bvchop) (FLOOR-PEEL-OFF-CONSTANT MOD-OF-EXPT-OF-2)))))

(defthm getbit-of-one-less
  (implies (and (integerp x)
                (natp n))
           (equal (getbit n (+ -1 x))
                  (if (equal 0 (bvchop n x))
                      (bitnot (getbit n x))
                    (getbit n x))))
  :hints (("Goal" :in-theory (e/d (getbit bvchop slice logtail bitnot mod-sum-cases)
                                  (MOD-OF-EXPT-OF-2 ;mod-of-expt-of-2-constant-version
                                                    bvchop-1-becomes-getbit slice-becomes-getbit anti-slice)))))

(DEFTHM bvchop-when-getbit-and-bvchop-known
  (IMPLIES (and (equal (getbit m x) k1)
                (syntaxp (quotep k1))
                (equal (bvchop m x) k2)
                (syntaxp (quotep k2))
                (equal m (+ -1 n))
                (posp N))
           (EQUAL (bvchop n x)
                  (bvcat 1 k1 (+ -1 n) k2))))

(defthm sbvlt-of-minus-one
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (equal k (+ -1 (expt 2 size))) ;minus one
                (unsigned-byte-p free x)
                (< free size)
                (natp size))
           (sbvlt size k x))
  :hints (("Goal" :in-theory (enable sbvlt-rewrite))))




;see leftrotate32-of-leftrotate32
;; (defthm leftrotate32-of-bvuminus-and-leftrotate32
;;   (implies (natp amt)
;;            (equal (leftrotate32 (bvuminus '5 amt) (leftrotate32 amt val))
;;                   (bvchop 32 val)))
;;   :hints (("Goal" :in-theory (e/d (leftrotate32 leftrotate bvuminus bvminus) (bvminus-becomes-bvplus-of-bvuminus)))))

;move
(defthm leftrotate32-of-leftrotate32
  (implies (and (natp k1)
                (natp k2))
           (equal (leftrotate32 k1 (leftrotate32 k2 x))
                  (leftrotate32 (bvplus 5 k1 k2) x)))
  :hints (("Goal" :in-theory (enable leftrotate32
                                     ;leftrotate
                                     ;;natp bvchop-of-sum-cases
                                     bvplus
                                     ))))

(defthm bvminus-of-bvchop-gen-arg2
  (implies (and (<= size1 size2)
                (integerp x)
                (integerp y)
                (< 0 size2)
                (natp size1)
                (natp size2))
           (equal (bvminus size1 y (bvchop size2 x))
                  (bvminus size1 y x)))
  :hints (("Goal"
           :in-theory (enable bvminus bvplus))))

(defthm bvchop-sum-minus-bvchop-arg1
  (implies (and (integerp x)
                (integerp y)
                (natp n))
           (equal (BVCHOP n (+ (- (BVCHOP n x)) y))
                  (BVCHOP n (+ (- x) y))))
  :hints (("Goal" :in-theory (e/d (bvminus) (;BVPLUS-RECOLLAPSE
                                             )))))

(defthm bvchop-sum-minus-bvchop-arg2-of-2
  (implies (and (integerp x)
                (integerp y)
                (natp n))
           (equal (BVCHOP n (+ y (- (BVCHOP n x))))
                  (BVCHOP n (+ y (- x)))))
  :hints (("Goal" :in-theory (enable bvminus))))

(DEFTHM BVCHOP-+-CANCEL-seconds
  (IMPLIES (AND (FORCE (INTEGERP SIZE))
                (>= SIZE 0)
                (FORCE (INTEGERP I))
                (FORCE (INTEGERP J))
                (FORCE (INTEGERP K)))
           (EQUAL (EQUAL (BVCHOP SIZE (+ J I))
                         (BVCHOP SIZE (+ K I)))
                  (EQUAL (BVCHOP SIZE J)
                         (BVCHOP SIZE K)))))

(defthm bvchop-minus-equal-bvchop-minus
  (IMPLIES (AND (NATP N)
                (INTEGERP FREE)
                (INTEGERP X)
                (INTEGERP Y))
           (equal (EQUAL (BVCHOP N (- X))
                         (BVCHOP N (- FREE)))
                  (EQUAL (BVCHOP N X)
                         (BVCHOP N FREE))))
  :hints (("Goal" :in-theory (e/d (bvchop) (MOD-OF-EXPT-OF-2)))))

;do we need this?
(DEFTHMd BVCHOP-SUM-SUBST-minus
  (IMPLIES (AND (EQUAL (BVCHOP N X) (BVCHOP N FREE))
                (SYNTAXP (SMALLER-TERMP FREE X))
                (NATP N)
                (INTEGERP FREE)
                (INTEGERP X)
                (INTEGERP Y))
           (EQUAL (BVCHOP N (+ (- X) Y))
                  (BVCHOP N (+ (- FREE) Y))))
  :hints (("Goal" :in-theory (disable ))))

(defthmd bvchop-sum-subst
  (implies (and (equal (bvchop n x) (bvchop n free))
                (syntaxp (smaller-termp free x))
                (natp n)
                (integerp free)
                (integerp x)
                (integerp y)
                )
           (equal (bvchop n (+ x y))
                  (bvchop n (+ free y))))
  :hints (("Goal" :in-theory (disable BVCHOP-SUM-DROP-BVCHOP)
           :use ((:instance BVCHOP-SUM-DROP-BVCHOP (m n) (y x) (z y))
                 (:instance BVCHOP-SUM-DROP-BVCHOP (m n) (y free) (z y))))))

(defthm equal-bvchop-bvchop-move-minus
  (implies (and (natp n)
                (integerp x)
                (integerp y)
                (integerp z))
           (equal (EQUAL (BVCHOP N X) (BVCHOP N (+ (- y) z)))
                  (equal (bvchop n (+ x y)) (bvchop n z))))
  :hints (("Goal"
           :use ((:instance BVCHOP-SUM-SUBST (x x) (free (+ (- Y) Z)) (y y))
                 (:instance BVCHOP-SUM-SUBST (x z) (free (+ x y)) (y (- y))))

           :in-theory (e/d (bvminus )
                           (;BVPLUS-RECOLLAPSE ;BVCHOP-SUM-MINUS-BVCHOP-ARG2-OF-2
                            )))))

(defthm equal-bvchop-bvchop-move-minus2
  (implies (and (natp n)
                (integerp x)
                (integerp y)
                (integerp z))
           (equal (EQUAL (BVCHOP N X) (BVCHOP N (+ z (- y))))
                  (equal (bvchop n (+ x y)) (bvchop n z))))
  :hints (("Goal"
           :use ((:instance BVCHOP-SUM-SUBST (x x) (free (+ (- Y) Z)) (y y))
                 (:instance BVCHOP-SUM-SUBST (x z) (free (+ x y)) (y (- y))))

           :in-theory (e/d (bvminus )
                           (;BVPLUS-RECOLLAPSE ;BVCHOP-SUM-MINUS-BVCHOP-ARG2-OF-2
                            )))))

;fixme drop hyps
;solve to get a constant (or we could move the minus to the other side and solve the resulting plus)
(defthm bvminus-solve
  (implies (and (syntaxp (and (quotep n)
                              (quotep k)
                              (quotep k2)))
                (natp n)
                (integerp x)
                (integerp k)
                (integerp k2))
           (equal (equal k (bvminus n k2 x))
                  (and (equal (bvchop n x) (bvminus n k2 k))
                       (unsigned-byte-p n k))))
  :hints (("Goal"
;          :use (:instance BVCHOP-SUM-SUBST-minus (x k) (free (+ K2 (- X))) (y k2))
           :use ((:instance equal-bvchop-bvchop-move-minus (x x) (y k) (z k2))
                 (:instance equal-bvchop-bvchop-move-minus (x k) (y x) (z k2)))
           :in-theory (e/d (bvminus )
                           (;BVPLUS-RECOLLAPSE
                            BVCHOP-SUM-MINUS-BVCHOP-ARG2-OF-2
                                              EQUAL-BVCHOP-BVCHOP-MOVE-MINUS2
                            equal-bvchop-bvchop-move-minus
                            )))))

(defthm bvminus-solve2
  (implies (and (syntaxp (and (quotep n)
                              (quotep k)
                              (quotep k2)))
                (natp n)
                (integerp x)
                (integerp k)
                (integerp k2))
           (equal (equal k (bvminus n x k2))
                  (and (equal (bvchop n x) (bvplus n k2 k))
                       (unsigned-byte-p n k))))
  :hints (("Goal"
;          :use (:instance BVCHOP-SUM-SUBST-minus (x k) (free (+ K2 (- X))) (y k2))
           :use ((:instance equal-bvchop-bvchop-move-minus (x k) (y k2) (z x))
;                 (:instance equal-bvchop-bvchop-move-minus (x k) (y x) (z x))
                 )
           :in-theory (e/d (bvminus
                            bvplus
                                    )
                           (;BVPLUS-RECOLLAPSE ;BVCHOP-SUM-MINUS-BVCHOP-ARG2-OF-2
;                            bvminus
                            equal-bvchop-bvchop-move-minus
                            ;anti-bvplus
                            )))))


;bozo add bvplus solve rules like we have for bvminus...
;there's probably a whole theory of that stuff (maybe use bvuminus)


;bozo extend to bvplus
(defthm bvchop-sum-solve-for-constant-arg1
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)
                              (quotep n)))
                (integerp x)
                (integerp k1)
                (integerp k2)
                (natp n)
                )
           (equal (equal k1 (bvchop n (+ k2 x)))
                  (and (unsigned-byte-p n k1)
                       (equal (bvchop n x) (bvchop n (- k1 k2)))))))

(defthm bvchop-sum-solve-for-constant-arg2
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)
                              (quotep n)))
                (integerp x)
                (integerp k1)
                (integerp k2)
                (natp n)
                )
           (equal (equal k1 (bvchop n (+ x k2)))
                  (and (unsigned-byte-p n k1)
                       (equal (bvchop n x) (bvchop n (- k1 k2))))))
  :hints (("Goal" :in-theory (disable ;bvplus-recollapse
                              ))))

(defthm bvchop-of-sum-of-minus-of-bvchop-gen-arg2
  (implies (and (<= size size2)
                (natp size2)
;                (natp size)
                (integerp x)
                (integerp Y)
                )
           (equal (bvchop size (+ x (- (bvchop size2 y))))
                  (bvchop size (+ x (- y)))))
  :hints (("Goal" :in-theory (disable ;BVPLUS-RECOLLAPSE
                              EQUAL-BVCHOP-BVCHOP-MOVE-MINUS2))))

;no hyps about size
(defthm bvchop-of-sum-of-minus-of-bvchop-same
  (implies (and (integerp x)
                (integerp Y)
                )
           (equal (bvchop size (+ x (- (bvchop size y))))
                  (bvchop size (+ x (- y)))))
  :hints (("Goal" :in-theory (disable ;BVPLUS-RECOLLAPSE
                              EQUAL-BVCHOP-BVCHOP-MOVE-MINUS2))))

(defthm bvchop-of-sum-of-minus-of-bvchop-gen-arg3
  (implies (and (<= size size2)
                (natp size2)
;                (natp size)
                (integerp x)
                (integerp Y)
                (integerp w)
                )
           (equal (bvchop size (+ w x (- (bvchop size2 y))))
                  (bvchop size (+ w x (- y)))))
  :hints (("Goal" :in-theory (disable ;BVPLUS-RECOLLAPSE
                              ))))

;no hyps on size
(defthm bvchop-of-sum-of-minus-of-bvchop-same-alt
  (implies (and (integerp x)
                (integerp Y)
                (integerp w)
                )
           (equal (bvchop size (+ w x (- (bvchop size y))))
                  (bvchop size (+ w x (- y)))))
  :hints (("Goal" :use (:instance bvchop-of-sum-of-minus-of-bvchop-same (x (+ w x))))))

(defthm bvchop-of-sum-of-bvchop-gen-arg3
  (implies (and (<= size size2)
                (natp size2)
 ;               (natp size)
                (integerp x)
                (integerp Y)
                (integerp w)
                )
           (equal (bvchop size (+ w x (bvchop size2 y)))
                  (bvchop size (+ w x y))))
  :hints (("Goal" :in-theory (disable ;BVPLUS-RECOLLAPSE
                              ))))

;no hyps on size
(defthm bvchop-of-sum-of-bvchop-same-alt
  (implies (and (integerp x)
                (integerp Y)
                (integerp w))
           (equal (bvchop size (+ w x (bvchop size y)))
                  (bvchop size (+ w x y)))))

;; ;use trim
;; (defthm bitxor-of-bvor-arg1
;;   (implies (and (< 1 n)
;;                 (natp n))
;;            (equal (bitxor (bvor n x y) z)
;;                   (bitxor (bvor 1 x y) z)))
;;   :hints (("Goal" :use ((:instance bitxor-of-bvchop-arg1 (x (bvor n x y)) (n 1) (y z))
;;                         (:instance bitxor-of-bvchop-arg1 (x (bvor 1 x y)) (n 1) (y z)))
;;            :in-theory (disable bitxor-of-bvchop-arg1 bitxor-of-bvchop-arg2 BITXOR-OF-GETBIT-ARG1 ;BITXOR-OF-GETBIT-ARG2
;;                                ))))

;; ;use trim
;; (defthm bitxor-of-bvor-arg2
;;   (implies (and (< 1 n)
;;                 (natp n))
;;            (equal (bitxor z (bvor n x y))
;;                   (bitxor z (bvor 1 x y))))
;;   :hints (("Goal" :use ((:instance bitxor-of-bvchop-arg1 (x (bvor n x y)) (n 1) (y z))
;;                         (:instance bitxor-of-bvchop-arg1 (x (bvor 1 x y)) (n 1) (y z)))
;;            :in-theory (disable bitxor-of-bvchop-arg1 bitxor-of-bvchop-arg2 BITXOR-OF-GETBIT-ARG1 BITXOR-OF-BVOR-ARG1))))


(local
 (defthm slice-when-bvlt-gen-helper
   (implies (and (bvlt size x free)
                 (<= (+ 1 high) size)
                 (<= (bvchop size free) (expt 2 low))
                 (natp high)
                 (natp low)
                 (unsigned-byte-p size x) ;dropped below
                 )
            (equal (slice high low x)
                   0))
   :hints (("Goal" :in-theory (enable bvlt slice-too-high-helper)))))

(defthm slice-when-bvlt-gen
  (implies (and (bvlt size x free) ;size is also free
                (syntaxp (and (quotep free)
                              (quotep size)
                              (quotep low)
                              (quotep high)))
                (<= (+ 1 high) size)
                (<= (bvchop size free) (expt 2 low))
                (natp high)
                (natp low))
           (equal (slice high low x)
                  0))
  :hints (("Goal" :use (:instance slice-when-bvlt-gen-helper (x (bvchop size x)))
           :in-theory (disable slice-when-bvlt-gen-helper))))

;the integerp hyps are needed because bvplus ifixes its arguments - should it?
;disabled for library proofs
(defthmd bvlt-of-plus-arg2
  (implies (and (integerp y)
                (integerp z))
           (equal (bvlt size x (+ y z))
                  (bvlt size x (bvplus size y z))))
  :hints (("Goal" :in-theory (e/d (bvlt bvchop-of-sum-cases bvplus bvuminus bvminus)
                                  (<-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free bvminus-becomes-bvplus-of-bvuminus)))))

;the integerp hyps are needed because bvplus ifixes its arguments - should it?
;disabled for library proofs
(defthmd bvlt-of-plus-arg1
  (implies (and (integerp y)
                (integerp z))
           (equal (bvlt size (+ y z) x)
                  (bvlt size (bvplus size y z) x)))
  :hints (("Goal" :in-theory (e/d (bvlt bvchop-of-sum-cases bvplus bvuminus bvminus)
                                  (<-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free bvminus-becomes-bvplus-of-bvuminus)))))

(defthm equal-of-bitxor-and-bitor
  (equal (equal (bitxor x y) (bitor x y))
         (equal 0 (bitand x y)))
  :hints (("Goal" :cases ((equal 1 (getbit 0 x))))))

(defthm bitxor-of-bvcat-irrel-arg2
  (implies (and (posp lowsize)
                (posp highsize) ;drop?
                )
           (equal (bitxor x (bvcat highsize highval lowsize lowval))
                  (bitxor x lowval))))

(defthm bitxor-of-bvcat-irrel-arg1
  (implies (and (posp lowsize)
                (posp highsize) ;drop?
                )
           (equal (bitxor (bvcat highsize highval lowsize lowval) x)
                  (bitxor lowval x))))

(defthm equal-of-bvplus-constant-and-constant
  (implies (and (syntaxp (quotep k1))
                (syntaxp (quotep k2))
                (syntaxp (quotep size))
                (natp size))
           (equal (equal k1 (bvplus size k2 x))
                  (and (unsigned-byte-p size k1)
                       (equal (bvminus size k1 k2) (bvchop size x)))))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p bvlt bvchop-of-sum-cases bvplus bvuminus bvminus
                                                   bvchop-when-i-is-not-an-integer)
                                  ( bvminus-becomes-bvplus-of-bvuminus bvlt-of-plus-arg2 bvlt-of-plus-arg1
                                                                       <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free
                                                                       )))))

(defthm equal-of-bvplus-constant-and-constant-alt
  (implies (and (syntaxp (quotep k1))
                (syntaxp (quotep k2))
                (syntaxp (quotep size))
                (natp size))
           (equal (equal (bvplus size k2 x) k1)
                  (and (unsigned-byte-p size k1)
                       (equal (bvminus size k1 k2)
                              (bvchop size x)))))
  :hints (("Goal" :use (:instance equal-of-bvplus-constant-and-constant)
           :in-theory (disable equal-of-bvplus-constant-and-constant))))

(defthmd bvplus-drop
  (implies (and (< (+ x y) (expt 2 32))
                (natp x)
                (natp y))
           (equal (bvplus 32 x y)
                  (+ x y))))

(defthm logext-when-non-negative-becomes-bvchop
  (implies (<= 0 (logext size x))
           (equal (logext size x)
                  (bvchop (+ -1 size) x)))
  :rule-classes ((:rewrite :backchain-limit-lst (1)))
  :hints (("Goal" :in-theory (enable logext logapp))))

;compare to UNSIGNED-BYTE-P-TIGHTEN and USB-HACK
(defthm unsigned-byte-p-when-top-bit-0
  (implies (and (equal free (getbit freeindex x)) ; free vars for poor man's backchain limit?
                (equal 0 free)
                (equal freeindex (+ -1 size))
                (< 0 size))
           (equal (unsigned-byte-p size x)
                  (and (unsigned-byte-p freeindex x)
                       (integerp size))))
  :hints (("Goal" :in-theory (e/d (posp)
                                  (equal-of-bvchop-and-bvchop-same
                                   bvchop-when-top-bit-not-1-fake-free))
           :use (:instance split-with-bvcat (hs 1) (ls (+ -1 size))))))

(defthmd logext-drop
  (implies (and (not (sbvlt 32 x 0))
                (unsigned-byte-p 32 x))
           (equal (logext 32 x)
                  x))
  :hints (("Goal" :in-theory (enable SBVLT))))

(defthmd <-of-logext-and-0
  (implies (posp size)
           (equal (< (logext size k) 0)
                  (equal 1 (getbit (+ -1 size) k))))
  :hints (("Goal" :in-theory (enable logext))))

;rename
(defthm equal-of-maxint-when-sbvlt
  (implies (sbvlt 32 x y)
           (not (equal 2147483647 (bvchop 32 x))))
  :hints (("Goal" :in-theory (enable sbvlt-rewrite))))

(defthm bvchop-plus-1-split
  (implies (and (syntaxp (not (quotep n))) ;defeats acl2's overaggressive matching
                (integerp n)
                (natp size))
           (equal (bvchop size (+ 1 n))
                  (if (equal (bvchop size n) (+ -1 (expt 2 size)))
                      0
                    (+ 1 (bvchop size n)))))
  :hints (("Goal" :in-theory (e/d (bvchop mod-sum-cases) (MOD-OF-EXPT-OF-2)))))

(defthm bvchop-reduce-when-all-but-top-bit-known
  (implies (and (equal (bvchop 31 x) free)
                (syntaxp (quotep free)))
           (equal (bvchop 32 x)
                  (bvcat 1 (getbit 31 x) 31 free))))

(defthm <-of-bvchop-hack
  (IMPLIES (NATP HIGH)
           (equal (< (BVCHOP (+ 1 HIGH) X) (EXPT 2 HIGH))
                  (not (EQUAL 1 (GETBIT HIGH X)))))
  :hints (("Goal" :use (:instance split-with-bvcat (x x) (hs 1) (ls high))
           :in-theory (e/d (bvcat logapp) ())
           )))

(defthmd getbit-when-bvlt-of-small-helper
  (implies (and (bvlt (+ 1 size) x (expt 2 size))
                (natp size))
           (equal (getbit size x)
                  0))
  :hints (("Goal" :in-theory (e/d (bvlt)
                                  (BVCAT-SLICE-SAME ;BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE
                                   SLICE-BECOMES-GETBIT
                                   BVCHOP-1-BECOMES-GETBIT
                                   BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

(defthm getbit-when-bvlt-of-small
  (implies (and (bvlt (+ 1 size) x free)
                (not (bvlt (+ 1 size) (expt 2 size) free))
                (natp size))
           (equal (getbit size x)
                  0))
  :hints (("Goal" :use (:instance getbit-when-bvlt-of-small-helper))))

; x<=y implies x<=y+1 (assuming incrementing y does not wrap around)
(defthm sbvlt-of-bvplus-of-1
  (implies (and (sbvlt 32 x y)
                (not (equal (+ -1 (expt 2 31)) (bvchop 32 y))))
           (sbvlt 32 x (bvplus 32 1 y)))
  :hints (("Goal" :in-theory (enable bvplus bvlt sbvlt-rewrite
                                     getbit-when-bvlt-of-small-helper))))



;gen!
(defthm getbit-of-plus-of-expt-2
  (implies (integerp x)
           (equal (GETBIT 31 (+ 2147483648 x))
                  (if (equal 0 (GETBIT 31 x))
                      1
                    0)))
  :hints (("Goal" :in-theory (e/d (getbit SLICE-OF-SUM-CASES) (SLICE-BECOMES-GETBIT BVCHOP-1-BECOMES-GETBIT)))))


;gen
(defthm slice-of-minus-of-expt
  (implies (posp size)
           (equal (SLICE (+ -1 SIZE) 1 (- (EXPT 2 SIZE)))
                  0))
  :hints (("Goal" :in-theory (e/d (slice LOGTAIL bvchop
                                         expt-of-+ ;;EXPONENTS-ADD-unrestricted
                                         )
                                  (BVCHOP-OF-LOGTAIL-BECOMES-SLICE
                                   MOD-OF-EXPT-OF-2)))))



(defthm bvchop-of-times-of-expt-and-/-of-expt
  (implies (and (natp low)
                (natp high))
           (equal (BVCHOP (+ HIGH (- LOW)) (* (EXPT 2 HIGH) (/ (EXPT 2 LOW))))
                  0))
  :hints (("Goal" :use (:instance bvchop-of-expt-0 (size1 (- high low)) (size2 (- high low)))
           :in-theory (e/d (expt-of-+) (bvchop-of-expt-0 BVCHOP-OF-EXPT-2-N)))))

(local (in-theory (disable LOGTAIL-LESSP))) ;todo


(defthm bvlt-tighten-when-getbit-0
  (implies (and (equal (getbit 31 x) 0)
                (unsigned-byte-p 31 z))
           (equal (bvlt 32 z x)
                  (bvlt 31 z x)))
  :hints (("Goal" :in-theory (e/d (bvlt) ( ;<-becomes-bvlt
                                          <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free
 ;                                         bvchop-extend-hack-gen
                                          )))))

(defthm bvlt-tighten-when-getbit-0-alt
  (implies (and (equal (getbit 31 x) 0)
                (unsigned-byte-p 31 z))
           (equal (bvlt 32 x z)
                  (bvlt 31 x z)))
  :rule-classes ((:rewrite :backchain-limit-lst (1 1)))
  :hints (("Goal" :in-theory (e/d (bvlt) ( ;<-becomes-bvlt
                                          <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free
;                                          bvchop-extend-hack-gen
                                          )))))

(defthm bvle-tighten-32-31
  (implies (and (syntaxp (quotep k))
                (UNSIGNED-BYTE-P 31 x))
           (equal (BVLT 32 x k)
                  (if (bvle 32 (expt 2 31) k)
                      t
                    (bvlt 31 x k))))
  :hints (("Goal"
           :use ((:instance split-with-bvcat (x k) (hs 1) (ls 31)))
           :in-theory (e/d (sbvdivdown bvlt getbit-when-bvlt-of-small-helper)
                           (<-becomes-bvlt <-becomes-bvlt-alt
                                           EQUAL-OF-BVCHOP-AND-BVCHOP-SAME
                                           BVCAT-SLICE-SAME BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE BVCAT-OF-GETBIT-AND-X-ADJACENT)))))

(defthm bvchop-plus-bvchop-bound
  (implies (integerp size)
           (< (+ (bvchop (+ -1 size) x) (bvchop (+ -1 size) y)) (expt 2 size)))
  :hints (("Goal" :in-theory (e/d (expt-of-+)( bvchop-upper-bound))
           :use ((:instance bvchop-upper-bound (n (+ -1 size)) (x x))
                 (:instance bvchop-upper-bound (n (+ -1 size)) (x y))))))


;trying disabled.
;just go to getbit of bvplus?
(defthmd getbit-of-plus
  (implies (and (integerp x)
                (natp size)
                (integerp y)
                )
           (equal (getbit size (+ x y))
                  (if (>= (bvplus (+ 1 size) (bvchop size x) (bvchop size y))
                          (expt 2 size))
                      (bitnot (bitxor (getbit size x) (getbit size y)))
                    (bitxor (getbit size x) (getbit size y)))))
  :hints (("Goal"
           :use ((:instance usb1-cases (x (LOGTAIL size (BVCHOP (+ 1 size) Y))))
                 (:instance usb1-cases (x (LOGTAIL size (BVCHOP (+ 1 size) x)))))
           :in-theory (e/d (bitnot getbit slice BVCHOP-OF-SUM-CASES bvplus logtail-of-bvchop)
                           ( anti-slice bvchop-of-logtail
; Matt K. mod 5/2016 (type-set bit for {1})
;bitp-bvchop-1
                                        )))))


;;only the lowest bit is of interest
;move
(defthm integerp-of-*-of-1/2-and-mod-of-expt
  (implies (and (posp size)
                (rationalp x))
           (equal (integerp (* 1/2 (mod x (expt 2 size))))
                  (integerp (* 1/2 x))))
  :hints (("Goal" :in-theory (e/d (expt) (expt-hack)))))

(defthm LOGEXT-of-plus
  (implies (and (integerp x)
                (posp size)
                (integerp y)
                )
           (equal (logext size (+ x y))
                  (if (>= (+ (logext size x) (logext size y))
                          (expt 2 (+ -1 size)))
                      (- (+ (logext size x) (logext size y))
                         (expt 2 size))
                    (if (< (+ (logext size x) (logext size y))
                           (- (expt 2 (+ -1 size))))
                        (+ (+ (logext size x) (logext size y))
                           (expt 2 size))
                      (+ (logext size x) (logext size y))))))
  :hints (("Goal"
           :use (:instance bvchop-plus-bvchop-bound)
           :in-theory (e/d (logapp logext LOGAPP-0 bvplus BVCHOP-OF-SUM-CASES getbit-of-plus bvchop mod-sum-cases)
                           (TIMES-4-BECOMES-LOGAPP  bvchop-plus-bvchop-bound expt
                                                    MOD-EXPT-SPLIT ;bad rule!
                                                    )))))

;todo: prove a getbit-of-sum-cases rule?  does it already exist?  see getbit-of-plus
;; (thm
;;  (equal (GETBIT 31 (+ x y))


;gen the 0 to any constant!
(defthm sbvlt-of-bvplus-of-constant-and-0
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p 31 k) ;gen?
                (bvlt 32 0 k)
                )
           (equal (sbvlt 32 (bvplus 32 k x) 0)
                  (or (sbvle 32 (- (expt 2 31) k) x)
                      (sbvlt 32 x (- k)))))
  :hints (("Goal" :in-theory (e/d (sbvlt bvplus LOGEXT-CASES BVUMINUS bvminus)
                                  (sbvlt-rewrite <-of-logext-and-0-alt BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

(defthm getbit-of+-of-4294967296
 (implies (integerp x)
          (equal (GETBIT 31 (+ 4294967296 x))
                 (GETBIT 31 x)))
 :hints (("Goal" :in-theory (e/d (getbit) (SLICE-BECOMES-GETBIT BVCHOP-1-BECOMES-GETBIT)))))

(defthm sbvlt-of-bvuminus
  (implies (unsigned-byte-p 32 x)
           (equal (SBVLT 32 (BVUMINUS 32 x) 0)
                  (if (equal x (expt 2 31))
                      t
                    (SBVLT 32 0 x))))
  :hints (("Goal"
           :use ((:instance integerp-squeeze
                            (x (* x 1/2147483648)))
                 (:instance SPLIT-BV
                            (y x)
                            (n 32)
                            (m 31)))
           :in-theory (e/d ( ;; sbvlt-rewrite
                            sbvlt logext logapp
                            logtail
                            BVUMINUS BVMINUS bvlt getbit slice SBVLT-rewrite
                            ;;INTEGERP-OF-*-OF-/-BECOMES-EQUAL-OF-0-AND-MOD ;looped
                            bvcat)
                           (<-OF-*-AND-*-SAME-LINEAR ;why?
                            BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                            SLICE-BECOMES-GETBIT
                            BVCHOP-1-BECOMES-GETBIT
                            BVCHOP-OF-LOGTAIL-BECOMES-SLICE
                            <-OF-LOGEXT-AND-0-ALT)))))

;gen the 0 to any constant!
(defthm sbvlt-of-bvplus-of-0-and-constant
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p 31 k) ;gen?
                (bvlt 32 0 k)
                )
           (equal (sbvlt 32 0 (bvplus 32 k x))
                  (and (sbvlt 32 (- k) x)
                       (sbvlt 32 x (- (expt 2 31) k)))))
  :hints (("Goal" :in-theory (e/d (sbvlt bvplus LOGEXT-CASES BVUMINUS bvminus)
                                  (sbvlt-rewrite <-of-logext-and-0-alt BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

;trying enabled..
(defthm <-of-bvplus-of-minus-1
  (implies (and (unsigned-byte-p 32 n)
                (sbvlt 32 0 n))
           (< (bvplus 32 4294967295 n) n))
  :hints (("Goal" :in-theory (enable bvplus sbvlt bvchop-of-sum-cases; BVPLUS-OF-MINUS-1
                                     ))))

(defthm bvmult-of-bvplus-1
  (equal (bvmult '32 (bvplus '32 x y) z)
         (bvplus '32 (bvmult '32 x z) (bvmult '32 y z)))
  :hints (("Goal" :in-theory (enable bvmult bvplus))))

(defthm bvmult-of-bvplus-2
  (equal (bvmult '32 z (bvplus '32 x y))
         (bvplus '32 (bvmult '32 x z) (bvmult '32 y z)))
  :hints (("Goal" :in-theory (enable bvmult bvplus))))

(defthm bvmult-of-bvminus-1
  (equal (bvmult '32 (bvminus '32 x y) z)
         (bvminus '32 (bvmult '32 x z) (bvmult '32 y z)))
  :hints (("Goal" :in-theory (enable bvmult bvminus))))

(defthm bvmult-of-bvminus-2
  (equal (bvmult '32 z (bvminus '32 x y))
         (bvminus '32 (bvmult '32 z x) (bvmult '32 z y)))
  :hints (("Goal" :in-theory (enable bvmult bvminus))))

;needed for termination of loop functions
(defthm <-of-bvminus-of-1-alt
  (implies (and (unsigned-byte-p 32 n)
                (sbvlt 32 0 n))
           (< (bvminus 32 n 1) n))
  :hints (("Goal" :in-theory (enable bvminus; -becomes-bvplus-of-bvuminus
                                     bvchop-of-sum-cases
                                     ))))

;newly disabled remove all the disables later
(defthmd <-of-bvplus-becomes-bvlt-arg1
  (implies (and (unsigned-byte-p size y)
                (natp size) ;drop
                )
           (equal (< (bvplus size x z) y)
                  (bvlt size (bvplus size x z) y)))
  :hints (("Goal" :in-theory (e/d (bvlt) (<-BECOMES-BVLT <-BECOMES-BVLT-alt
                                                         EQUAL-OF-+-AND-BV ;looped
                                                         )))))

(defthmd <-of-bvplus-becomes-bvlt-arg2
  (implies (and (unsigned-byte-p size y)
                (natp size) ;drop
                )
           (equal (< y (bvplus size x z))
                  (bvlt size y (bvplus size x z))))
  :hints (("Goal" :in-theory (e/d (bvlt) (<-BECOMES-BVLT <-BECOMES-BVLT-alt)))))

(defthmd bvlt-add-to-both-sides
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (natp size)
                )
           (equal (bvlt size x y)
                  (if (bvlt size x (bvuminus size z))
                      (if (bvlt size y (bvuminus size z))
                          ;;neither overflows
                          (bvlt size (bvplus size x z) (bvplus size y z))
                        ;; y overflows b x does not
                        t)
                    (if (bvlt size y (bvuminus size z))
                        ;;x overflows but y does not
                        nil
                      ;;both overflow
                      (bvlt size (bvplus size x z) (bvplus size y z))))))
  :hints (("Goal" :in-theory (e/d (bvlt bvchop-of-sum-cases bvplus bvuminus bvminus)
                                  ( bvminus-becomes-bvplus-of-bvuminus bvlt-of-plus-arg2 bvlt-of-plus-arg1
                                                <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free
)))))

(defthm bvlt-of-bvplus-and-bvplus-cancel-helper
  (implies (natp size)
           (equal (bvlt size (bvplus size y x) (bvplus size z x))
                  (if (bvlt size (bvplus size y x) (bvuminus size (bvuminus size x)))
                      (if (bvlt size (bvplus size z x) x) ;simplify?!
                          (bvlt size y z)
                        t)
                    (if (bvlt size (bvplus size z x) x) ;simplify?!

                        nil
                      (bvlt size y z)))))
  :hints (("Goal"
           :cases ((equal 0 (BVCHOP SIZE z)))
           :use (:instance bvlt-add-to-both-sides (x (bvplus size y x))
                           (y (bvplus size z x))
                           (z (bvuminus size x))))))

(defthm bvlt-of-bvplus-same
  (implies (natp size)
           (equal (bvlt size (bvplus size x y) x)
                  (if (equal 0 (bvchop size y))
                      nil ;move the bvuminus?
                    (bvle size (bvuminus size y) x))))
  :hints (("Goal" :in-theory (e/d (bvlt bvchop-of-sum-cases bvplus bvuminus bvminus)
                                  ( bvminus-becomes-bvplus-of-bvuminus bvlt-of-plus-arg2 bvlt-of-plus-arg1
                                                <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free
)))))

(defthm bvlt-of-bvplus-same-alt
  (implies (natp size)
           (equal (bvlt size (bvplus size y x) x)
                  (if (equal 0 (bvchop size y))
                      nil
                    (bvle size (bvuminus size y) x))))
  :hints (("Goal" :use (:instance bvlt-of-bvplus-same)
           :in-theory (disable bvlt-of-bvplus-same))))

;ffixme simplify rhs?
(defthm bvlt-of-bvplus-and-bvplus-cancel
  (implies (natp size)
           (equal (bvlt size (bvplus size y x) (bvplus size z x))
                  (if (and (not (equal 0 (bvchop size y)))
                           (bvle size (bvuminus size y) x))
                      (if (and (not (equal 0 (bvchop size z)))
                               (bvle size (bvuminus size z) x))
                          (bvlt size y z)
                        t)
                    (if (and (not (equal 0 (bvchop size z)))
                             (bvle size (bvuminus size z) x))
                        nil
                      (bvlt size y z)))))
  :hints (("Goal" :use (bvlt-of-bvplus-same-alt
                        (:instance bvlt-of-bvplus-same-alt (y z)) ;ffixme investigate the need for this
                        (:instance bvlt-of-bvplus-and-bvplus-cancel-helper))
           :in-theory (disable bvlt-of-bvplus-same-alt
                               bvlt-of-bvplus-and-bvplus-cancel-helper))))

(defthm bvlt-of-constant-when-<-of-constant
  (implies (and (syntaxp (quotep k2))
                (< i k1)
                (syntaxp (and (quotep k1)
                              (quotep size)))
                (<= k1 (bvchop size k2)) ;gets computed
                (natp i)
                (natp size))
           (bvlt size i k2))
  :hints (("Goal" :in-theory (enable bvlt))))

;this is for when x is a bit-vector that's obviously less than k
;drop special cases of this rule?
(defthm bvlt-when-bound
  (implies (and (syntaxp (quotep k))
                (bind-free (bind-var-to-unsigned-term-size 'xsize x))
                (< xsize size)
                (natp size)
                (bvle size (expt 2 xsize) k)
                (force (unsigned-byte-p-forced xsize x)))
           (bvlt size x k))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p UNSIGNED-BYTE-P-FORCED) (<-becomes-bvlt <-becomes-bvlt-alt)))))

(defthm bvuminus-when-smaller
  (implies (and (unsigned-byte-p free x)
                (< free size)
                (natp size))
           (equal (bvuminus size x)
                  (if (equal 0 x)
                      0
                    (bvplus size (- (expt 2 size) (expt 2 free)) (bvuminus free x)))))
;   :rule-classes ((:rewrite :backchain-limit-lst (1)))
  :hints (("Goal" :in-theory (e/d (bvuminus bvminus bvplus unsigned-byte-p) ( bvminus-becomes-bvplus-of-bvuminus)))))

;simplify the lhs?
(defthmd bvlt-add-to-both-sides-constant-lemma-helper
  (implies (and (syntaxp (and (quotep k2)
                              (quotep k1)))
                (integerp k2)
                (integerp k1)
                (natp size))
           (equal (bvlt size k2 (bvplus size k1 y))
                  (if (bvlt size k2 k1)
                      (if (bvlt size (bvplus size k1 y) k1) ;looping?
                          (bvlt size (bvplus size k2 (bvuminus size k1)) y)
                        t)
                    (if (bvlt size (bvplus size k1 y) k1) ;looping case?
                        nil
                      (bvlt size (bvplus size k2 (bvuminus size k1)) y)))))
  :hints (("Goal" :use (:instance bvlt-add-to-both-sides (x k2) (size size) (y (bvplus size k1 y)) (z (bvuminus size k1)))
           :in-theory (disable bvlt-add-to-both-sides
                               BVLT-OF-PLUS-ARG2
                               BVLT-OF-BVPLUS-SAME
                               BVLT-OF-PLUS-ARG1))))

(defthmd bvlt-of-bvuminus-arg2
  (implies (and (integerp k1)
                (natp size))
           (equal (bvlt size k1 (bvuminus size y))
                  (if (equal 0 (bvchop size y))
                      nil
                    (if (equal 0 (bvchop size k1))
                        t
                      (bvlt size y (bvuminus size k1))))))
  :hints (("Goal" :in-theory (e/d (bvlt bvuminus bvminus bvchop-of-sum-cases bvplus)
                                  ( bvminus-becomes-bvplus-of-bvuminus
                                               <-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free
                                               bvlt-of-plus-arg2
                                               bvlt-of-plus-arg1)))))

(defthmd bvlt-add-to-both-sides-constant-lemma-helper2
  (implies (and (syntaxp (and (quotep k2)
                              (quotep k1)
                              (quotep size)))
                (integerp k2)
                (integerp k1)
                (natp size)
                )
           (equal (bvlt size k2 (bvplus size k1 y))
                  (if (bvlt size k2 k1)
                      (if (if (equal 0 (bvchop size y))
                              nil
                            (not (if (equal 0 (bvchop size k1))
                                     t
                                   (bvlt size y (bvuminus size k1)))))
                          (bvlt size (bvplus size k2 (bvuminus size k1)) y)
                        t)
                    (if (if (equal 0 (bvchop size y))
                            nil
                          (not (if (equal 0 (bvchop size k1))
                                   t
                                 (bvlt size y (bvuminus size k1)))))
                        nil
                      (bvlt size (bvplus size k2 (bvuminus size k1)) y)))))
  :hints (("Goal" :use (bvlt-of-bvuminus-arg2
                        (:instance bvlt-add-to-both-sides-constant-lemma-helper))
           :in-theory (e/d ( ;bvlt-of-bvuminus-arg2) (
                            bvlt-add-to-both-sides-constant-lemma-helper)))))

;fixme  - simplify this?
(defthm bvlt-add-to-both-sides-constant-lemma
  (implies (and (syntaxp (quotep k2))
                (syntaxp (quotep k1))
                (syntaxp (quotep size))
                (natp size))
           (equal (bvlt size k2 (bvplus size k1 y))
                  (if (bvlt size k2 k1)
                      (if (equal 0 (bvchop size k1))
                          t
                        (if (bvlt size y (bvuminus size k1))
                            t
                          (bvlt size (bvplus size k2 (bvuminus size k1)) y)))
                    (if (equal 0 (bvchop size k1))
                        (bvlt size k2 y)
                      (if (bvlt size y (bvuminus size k1))

                          (bvlt size (bvplus size k2 (bvuminus size k1)) y)
                        nil)))))
  :hints (("Goal" :use (:instance bvlt-add-to-both-sides-constant-lemma-helper2 (k2 (ifix k2))(k1 (ifix k1)))
           :in-theory (e/d (BVLT-OF-0-ARG2)
                           ( bvlt-add-to-both-sides-constant-lemma-helper2)))))

(defthm equal-of-bvplus-move-bvminus
  (IMPLIES (NATP SIZE)
           (equal (EQUAL (BVPLUS SIZE K2 (BVUMINUS SIZE K1))
                         (BVCHOP SIZE Y))
                  (EQUAL (bvchop SIZE K2)
                         (BVPLUS SIZE K1 Y))))
  :hints (("Goal" :in-theory (e/d (bvplus bvmod bvchop-of-sum-cases
                                          bvuminus
                                          bvminus
                                          bvlt)
                                  (bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt-free
                                   <-becomes-bvlt-free-alt
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt)))))

(defthm equal-of-bvplus-move-bvminus-better
  (implies (natp size)
           (equal (equal y (bvplus size k2 (bvuminus size k1)))
                  (and (unsigned-byte-p size y)
                       (equal (bvchop size k2)
                              (bvplus size k1 y)))))
  :hints (("Goal" :use (:instance equal-of-bvplus-move-bvminus)
           :in-theory (disable equal-of-bvplus-move-bvminus))))

(defthm bvlt-add-to-both-sides-constant-lemma-no-split
  (implies (and (syntaxp (and (quotep k2)
                              (quotep k1)
                              (quotep size)))
                (bvlt size y (bvuminus size k1)) ;this case
                (natp size))
           (equal (bvlt size k2 (bvplus size k1 y))
                  (if (bvlt size k2 k1) ;will be computed
                      t
                    (bvlt size (bvplus size k2 (bvuminus size k1)) y))))
  :hints (("Goal" :use (:instance bvlt-add-to-both-sides-constant-lemma)
           :in-theory (disable bvlt-add-to-both-sides-constant-lemma))))

(defthm bvplus-of-bvuminus-32-31-special-case
  (implies (and (not (BVLT '31 x16 x7))
                (unsigned-byte-p 31 x16)
                (unsigned-byte-p 31 x7)
                )
           (equal (BVPLUS '32 x16 (BVUMINUS '31 x7))
                  (if (equal 0 (bvchop 31 x7))
                      (bvchop '32 x16)
                    (bvplus 32 (expt 2 31) (BVPLUS '31 x16 (BVUMINUS '31 x7))))))
  :hints (("Goal" :in-theory (e/d (bvplus bvmod bvchop-of-sum-cases
                                          bvuminus
                                          bvminus
                                          bvlt)
                                  (bvplus-of-plus-arg3
                                   bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt-free
                                   <-becomes-bvlt-free-alt
                                   <-becomes-bvlt
;                                   <-of-bvchop-arg1
                                   <-becomes-bvlt-alt)))))

(defthm bvlt-of-bvplus-same-arg2
  (implies (natp size)
           (equal (bvlt size x (bvplus size x y))
                  (and (bvlt size 0 y)
                       (or (equal 0 (bvchop size x))
                           (bvlt size y (bvuminus size x))))))
  :hints (("Goal" :in-theory (e/d (bvplus bvmod bvchop-of-sum-cases
                                          bvuminus
                                          bvminus
                                          bvlt)
                                  (bvlt-of-plus-arg1
                                   bvlt-of-plus-arg2
                                   bvminus-becomes-bvplus-of-bvuminus
                                   <-becomes-bvlt-free
                                   <-becomes-bvlt-free-alt
                                   <-becomes-bvlt
                                   <-becomes-bvlt-alt)))))

;(defun theory-test () '(BVLT-WHEN-BVCHOP-KNOWN-SUBST-ALT))

(defthm bvlt-of-bvplus-same-arg2-alt
  (implies (natp size)
           (equal (bvlt size x (bvplus size y x))
                  (and (bvlt size 0 y)
                       (or (equal 0 (bvchop size x))
                           (bvlt size y (bvuminus size x))))))
  :hints (("Goal" :use (:instance bvlt-of-bvplus-same-arg2)
           :in-theory (disable bvlt-of-bvplus-same-arg2 ;(theory-test)
                               ))))

(defthm bvlt-of-0-arg2-polarity
  (implies (and (syntaxp (want-to-weaken (bvlt size 0 x)))
                (natp size))
           (equal (bvlt size 0 x)
                  (not (equal 0 (bvchop size x)))))
  :hints (("Goal" :in-theory (e/d (bvlt unsigned-byte-p)
                                  (<-becomes-bvlt
                                   <-becomes-bvlt-alt
                                   <-BECOMES-BVLT-FREE)))))

(defthm logext-of-expt-same
  (implies (posp size)
           (equal (logext size (expt 2 size))
                  0)))

(defthm sbvlt-of-0-arg2-polarity
  (implies (and (syntaxp (want-to-strengthen (sbvlt size x 0)))
                (posp size))
           (equal (sbvlt size x 0)
                  (not (sbvlt size (+ (expt 2 size) -1) x))))
  :hints (("Goal" :use (:instance <-of-bvchop-and-bvchop-same (s1 size)
                                  (s2 (+ -1 size)))
           :in-theory (e/d (;sbvmoddown
                            bvlt sbvlt)
                           (<-of-bvchop-and-bvchop-same)))))

;hmm this cancelation rule is grosser than for < and +
(defthm sbvlt-sbvplus-minus-1-cancel
  (equal (sbvlt 32 4294967295 (bvplus 32 4294967295 x))
         (if (equal (bvchop 32 x) 2147483648)
             t
           (sbvlt 32 0 x)))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases bvchop-when-i-is-not-an-integer sbvlt-rewrite)
                                  (LOGEXT-WHEN-NON-NEGATIVE-BECOMES-BVCHOP logext-identity ;integer-tighten-bound
                                                                           )))))

(defthm sbvlt-sbvplus-minus-1-cancel-alt
  (equal (sbvlt 32 (bvplus 32 4294967295 x) 4294967295)
         (if (equal (bvchop 32 x) 2147483648)
             nil
           (sbvlt 32 x 0)))
  :hints (("Goal" :in-theory (e/d (bvplus bvchop-of-sum-cases bvchop-when-i-is-not-an-integer sbvlt-rewrite)
                                  (logext-identity ;integer-tighten-bound
                                   )))))

;gen
(defthm bvlt-of-bvplus-32-31-trim-alt
  (equal (BVLT 31 (BVPLUS 32 y x) z)
         (BVLT 31 (BVPLUS 31 y x) z))
  :hints (("Goal" :in-theory (e/d (bvlt)
                                  (<-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))

;gen
(defthm bvlt-of-bvplus-32-31-trim
  (equal (BVLT 31 z (BVPLUS 32 y x))
         (BVLT 31 z (BVPLUS 31 y x)))
  :hints (("Goal" :in-theory (e/d (bvlt)
                                  (<-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))

;hope the case split is okay.. (see no-split version below)
(DEFTHM BVPLUS-OF-1-TIGHTEN
  (IMPLIES (AND (UNSIGNED-BYTE-P free X)
                (< free SIZE)
                (natp free)
                (Integerp size)
                )
           (EQUAL (BVPLUS SIZE 1 X)
                  (IF (EQUAL (+ -1 (expt 2 free)) X)
                      (expt 2 free)
                      (BVPLUS free 1 X))))
  :HINTS
  (("Goal"
    :IN-THEORY
    (E/D
     (BVCHOP-OF-SUM-CASES
      BVLT BVPLUS
      BVUMINUS BVMINUS UNSIGNED-BYTE-P-FORCED)
     (<-BECOMES-BVLT-FREE <-BECOMES-BVLT <-BECOMES-BVLT-ALT


                          BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS

                          BVLT-OF-PLUS-ARG1 BVLT-OF-PLUS-ARG2)))))

(defthm bvplus-of-1-tighten-no-split
  (implies (and (unsigned-byte-p free x)
                (not (equal (+ -1 (expt 2 free)) x))
                (< free size)
                (natp free)
                (integerp size))
           (equal (bvplus size 1 x)
                  (bvplus free 1 x)))
  :hints (("Goal" :use (:instance bvplus-of-1-tighten)
           :in-theory (disable bvplus-of-1-tighten))))

(defthm bvlt-when-bvlt-false2
  (implies (and (syntaxp (quotep k))
                (BVLT size free x)
                (syntaxp (quotep free))
                (syntaxp (quotep size))
                (bvle size (+ -1 k) free) ;gets evaluated
                (integerp k)
                (natp size)
                )
           (not (BVLT size x k)))
  :hints (("Goal" :in-theory (e/d (bvlt ;unsigned-byte-p
                                   bvchop-of-sum-cases
                                   bvplus
                                   )
                                  (<-becomes-bvlt <-becomes-bvlt-alt
                                                  bvlt-of-plus-arg1
                                                  bvlt-of-plus-arg2
                                                  <-of-bvplus-becomes-bvlt-arg1
                                                  <-of-bvplus-becomes-bvlt-arg2)))))

(defthm bvlt-when-not-bvlt-one-more
  (implies (and (syntaxp (quotep const)) ;new
                (not (bvlt size free x))
                (syntaxp (quotep free)) ;new
                (equal free (+ 1 const))
                (unsigned-byte-p size free)
                (unsigned-byte-p size const)
                (integerp size))
           (equal (bvlt size const x)
                  (equal free (bvchop size x))))
  :hints (("Goal" :in-theory (e/d (bvlt) (<-becomes-bvlt <-becomes-bvlt-alt
                                                         <-of-bvplus-becomes-bvlt-arg1
                                                         <-becomes-bvlt-free
                                                         <-of-bvplus-becomes-bvlt-arg2
                                                         BVLT-OF-PLUS-ARG1
                                                         )))))
;use polarities?
(defthm bvlt-unique
  (implies (and (bvlt size x free)
                (syntaxp (quotep free))
                (equal free (+ 2 k))
                (unsigned-byte-p size k)
                (natp size)
                )
           (equal (bvlt size k x)
                  (equal (+ 1 k) (bvchop size x))))
  :hints (("Goal" :in-theory (enable bvlt bvchop-of-sum-cases))))

;simplify rhs?
(defthm bvlt-of-bvplus-and-bvplus-cancel-1-1
  (implies (natp size)
           (equal (bvlt size (bvplus size x y) (bvplus size x z))
                  (if (and (not (equal 0 (bvchop size y)))
                           (bvle size (bvuminus size y) x))
                      (if (and (not (equal 0 (bvchop size z)))
                               (bvle size (bvuminus size z) x))
                          (bvlt size y z)
                        t)
                    (if (and (not (equal 0 (bvchop size z)))
                             (bvle size (bvuminus size z) x))
                        nil
                      (bvlt size y z)))))
  :hints (("Goal" :use (:instance bvlt-of-bvplus-and-bvplus-cancel)
           :in-theory (disable bvlt-of-bvplus-and-bvplus-cancel))))

;which form do we prefer?
;this seems like a bad rule?..
(defthm bvlt-of-bvuminus
  (implies (and (unsigned-byte-p 31 x)
                (unsigned-byte-p 31 y))
           (equal (bvlt '31 x (bvuminus '31 y))
                  (if (equal 0 y)
                      nil
                    (bvlt 32 (bvplus 32 x y) (expt 2 31)))))
  :hints (("Goal"
           :expand (bvlt 31 x y)
           :in-theory (e/d (bvlt
                            bvplus
                            getbit-when-val-is-not-an-integer
                            bvuminus bvminus
                            bvchop-of-sum-cases sbvlt
                            bvchop-when-i-is-not-an-integer
                            bvchop-when-top-bit-1)
                           (getbit-of-plus
                            ;<-of-bvchop-arg1
                            <-becomes-bvlt-free
                            <-becomes-bvlt-free-alt <-becomes-bvlt

                            bvplus-of-plus-arg3
                            ;;fixme
                            bvminus-becomes-bvplus-of-bvuminus
                            <-becomes-bvlt
                            <-becomes-bvlt-alt
                            <-of-bvplus-becomes-bvlt-arg1
                            <-of-bvplus-becomes-bvlt-arg2

                            bvlt-of-plus-arg1
                            bvlt-of-plus-arg2)))))

(defthm bvplus-of-minus1-tighten-32
  (implies (and (unsigned-byte-p free x)
                (< free 32)
                (not (equal x 0)) ;limit?
                )
           (equal (BVPLUS '32 4294967295 x)
                  (bvplus free (+ -1 (expt 2 free)) x)))
  :hints (("Goal" :in-theory (enable bvplus bvchop-of-sum-cases))))

(defthm bvplus-of-bvminus-known
  (implies (and (EQUAL x (BVPLUS 32 free y))
                (syntaxp (quotep free))
                (unsigned-byte-p 32 x)
                )
           (equal (BVPLUS 32 x (bvuminus 32 y))
                  (bvchop 32 free))) ;gets computed
  :hints (("Goal" :in-theory (e/d (bvplus-drop) (BVPLUS-OF-1-TIGHTEN)))))

;move
(defthm equal-of-0-and-bvsx
  (implies (and (natp size)
                (posp old-size)
                (<= old-size size))
           (equal (equal 0 (bvsx size old-size x))
                  (equal 0 (bvchop old-size x))))
  :hints (("Goal" :in-theory (enable bvsx getbit-when-equal-of-constant-and-bvchop))))

(defthm rewrite-bv-equality-when-sizes-dont-match-1
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'x-size x) (x-size))
                (bind-free (bind-var-to-unsigned-term-size-if-trimmable 'y-size y) (y-size))
                (syntaxp (and (not (quotep x))
                              (not (quotep y))))
                (< x-size y-size)
                (force (natp x-size))
                (force (natp y-size))
                (force (unsigned-byte-p-forced x-size x))
                (force (unsigned-byte-p-forced y-size y))
                )
           (equal (equal x y)
                  (and (equal x (bvchop x-size y))
                       (equal (slice (+ -1 y-size) x-size y)
                              0))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced)
           :use (:instance rewrite-bv-equality-when-sizes-dont-match-core))))

(defthm rewrite-bv-equality-when-sizes-dont-match-2
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'x-size x) (x-size))
                (bind-free (bind-var-to-unsigned-term-size-if-trimmable 'y-size y) (y-size))
                (syntaxp (and (not (quotep x))
                              (not (quotep y))))
                (< x-size y-size)
                (force (natp x-size))
                (force (natp y-size))
                (force (unsigned-byte-p-forced x-size x))
                (force (unsigned-byte-p-forced y-size y))
                )
           (equal (equal y x)
                  (and (equal x (bvchop x-size y))
                       (equal (slice (+ -1 y-size) x-size y)
                              0))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced)
           :use (:instance rewrite-bv-equality-when-sizes-dont-match-core))))

;seems powerful.  could be dangerous?
(defthm bvchop-subst-when-equal-of-bvchops
  (implies (and (equal (bvchop 32 x) (bvchop 32 free))
                (syntaxp (smaller-termp free x)))
           (equal (bvchop 31 x)
                  (bvchop 31 free))))

(defthm <-of-bvminus-and-bvminus
  (implies (and (sbvle 32 y x)
                (sbvle 32 z x)
                (sbvle 32 0 z) ;gen
                )
           (equal (< (BVMINUS 32 x y) (BVMINUS 32 x z))
                  (sbvlt 32 z y)))
  :hints (("Goal" :in-theory (enable BVMINUS SBVLT-rewrite
                                     bvlt
                                     BVCHOP-OF-SUM-CASES
                                     getbit-when-bvlt-of-small-helper))))

 ;todo gen
(defthm <-of-bvchop-and-bvchop-31-32-same
 (EQUAL (< (BVCHOP 31 X) (BVCHOP 32 X))
        (equal 1 (getbit 31 x)))
 :hints (("Goal" :use (:instance <-OF-BVCHOP-AND-BVCHOP-SAME (s2 32) (s1 31))
          :in-theory (disable <-OF-BVCHOP-AND-BVCHOP-SAME
                              REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-1))))


(defthmd bvchop-when-top-bit-0
  (implies (and (equal 0 (getbit (+ -1 size) x))
                (posp size))
           (equal (bvchop size x)
                  (bvchop (+ -1 size) x))))

(defthmd bvchop-when-top-bit-0-widen
  (implies (and (equal 0 (getbit (+ -1 size) x))
                (posp size))
           (equal (bvchop size x)
                  (bvchop (+ -1 size) x))))

;subtracting a value that is one larger than x gives a smaller result than subtracting x
(defthm <-of-bvminus-of-bvplus-of-1-and-bvminus
  (implies (sbvlt 32 x y)
           (< (bvminus 32 y (bvplus 32 1 x))
              (bvminus 32 y x)))
  :hints (("Goal"
           :cases ((equal 0 (getbit 31 y)))
           :in-theory (e/d (bvminus sbvlt-rewrite
                                    bvlt bvplus ; bvchop
                                    BVCHOP-WHEN-TOP-BIT-1
                                    bvCHOP-WHEN-TOP-BIT-0
                                    bvchop-of-sum-cases) (REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-1 ;looped
                                    )))))

(defthm equal-of-bvchop-32-and-bvchop-31
  (equal (EQUAL (BVCHOP 32 X) (BVCHOP 31 Y))
         (and (equal 0 (getbit 31 x))
              (EQUAL (BVCHOP 31 X) (BVCHOP 31 Y))))
  :hints (("Goal" :in-theory (enable REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-2))))

(defthm bvif-of-equal-1-0
  (implies (and (unsigned-byte-p 1 x)
                (unsigned-byte-p 1 y))
           (equal (bvif 1 (equal x y) 1 0)
                  (bitxor 1 (bitxor x y)))))

(defthm bvif-of-equal-0-1
  (implies (and (unsigned-byte-p 1 x)
                (unsigned-byte-p 1 y))
           (equal (bvif 1 (equal x y) 0 1)
                  (bitxor x y)))
  :hints (("Goal" :cases ((equal 0 x)))))

(defthm equal-of-bvchops-when-equal-of-getbits
  (implies (and (syntaxp (want-to-strengthen (equal (bvchop 31 x) (bvchop 31 y))))
                (equal (getbit 31 x) (getbit 31 y)))
           (equal (equal (bvchop 31 x) (bvchop 31 y))
                  (equal (bvchop 32 x) (bvchop 32 y))))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0))))

(defthm equal-of-bvchop-when-lower-bits-equal
  (implies (and (syntaxp (want-to-weaken (equal k (bvchop 32 n))))
                (equal (bvchop 31 n) (bvchop 31 k)))
           (equal (equal k (bvchop 32 n))
                  (and (unsigned-byte-p 32 k)
                       (equal (getbit 31 k) (getbit 31 n)))))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0)))
  :hints (("Goal" :in-theory (disable BVCAT-OF-GETBIT-AND-X-ADJACENT BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE))))

(defthm not-<-when-sbvlt
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p 31 k) ;gen?
;                (unsigned-byte-p 32 k) (not (equal k (expt 2 31)))
                (sbvlt 32 k2 x) ;k2 is a free var
                (syntaxp (quotep k2))
                (sbvle 32 (+ -1 k) k2)
                (natp x))
           (not (< x k)))
  :hints (("Goal" :in-theory (enable sbvlt-rewrite bvlt bvchop-of-sum-cases))))

;gen?
(defthm not-<-when-sbvlt-alt
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p 31 k)
                (sbvlt 32 x k2) ;k2 is a free var
                (syntaxp (quotep k2))
                (sbvle 32 k2 (+ 1 k)) ;gets computed
                (unsigned-byte-p 32 x)
                (sbvle 32 0 x))
           (not (< k x)))
  :hints (("Goal" :in-theory (enable sbvlt-rewrite bvlt bvchop-of-sum-cases))))

;compare to SBVLT-BOUND-LEMMA
(defthm sbvlt-when-<-negative-case
  (implies (and (< k n) ;k is a free var
                (syntaxp (quotep k))
                (<= (+ -1 (expt 2 31)) k)
                (unsigned-byte-p 32 n))
           (sbvlt 32 n 0))
  :hints (("Goal" :in-theory (enable sbvlt-rewrite))))


;When we know n>=k, weaken n>k to n<>k
(defthm sbvlt-weaken-to-not-equal-when-<=
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p 31 k)
                (syntaxp (want-to-weaken '(sbvlt 32 k n)))
                (<= k2 n) ;k2 is a free var but below we require k2=k
                (syntaxp (quotep k2))
                (equal k k2)
                (unsigned-byte-p 31 n)
                )
           (equal (sbvlt 32 k n)
                  (not (equal n k))))
  :hints (("Goal" :in-theory (enable sbvlt-rewrite bvlt))))

;add more variants...
(defthm bvminus-of-bvplus-and-bvplus-same
  (equal (bvminus size (bvplus size z x) (bvplus size z y))
         (bvminus size x y))
  :hints (("Goal" :in-theory (enable bvminus bvplus bvchop-of-sum-cases))))

;helpful for termination (hence the < rather than sbvlt)
(defthm <-of-bvminus-and-bvminus-of-bvplus-of-1
  (implies (and (equal size 32) ;gen!
                (sbvle size x y)
                (not (sbvlt size x 0))
                (unsigned-byte-p size y) ;drop?
                (posp size)
                )
           (< (bvminus size y x) (bvminus size (bvplus size 1 y) x)))
  :hints (("Goal" :in-theory (enable bvminus bvplus bvchop-of-sum-cases sbvlt))))

;can help with termination
(defthm <-of-bvplus-of-1-same
  (implies (unsigned-byte-p 32 x)
           (equal (< x (bvplus 32 1 x))
                  (not (equal (bvchop 32 x) 4294967295))))
  :hints (("Goal" :in-theory (enable bvplus bvchop-of-sum-cases))))

(defthm <-of-bvchop-and-bvplus-of-1-same
  (equal (< (bvchop 32 x) (bvplus 32 1 x))
         (not (equal (bvchop 32 x) 4294967295)))
  :hints (("Goal" :in-theory (enable bvplus bvchop-of-sum-cases))))

;helpful for termination proofs
(defthm <-of-bvminus-and-bvminus-same
  (implies (and (bvle 32 y x)
                (bvle 32 z x))
           (equal (< (bvminus 32 x y)
                     (bvminus 32 x z))
                  (< (bvchop 32 z)
                     (bvchop 32 y))))
  :hints (("Goal" :in-theory (enable bvminus bvplus bvchop-of-sum-cases bvchop-of-minus bvlt))))

;; Lemmas to convert arithmetic operations to bit-vector operations:

(defthmd <-to-sbvlt-32
  (implies (and (signed-byte-p 32 x)
                (signed-byte-p 32 y))
           (equal (< x y)
                  (sbvlt 32 (bvchop 32 x) (bvchop 32 y))))
  :hints (("Goal" :in-theory (enable sbvlt))))

(defthmd +-to-bvplus-32
  (implies (and (signed-byte-p 32 x)
                (signed-byte-p 32 y)
                (< (+ x y) (expt 2 31))
                (<= (- (expt 2 31)) (+ x y))
                )
           (equal (+ x y)
                  (logext 32 (bvplus 32 (bvchop 32 x) (bvchop 32 y)))))
  :hints (("Goal" :in-theory (enable sbvlt signed-byte-p bvplus))))

;move
(defthm bit-to-bool-of-bool-to-bit
  (implies (booleanp x)
           (equal (bit-to-bool (bool-to-bit x))
                  x)))

;move
(defthm unsigned-byte-p-1-when-not-0
  (implies (and (not (equal 0 x))
                (syntaxp (want-to-strengthen (unsigned-byte-p 1 x))))
           (equal (unsigned-byte-p 1 x)
                  (equal 1 x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-1-when-not-1
  (implies (and (not (equal 1 x))
                (syntaxp (want-to-strengthen (unsigned-byte-p 1 x))))
           (equal (unsigned-byte-p 1 x)
                  (equal 0 x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

;; TODO: Prove these:

;; (defthm sbvdiv-and-sbvrem-relationship-helper
;;   (implies (and (posp size)
;;                 (unsigned-byte-p size x)
;;                 (unsigned-byte-p size y)
;;                 )
;;            (equal (bvplus size (bvmult size y (sbvdiv size x y)) (sbvrem size x y))
;;                   (bvchop size x)))
;;   :hints (("Goal" :in-theory (enable rem sbvdiv sbvrem bvmult bvplus logext-cases))))

;; (defthm sbvdiv-and-sbvrem-relationship
;;   (implies (unsigned-byte-p size x)
;;            (equal (bvplus size (bvmult size y (sbvdiv size x y)) (sbvrem size x y))
;;                   x))
;;   :hints (("Goal" :use (:instance sbvdiv-and-sbvrem-relationship-helper (y (bvchop size y))))))

;; (defthm sbvdiv-and-sbvrem-relationship-gen
;;   (equal (bvplus size (bvmult size y (sbvdiv size x y)) (sbvrem size x y))
;;          (bvchop size x))
;;   :hints (("Goal" :use (:instance sbvdiv-and-sbvrem-relationship-helper (y (bvchop size y))))))

(defthm sbvlt-of-0-when-getbit-1
  (implies (and (equal 1 (getbit size-1 x)) ;size-1 is a free var
                (equal size-1 (- size 1))
                (posp size))
           (sbvlt size x 0))
  :hints (("Goal" :in-theory (enable sbvlt-rewrite))))

(defthm bvlt-when-sbvlt-false
  (implies (and (syntaxp (and (quotep size)
                              (quotep k)))
                (sbvlt size2 x free)
                (syntaxp (quotep free))
                (syntaxp (quotep size2))
                (unsigned-byte-p size free) ;gets computed - drop?
                (equal size2 (+ 1 size)) ;gets computed
                (bvle size2 free (+ 1 k)) ;gets computed
                (unsigned-byte-p size k) ;gets computed - drop?
                (integerp k)
                (natp size)
                (unsigned-byte-p size x) ;expensive?
                )
           (not (bvlt size k x)))
  :hints (("Goal" ;:cases ((unsigned-byte-p size (bvchop size2 x)))
           :in-theory (enable sbvlt-rewrite bvlt bvchop-of-sum-cases))))

;expensive?
;may want to disable for code proofs
(defthm signed-byte-p-when-top-bit-0
  (implies (and (equal 0 (getbit (+ -1 n) k))
                (natp n))
           (equal (signed-byte-p n k)
                  (unsigned-byte-p (+ -1 n) k)))
  :hints (("Goal" :in-theory (e/d (signed-byte-p getbit slice bvchop-of-logtail logtail bvchop UNSIGNED-BYTE-P)
                                  (MOD-OF-EXPT-OF-2
                                   slice-becomes-getbit bvchop-1-becomes-getbit
                                   logtail-becomes-slice-bind-free
                                   bvchop-of-logtail-becomes-slice)))))

(defthm signed-byte-p-when-top-bit-1
  (implies (and (signed-byte-p n k)
                (equal 1 (getbit (+ -1 n) k)))
           (equal k
                  (- (bvchop (+ -1 n) k)
                     (expt 2 (+ -1 n))
                     )))
  :rule-classes nil
  :hints (("Goal" :cases ((< k 0)(< 0 k))
           :in-theory (e/d (signed-byte-p getbit slice bvchop-of-logtail logtail bvchop UNSIGNED-BYTE-P)
                                  (MOD-EXPT-SPLIT
                                   MOD-OF-EXPT-OF-2
                                   slice-becomes-getbit bvchop-1-becomes-getbit
                                   logtail-becomes-slice-bind-free
                                   bvchop-of-logtail-becomes-slice)))))

(defthm slice-of-bvsx
  (implies (and (< low old-size) ;this case (there must be at least one bit to sign-extend?)
                (< high new-size)
                (<= old-size new-size)
                (<= low high)
                (natp high)
                (natp low)
                (posp old-size)
                (natp new-size))
           (equal (slice high low (bvsx new-size old-size x))
                  (bvsx (+ 1 high (- low)) (- old-size low) (slice high low x))))
  :hints (("Goal" :in-theory (enable bvsx BVCAT-OF-0 natp))))

(defthm bvsx-too-high
  (implies (and (unsigned-byte-p (+ -1 old-size) x)
                (<= old-size new-size))
           (equal (bvsx new-size old-size x)
                  x))
  :hints (("Goal" :in-theory (e/d (natp bvsx getbit-too-high)
                                  (collect-constants-times-equal)))))

(defthm bvsx-too-high-syntactic
  (implies (and (bind-free (bind-var-to-unsigned-term-size 'xsize x) (xsize))
                (< xsize old-size)
                (natp old-size)
                (<= old-size new-size)
                (unsigned-byte-p-forced xsize x))
           (equal (bvsx new-size old-size x)
                  x))
  :hints (("Goal" :use (:instance bvsx-too-high)
           :in-theory (e/d (unsigned-byte-p-forced)
                           (bvsx-too-high)))))

(defthm bvsx-of-bvsx
  (implies (and (<= old-size new-size)
                (<= new-size big-size)
                (posp old-size) ;must have at least 1 bit to sign-extend..
                (integerp new-size)
                (integerp big-size))
           (equal (bvsx big-size new-size (bvsx new-size old-size x))
                  (bvsx big-size old-size x)))
  :hints (("Goal" :in-theory (enable bvsx))))

(defthm slice-of-bvsx-high
  (implies (and (<= old-size low) ;this case
                (< high new-size)
                (<= old-size new-size)
                (<= low high)
                (natp high)
                (natp low)
                (posp old-size)
                (natp new-size))
           (equal (slice high low (bvsx new-size old-size x))
                  (repeatbit (+ 1 high (- low))
                             (getbit (+ -1 old-size) x))))
  :hints (("Goal" :in-theory (enable bvsx bvcat-of-0 natp))))

(defthm unsigned-byte-p-of-repeatbit-of-1-arg2
  (implies (natp n)
           (equal (unsigned-byte-p size (repeatbit n 1))
                  (and (<= n size)
                       (natp size)))))

(defthm unsigned-byte-p-of-bvsx-alt
  (implies (and (< size new-size) ;this case
                (<= old-size size) ;this case
                (natp size)
                (natp new-size)
                (posp old-size)
                (<= old-size new-size))
           (equal (unsigned-byte-p size (bvsx new-size old-size x))
                  (equal 0 (getbit (+ -1 old-size) x))))
  :hints (("Goal" :in-theory (e/d (bvsx) (REPEATBIT-OF-1-ARG2)))))

(defthm bvchop-subst-when-equal-of-bvchops-gen
  (implies (and (equal (bvchop size2 x) (bvchop size2 free))
                (syntaxp (smaller-termp free x))
                (<= size size2)
                (natp size)
                (integerp size2)
                )
           (equal (bvchop size x)
                  (bvchop size free))))

;helpful for termination
(defthm <-of-bvminus-of-bvplus-of-1-and-bvminus-same
  (implies (and (bvlt size y x)
                (posp size))
           (< (bvminus size x (bvplus size 1 y))
              (bvminus size x y)))
  :hints (("Goal" :in-theory (e/d (sbvlt-rewrite bvplus bvuminus bvminus getbit-of-plus bvlt bvchop-of-sum-cases)
                                  (bvminus-becomes-bvplus-of-bvuminus)))))

;helpful for termination
;; in this version, the size is one less. todo: do we need both?
(defthm <-of-bvminus-of-bvplus-of-1-and-bvminus-same-alt
  (implies (and (bvlt (+ -1 size) y x)
                (posp size))
           (< (bvminus size x (bvplus size 1 y))
              (bvminus size x y)))
  :hints (("Goal" :in-theory (e/d (sbvlt-rewrite bvplus bvuminus bvminus getbit-of-plus bvlt bvchop-of-sum-cases)
                                  (bvminus-becomes-bvplus-of-bvuminus)))))

(defthm bvlt-when-bvlt-smaller
  (implies (and (bvlt freesize x y)
                (<= freesize size)
                (unsigned-byte-p freesize x)
                ;; (unsigned-byte-p freesize y)
                (integerp size))
           (bvlt size x y))
  :hints (("Goal" :in-theory (enable bvlt))))

(defthm bvand-of-repeatbit-of-1
  (equal (bvand size x (repeatbit size 1))
         (bvchop size x))
  :hints (("Goal" :in-theory (enable repeatbit))))

;todo: compare to the other variants of this rule
(defthm bvchop-of-bvsx3
  (implies (and (<= n old-size)
                (< 0 old-size)
                (<= old-size new-size)
                (natp n)
                (natp new-size)
                (natp old-size))
           (equal (bvchop n (bvsx new-size old-size val))
                  (bvchop n val)))
  :hints (("Goal" :cases ((equal n old-size))
           :in-theory (enable bvsx))))

(defthmd equal-of-logext
  (implies (and ;(integerp x)
                (integerp y)
                (posp n)
                )
           (equal (equal x (logext n y))
                  (and (equal (bvchop n x)
                              (bvchop n y))
                       (signed-byte-p n x)
                       (integerp x)))))

(defthmd bvchop-of-sum-of-logext-becomes-bvplus
  (implies (and (<= size size2)
                (natp size)
                (natp size2)
                (integerp x))
           (equal (bvchop size (+ x (logext size2 y)))
                  (bvplus size x y)))
  :hints (("Goal" :in-theory (enable bvplus) :cases ((integerp y)))))

(defthm slice-of-logext-middle
  (implies (and (< low n)
                (<= n high)
                (posp n)
                (natp low)
                (integerp high))
           (equal (slice high low (logext n x))
                  (bvsx (+ 1 high (- low))
                        (- n low)
                        (slice (+ -1 n) low x))))
  :hints (("Goal" :in-theory (e/d (slice logext repeatbit bvsx LOGTAIL-OF-BVCHOP)
                                  (BVCHOP-OF-LOGTAIL-BECOMES-SLICE BVCHOP-OF-LOGTAIL)))))

(defthm slice-of-logext-gen
  (implies (and (posp n)
                (natp low)
                (integerp high))
           (equal (slice high low (logext n x))
                  (if (< high n)
                      (slice high low x)
                    (if (< low n)
                        (bvsx (+ 1 high (- low))
                              (- n low)
                              (slice (+ -1 n) low x))
                      (bvsx (+ 1 high (- low))
                            1
                            (getbit (+ -1 n) x)))))))


;gen
(defthm <-if-bvchop-and-+of-bvchop-cancel
 (equal (< (bvchop 32 x) (+ y (bvchop 31 x)))
        (< (* (expt 2 31) (getbit 31 x)) y))
 :hints (("Goal" :use (:instance
                       acl2::split-bv
                       (n 32)
                       (m 31)
                       (y (bvchop 32 x)))
          :in-theory (e/d (bvcat logapp) (acl2::logapp-of-bvchop-same)))))


;gen
(defthm <-of-bvplus-of-minus1-and-bvchop-same
  (equal (< (bvplus 32 4294967295 x) (bvchop 31 x))
         (and (equal (getbit 31 x) 0)
              (not (equal 0 (bvchop 31 x)))))
  :hints (("Goal" :in-theory (e/d (bvplus acl2::bvchop-of-sum-cases)
                                  (;acl2::bvplus-recollapse
                                   )))))

(local
 (defthm getbit-of-leftrotate-high
   (implies (and (<= amt n) ; this case
                 (< n width)
                 (< amt width)
                 (natp n)
                 (natp amt)
                 (natp width))
            (equal (getbit n (leftrotate width amt x))
                   (getbit (- n amt) x)))
   :hints (("Goal" :in-theory (e/d (getbit leftrotate) (bvchop-1-becomes-getbit
                                                        slice-becomes-getbit))))))

(local
 (defthm getbit-of-leftrotate-low
   (implies (and (< n amt) ; this case
                 (< n width)
                 (< amt width)
                 (natp n)
                 (natp amt)
                 (natp width))
            (equal (getbit n (leftrotate width amt x))
                   (getbit (+ width (- amt) n) x)))
   :hints (("Goal" :in-theory (e/d (getbit leftrotate) (bvchop-1-becomes-getbit
                                                        slice-becomes-getbit))))))

(defthm getbit-of-leftrotate
  (implies (and ;(< amt width) ;gen?
            (natp n)
            (natp amt)
            (natp width))
           (equal (getbit n (leftrotate width amt x))
                  (if (< n width)
                      (if (< n (mod amt width)) ; this case
                          (getbit (+ width (- (mod amt width)) n) x)
                        (getbit (- n (mod amt width)) x))
                    0)))
  :hints (("Goal" :in-theory (e/d (getbit leftrotate) (bvchop-1-becomes-getbit
                                                       slice-becomes-getbit)))))

;; no mod in rhs
(defthmd getbit-of-leftrotate-simple
  (implies (and (< amt width) ; avoids mod in rhs
                (natp n)
                (natp amt)
                (natp width))
           (equal (getbit n (leftrotate width amt x))
                  (if (< n width)
                      (if (< n amt) ; this case
                          (getbit (+ width (- amt) n) x)
                        (getbit (- n amt) x))
                    0)))
  :hints (("Goal" :in-theory (e/d (getbit leftrotate) (bvchop-1-becomes-getbit
                                                       slice-becomes-getbit)))))


;todo: add full trim support for rotate ops
(defthmd trim-of-1-and-leftrotate
  (implies (and (< amt width) ; avoids mod in rhs
                (natp amt)
                (natp width))
           (equal (trim 1 (leftrotate width amt x))
                  (if (< 0 width)
                      (if (< 0 amt) ; this case
                          (getbit (+ width (- amt)) x)
                        (getbit amt x))
                    0)))
  :hints (("Goal" :in-theory (e/d (trim leftrotate) ()))))

(defthm bitand-of-leftrotate-arg1-trim
  (equal (bitand (leftrotate width amt x) y)
         (bitand (trim 1 (leftrotate width amt x)) y))
  :hints (("Goal" :in-theory (enable trim))))

(defthm bitand-of-leftrotate-arg2-trim
  (equal (bitand x (leftrotate width amt y))
         (bitand x (trim 1 (leftrotate width amt y))))
  :hints (("Goal" :in-theory (enable trim))))

(defthm bitxor-of-leftrotate-arg1-trim
  (equal (bitxor (leftrotate width amt x) y)
         (bitxor (trim 1 (leftrotate width amt x)) y))
  :hints (("Goal" :in-theory (enable trim))))

(defthm bitxor-of-leftrotate-arg2-trim
  (equal (bitxor x (leftrotate width amt y))
         (bitxor x (trim 1 (leftrotate width amt y))))
  :hints (("Goal" :in-theory (enable trim))))

;gen the 32s!
(defthm equal-of-leftrotate-and-leftrotate
  (implies (and (equal 32 size) ;gen!
                (natp size)
                ;(<= size 32)
                )
           (equal (equal (leftrotate size n x) (leftrotate size n y))
                  (equal (bvchop size x) (bvchop size y))))
  :hints (("Goal" :in-theory (enable leftrotate))))

;move
(defthm equal-of-leftrotate32-and-leftrotate32
  (equal (equal (leftrotate32 n x) (leftrotate32 n y))
         (equal (bvchop 32 x) (bvchop 32 y)))
  :hints (("Goal" :in-theory (enable leftrotate32))))

(defthm bvchop-subst-constant-from-logext
  (implies (and (equal (logext free x) k)
                (syntaxp (quotep k))
                (<= size free)
                (posp size)
                (integerp free)
                )
           (equal (bvchop size x)
                  (bvchop size k)))
  :hints (("Goal"
           :cases ((equal size (+ -1 free))
                   (< size (+ -1 free)))
           :in-theory (e/d (logext logtail-of-bvchop)
                           ( slice  BVCHOP-OF-LOGTAIL
                                    )))))

(defthm not-equal-max-int-when-<=
  (IMPLIES (AND (NOT (SBVLT 32 free x))
                (NOT (EQUAL (BVCHOP 32 free)
                            2147483647)))
           (not (EQUAL 2147483647 (BVCHOP 32 x))))
  :hints (("Goal" :in-theory (enable SBVLT))))

;move
(defthm svblt-trichotomy
  (or (sbvlt size x y)
      (sbvlt size y x)
      (equal (bvchop size x) (bvchop size y)))
  :rule-classes nil
  :hints (("Goal" :cases ((posp size))
           :in-theory (enable sbvlt
                              EQUAL-OF-LOGEXT-AND-LOGEXT))))

;move
;; This idiom can arise from the JVM LCMP instruction
(defthm myif-of-sbvlt-of-0-and-not-sbvlt-of-0
  (implies (posp size)
           (equal (myif (sbvlt size 0 x)
                        nil
                        (not (sbvlt size x 0)))
                  (equal 0 (bvchop size x))))
  :hints (("Goal"
           :use (:instance svblt-trichotomy (y 0))
           :in-theory (enable myif))))

(defthm booland-of-not-sbvlt-and-not-equal
  (implies (and (unsigned-byte-p size x)
                (unsigned-byte-p size k))
           (equal (booland (not (sbvlt size k x)) (not (equal k x)))
                  (sbvlt size x k)))
  :hints (("Goal" :use (:instance svblt-trichotomy (y k)))))

;disable?
(defthm unsigned-byte-p-tighten-when-slice-is-0
  (implies (and (equal 0 (slice k free x))
                (equal k (+ -1 size))
                (posp size)
                (< free size)
                (natp free))
           (equal (unsigned-byte-p size x)
                  (unsigned-byte-p free x)))
  :hints (("Goal"
           :use (:instance split-with-bvcat (hs (- size free)) (ls free))
           :in-theory (e/d () (equal-of-bvchop-and-bvchop-same)))))

(defthm unsigned-byte-p-of-slice-lemma
  (implies (and (unsigned-byte-p (+ n low) x)
                (natp n)
                (natp low)
                (natp high)
                )
           (equal (unsigned-byte-p n (slice high low x))
                  t))
  :hints (("Goal" :in-theory (e/d (slice) (anti-slice)))))

;gen to deal with more that just 1 top bit
(defthm unsigned-byte-p-of-slice-one-more
  (implies (and (equal (- high low) size)
                (natp high)
                (natp low)
                (<= low high))
           (equal (unsigned-byte-p size (slice high low x))
                  (equal 0 (getbit high x))))
  :hints (("Goal" :use (:instance split-bv (y (slice high low x)) (n (+ 1 (- low) high)) (m (- high low)))
           :in-theory (disable BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE))))

;; if the top bit is clear, there's no way dividing can make it set
(defthmd getbit-of-bvdiv-when-equal-0-of-getbit
  (implies (and (equal size-1 (+ -1 size))
                (equal 0 (getbit size-1 x))
                (integerp x)
                (integerp y)
                (natp size))
           (equal (getbit size-1 (bvdiv size x y))
                  0))
  :hints (("Goal" :cases ((equal size 0))
           :in-theory (enable bvdiv))))

(defthm getbit-of-bvdiv-when-equal-0-of-getbit-constant-version
  (implies (and (syntaxp (quotep size)) ;this version
                (equal size-1 (+ -1 size))
                (equal 0 (getbit size-1 x))
                (integerp x)
                (integerp y)
                (natp size))
           (equal (getbit size-1 (bvdiv size x y))
                  0))
  :hints (("Goal" :by getbit-of-bvdiv-when-equal-0-of-getbit)))

;; x-1 < y becomes x <= y
(defthmd bvlt-of-bvplus-of-minus1
  (implies (natp size)
           (equal (bvlt size (bvplus size -1 x) y)
                  (if (equal (bvchop size x) 0)
                      nil
                    (bvle size x y))))
  :hints (("Goal" :in-theory (enable bvlt bvplus
                                     bvchop-of-sum-cases))))

(defthm bvlt-of-bvplus-of-minus1-constant-version
  (implies (and (syntaxp (quotep k))
                (equal k (+ -1 (expt 2 size)))
                (natp size))
           (equal (bvlt size (bvplus size k x) y)
                  (if (equal (bvchop size x) 0)
                      nil
                    (bvle size x y))))
  :hints (("Goal" :in-theory (enable bvlt bvplus
                                     bvchop-of-sum-cases))))

;; x < 1+y becomes x <= y
(defthm bvlt-of-bvplus-of-1-arg2
  (implies (natp size)
           (equal (bvlt size x (bvplus size 1 y))
                  (if (equal (bvchop size y)  (+ -1 (expt 2 size)))
                      nil
                    (bvle size x y))))
  :hints (("Goal" :in-theory (enable bvlt bvplus
                                     bvchop-of-sum-cases))))

;; (defthm getbit-of-bvplus-of--1-top
;;   (implies (integerp x)
;;            (equal (getbit 31 (bvplus 32 (+ -1 (expt 2 31)) x))
;;                   (if (equal (bvchop 32 x) (expt 2 31))
;;                       0
;;                     (if (equal (bvchop 32 x) (expt 2 31))
;;                         1
;;                       (getbit 31 x)))))
;;   :hints (("Goal" :in-theory (e/d (bvlt bvplus
;;                                         bvchop-of-sum-cases
;;                                         getbit
;;                                         slice)
;;                                   (slice-becomes-getbit
;;                                    bvchop-1-becomes-getbit)))))

;; since x>=y, x is usually not less than y+1
(defthmd bvlt-of-bvplus-of-minus1-arg2-when-not-bvlt
  (implies (and (syntaxp (quotep k))
                (equal k (+ -1 (expt 2 size)))
                (not (bvlt size x y))
                (natp size))
           (equal (bvlt size x (bvplus size k y))
                  (if (equal 0 (bvchop size y))
                      (bvlt size x k) ;odd case
                    nil)))
  :hints (("Goal" :in-theory (enable bvlt bvplus
                                     bvchop-of-sum-cases))))

(defthm bvlt-of-bvplus-of-minus1-arg2-when-not-bvlt-cheap
  (implies (and (syntaxp (quotep k))
                (equal k (+ -1 (expt 2 size)))
                (not (bvlt size x y))
                (natp size))
           (equal (bvlt size x (bvplus size k y))
                  (if (equal 0 (bvchop size y))
                      (bvlt size x k) ;odd case
                    nil)))
  :rule-classes ((:rewrite :backchain-limit-lst (nil nil 0 nil)))
  :hints (("Goal" :by bvlt-of-bvplus-of-minus1-arg2-when-not-bvlt)))
