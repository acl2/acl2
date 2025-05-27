; BV Rules used by the Formal Unit Tester
;
; Copyright (C) 2016-2023 Kestrel Technology, LLC
; Copyright (C) 2024-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;; TODO: Move this material to libraries.
;; TODO: There are some rules here that are not strictly about BVS

;(include-book "kestrel/bv/rotate" :dir :system) ;for INTEGERP-OF-LEFTROTATE32
;(include-book "kestrel/bv/intro" :dir :system)
;(include-book "../rules1")
;(include-book "../axe-rules-mixed")
(include-book "kestrel/bv/bvlt" :dir :system)
(include-book "kestrel/bv/sbvlt" :dir :system)
(include-book "kestrel/bv/bvdiv" :dir :system)
(include-book "kestrel/bv/sbvdiv" :dir :system)
(include-book "kestrel/bv/bvmod" :dir :system)
(include-book "kestrel/bv/bvsx" :dir :system)
(include-book "kestrel/bv/bvand" :dir :system)
(include-book "kestrel/bv/bvxor" :dir :system)
(include-book "kestrel/bv/bvif" :dir :system)
(include-book "kestrel/bv/bvshl" :dir :system)
(include-book "kestrel/bv/bvmult" :dir :system)
(include-book "kestrel/bv/bool-to-bit" :dir :system)
(include-book "kestrel/booleans/boolif" :dir :system)
;(local (include-book "../axe-rules-mixed")) ; drop?
(local (include-book "../rules3")) ;drop
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system)) ; reduce?
(local (include-book "kestrel/arithmetic-light/divide" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divide" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/ash" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/bv/logand-b" :dir :system))
(local (include-book "kestrel/bv/logior" :dir :system))
(local (include-book "kestrel/bv/logxor-b" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/bv/bvsx-rules" :dir :system))
;(local (include-book "kestrel/bv/signed-byte-p" :dir :system))

;gen
(defthm not-sbvlt-of-sbvdiv-and-minus-constant-32-64
  (implies (unsigned-byte-p 31 x)
           (not (sbvlt 64 (sbvdiv 64 x y) 18446744071562067968)))
  :hints (("Goal" :in-theory (enable sbvdiv sbvlt))))

(defthm not-sbvlt-of-constant-and-sbvdiv-32-64
  (implies (unsigned-byte-p 31 x)
           (not (sbvlt 64 2147483647 (sbvdiv 64 x y))))
  :hints (("Goal" :in-theory (enable sbvdiv sbvlt))))

(defthm not-bvlt-of-constant-and-bvdiv-64-128
  (implies (unsigned-byte-p 64 x)
           (not (bvlt 128 18446744073709551615 (bvdiv 128 x y))))
  :hints (("Goal" :in-theory (enable bvdiv bvlt))))

(defthm not-bvlt-of-constant-and-bvdiv-32-64
  (implies (unsigned-byte-p 32 x)
           (not (bvlt 64 4294967295 (bvdiv 64 x y))))
  :hints (("Goal" :in-theory (enable bvdiv bvlt))))

;todo: gen
(defthm <-of-15-and-*-of-4
  (implies (natp x)
           (equal (< 15 (* x 4))
                  (< 3 x))))

;; (defthmd <-of-floor-when-<
;;   (implies (and (< x y)
;;                 (rationalp x))
;;            (< (floor x 1) y)))

(defthm <-of-*-when-constant-integers
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (posp k2) ; gen?
                (integerp k1)
                (integerp x))
           (equal (< k1 (* k2 x))
                  (let ((quot (/ k1 k2)))
                    (if (integerp quot)
                        (< quot x)
                      (< (floor quot 1) x)))))
  :hints (("Goal" ;:in-theory (enable <-of-floor-when-<)
           :cases ((<= x (/ K1 k2))))))

;gen
;why is this needed? maybe because of <-BECOMES-BVLT-AXE-BIND-FREE-ARG1-STRONG
(defthm unsigned-byte-p-2-of-bvchop-when-bvlt-of-4
  (implies (bvlt '32 x '4)
           (unsigned-byte-p '2 (bvchop '32 x))))

;; could restrict to constants
(defthm bvsx-when-bvlt
  (implies (and (bvlt old-size x (expt 2 (+ -1 old-size)))
                (natp old-size)
                (<= old-size new-size))
           (equal (bvsx new-size old-size x)
                  (bvchop old-size x)))
 :hints (("Goal" :in-theory (enable bvsx))))


;; (defthmd bvlt-hack-1
;;   (implies (not (bvlt 16 x 1))
;;            (equal (bvlt 16 x 2)
;;                   (equal (bvchop 16 x) 1)))
;;   :hints (("Goal" :in-theory (enable bvlt))))

;loops with boolif-of-bvlt-strengthen-to-equal?
;rename
;not used?
(defthmd bvlt-hack-1-gen
  (implies (and (syntaxp (quotep k))
                (not (bvlt 16 x (+ -1 k)))
                (< k (expt 2 16))
                (posp k))
           (equal (bvlt 16 x k)
                  (equal (bvchop 16 x) (+ -1 k))))
  :hints (("Goal" :in-theory (enable bvlt
                                     bvchop-of-sum-cases))))

;; (defthm boolif-of-t-and-nil-when-booleanp
;;   (implies (booleanp x)
;;            (equal (boolif x t nil)
;;                   x)))

(defthm boolif-of-bvlt-strengthen-to-equal-gen
  (implies (and (syntaxp (quotep k))
                (not (bvlt 16 x (+ -1 k)))
                (< k (expt 2 16))
                (posp k))
           (equal (boolif (bvlt 16 x k) then else)
                  (boolif (equal (bvchop 16 x) (+ -1 k)) then else)))
  :hints (("Goal" :in-theory (enable boolor
                                     bvlt ;todo
                                     bvchop-of-sum-cases
                                     BOOLIF
                                     ))))

(defthm boolif-of-bvlt-strengthen-to-equal
  (implies (and (syntaxp (quotep k))
                (not (bvlt 16 x (+ -1 k)))
                (< k (expt 2 16))
                (posp k))
           (equal (boolif (bvlt 16 x k) t else)
                  (boolif (equal (bvchop 16 x) (+ -1 k)) t else)))
  :hints (("Goal" :in-theory (enable boolor boolif
                                     bvlt ;todo
                                     bvchop-of-sum-cases
                                     ))))


;; use polarities?
(defthm bvlt-reduce-when-not-equal-one-less
  (implies (and (syntaxp (quotep k))
                (not (equal (+ -1 k) (bvchop 16 x)))
                (< k (expt 2 16))
                (posp k))
           (equal (bvlt 16 x k)
                  (bvlt 16 x (+ -1 k))))
  :hints (("Goal" :in-theory (enable boolor
                                     bvlt ;todo
                                     bvchop-of-sum-cases
                                     ))))

(theory-invariant (incompatible (:rewrite bvcat-of-minus-becomes-bvshl)
                                (:definition bvshl )))

;; (defthm not-equal-of-0-and-bvshl-of-1
;;   (implies (and (natp amt)
;;                 (< amt 32))
;;            (not (equal 0 (bvshl 32 1 amt))))
;;   :hints (("Goal" :in-theory (e/d (bvshl)
;;                                   (bvcat-of-minus-becomes-bvshl)))))


;; Library stuff:

;; or commute the 1 forward first
;; or use the fact that 1 is a mask of all 1s
; or do we have better ways to get rid of logand?
(defthm logand-of-1-becomes-getbit-arg2
  (equal (logand x 1)
         (getbit 0 x))
  :hints (("Goal" :cases ((integerp x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: generalize with a set of rules like the trim rules
;gen
(defthm bvplus-of-logxor-arg1
  (equal (bvplus 32 (logxor x y) z)
         (bvplus 32 (bvxor 32 x y) z))
  :hints (("Goal" :in-theory (enable bvxor))))

;todo: more like this
(defthm bvxor-of-logxor-arg2
  (equal (bvxor size x (logxor y z))
         (bvxor size x (bvxor size y z)))
  :hints (("Goal" :in-theory (enable bvxor))))

(defthm bvdiv-tighten-64-32 ;gen
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (BVDIV 64 x y)
                  (BVDIV 32 x y)))
  :hints (("Goal" :in-theory (enable bvdiv))))

(defthm bvmod-tighten-64-32 ;gen
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (BVmod 64 x y)
                  (BVmod 32 x y)))
  :hints (("Goal" :in-theory (enable bvmod))))

(defthm not-bvlt-of-max-when-unsiged-byte-p
  (implies (unsigned-byte-p 32 x)
           (not (bvlt 64 4294967295 x))))

;(in-theory (disable X86ISA::INTEGERP-WHEN-CANONICAL-ADDRESS-P-CHEAP)) ;todo

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;gen the sizes
(defthm bvuminus-of-bvif-constants
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)))
           (equal (bvuminus 32 (bvif 1 test k1 k2))
                  (bvif 32 test (bvuminus 32 (bvchop 1 k1)) (bvuminus 32 (bvchop 1 k2)))))
  :hints (("Goal" :in-theory (enable bvif getbit))))

(defthm ifix-of-if
  (equal (ifix (if test x86 x86_2))
         (if test (ifix x86) (ifix x86_2))))


;; (thm
;;  (IMPLIES (AND (< J 0)
;;                (INTEGERP I)
;;                (INTEGERP J))
;;           (<= (- (/ i j)) (FLOOR I J))))

;; (thm
;;  (IMPLIES (AND (< J 0)
;;                (INTEGERP I)
;;                (posp k) ; gen?
;;                (< I k)
;;                (INTEGERP J))
;;           (<= (- k) (FLOOR I J))))


;gen!
(defthm *-of-/-linear-when-both-negative-free-linear
  (implies (and (< free i)
                (integerp free)
                (< free 0)
                (<= j -1)
                (integerp i)
                (integerp j)
                (< i 0)
                )
           (< (* i (/ j)) (- free)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable <-of-*-of-/-arg1))))

;gen!
(defthm *-of-/-linear-when-i-negative-and-positive-linear
  (implies (and (< i free)
                (integerp free)
                (< free 0)
                (<= j -1)
                (integerp i)
                (integerp j)
                (<= 0 i))
           (< (- free) (* i (/ j))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable <-of-*-of-/-arg1))))

;(in-theory (disable X86ISA::<-WHEN-CANONICAL-ADDRESS-P-IMPOSSIBLE X86ISA::<-WHEN-CANONICAL-ADDRESS-P)) ;todo bad

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Shows that the division can't be too negative
;todo: add sbvdiv to x pkg
;todo: gen the 2
(defthm not-sbvlt-64-of-sbvdiv-64-of-bvsx-64-32-and--2147483648
  (not (sbvlt 64 (sbvdiv 64 (bvsx 64 32 x) 2) -2147483648))
  :hints (("Goal" :cases ((equal 0 (getbit 31 x)))
           :in-theory (e/d (sbvlt sbvdiv bvsx bvlt logext-cases bvcat logapp
                                  truncate-becomes-floor-gen
                                  getbit-of-+
                                  bvplus
                                  bvchop-of-sum-cases)
                           ( ;disable
                            )))))

;todo: also prove for slice and logtail
(defthm getbit-of-*-of-1/2
  (implies (and (integerp x)
                (equal 0 (getbit 0 x)) ; needed?
                (natp n))
           (equal (getbit n (* 1/2 x))
                  (getbit (+ 1 n) x)))
  :hints (("Goal" :in-theory (enable getbit slice logtail expt-of-+ ifix bvchop))))



;; Shows that the division can't be too positive
;; todo: gen the 2 but watch for the one weird case
(defthm not-sbvlt-64-of-2147483647-and-sbvdiv-64-of-bvsx-64-32
  (not (sbvlt 64 2147483647 (sbvdiv 64 (bvsx 64 32 x) 2) ))
  :hints (("Goal" :cases ((equal 0 (getbit 31 x)))
           :in-theory (e/d (sbvlt sbvdiv bvsx bvlt logext-cases bvcat logapp
                                  truncate-becomes-floor-gen
                                  getbit-of-+
                                  bvplus
                                  bvchop-of-sum-cases)
                           (sbvlt-rewrite ;disable
                            )))))

;; todo: recharacterize the x86 shift instruction so we don't need rules to put in the shifts
(defthm bvcat-of-minus-becomes-bvshl
  (implies (and (natp amt)
                (< amt 32))
           (equal (bvcat (+ 32 (- amt)) val amt 0)
                  (bvshl 32 val amt)))
  :hints (("Goal" :in-theory (enable bvshl))))

(defthm bvchop-subst-constant-alt
  (implies (and (syntaxp (not (quotep x)))
                (equal (bvchop free x) k) ; this rule
                (syntaxp (quotep k))
                (<= size free)
                ;(natp size)
                (integerp free))
           (equal (bvchop size x)
                  (bvchop size k)))
  :hints (("Goal" :use (:instance bvchop-subst-constant (free free) (size size))
           :in-theory (disable bvchop-subst-constant))))

;gen
(defthm bvcat-of-repeatbit-of-getbit-of-bvsx-same
  (implies (and (equal oldsize-1 (+ oldsize -1))
                (posp oldsize)
                (natp newsize)
                (< oldsize newsize)
                (posp size2) ; gen?
                )
           (equal (BVCAT size2 (REPEATBIT size2 (GETBIT oldsize-1 x)) newsize (BVSX newsize oldsize x))
                  (bvsx (+ size2 newsize) oldsize x))))

(defthmd bvcat-of-repeatbit-of-getbit-becomes-bvsx
  (implies (and (equal n (+ -1 lowsize))
                (posp lowsize)
                (natp highsize))
           (equal (bvcat highsize (repeatbit highsize (getbit n x)) lowsize x)
                  (bvsx (+ highsize lowsize) lowsize x)))
  :hints (("Goal" :in-theory (enable bvsx-alt-def-2
                                     repeatbit-of-1-arg2))))

(defthm not-sbvlt-of-bvsx-of-constant-arg2-64-8
  (implies (and (syntaxp (quotep k))
                (sbvle 64 k -128))
           (not (sbvlt 64 (bvsx 64 8 x) k)))
  :hints (("Goal" :in-theory (enable bvsx-alt-def-2 booland bvlt equal-of-slice sbvlt-rewrite))))

(defthm not-sbvlt-of-bvsx-of-constant-arg2-64-16
  (implies (and (syntaxp (quotep k))
                (sbvle 64 k (- (expt 2 (+ -1 16)))))
           (not (sbvlt 64 (bvsx 64 16 x) k)))
  :hints (("Goal" :in-theory (enable bvsx-alt-def-2 booland bvlt equal-of-slice sbvlt-rewrite))))

(defthm not-sbvlt-of-bvsx-of-constant-arg2-64-32
  (implies (and (syntaxp (quotep k))
                (sbvle 64 k (- (expt 2 (+ -1 32)))))
           (not (sbvlt 64 (bvsx 64 32 x) k)))
  :hints (("Goal" :in-theory (enable bvsx-alt-def-2 booland bvlt equal-of-slice sbvlt-rewrite))))

(defthm not-sbvlt-of-bvsx-of-constant-arg2-128-64
  (implies (and (syntaxp (quotep k))
                (sbvle 128 k (- (expt 2 (+ -1 64)))))
           (not (sbvlt 128 (bvsx 128 64 x) k)))
  :hints (("Goal" :in-theory (enable bvsx-alt-def-2 booland bvlt equal-of-slice sbvlt-rewrite))))

;; (defthm not-sbvlt-of-bvsx-of-constant-arg2-64
;;   (implies (and (syntaxp (quotep k))
;;                 (posp size)
;; ;                (equal size 8)
;;                 (< size 64)
;;                 (sbvle 64 k (- (expt 2 (+ -1 size)))))
;;            (not (sbvlt 64 (bvsx 64 size x) k)))
;;   :hints (("Goal" :cases ((EQUAL (GETBIT (+ -1 SIZE) k) 1))
;;            :in-theory (e/d (bvsx-alt-def-2 booland bvlt equal-of-slice)
;;                                   (exponents-add)))))

;gen!
(defthm not-sbvlt-of-bvsx-of-constant-arg3-64-8
  (implies (and (syntaxp (quotep k))
                (sbvle 64 (+ -1 128) k))
           (not (sbvlt 64 k (bvsx 64 8 x))))
  :hints (("Goal" :in-theory (enable bvsx-alt-def-2 booland bvlt equal-of-slice sbvlt-rewrite))))

(defthm not-sbvlt-of-bvsx-of-constant-arg3-64-16
  (implies (and (syntaxp (quotep k))
                (sbvle 64 (+ -1 (expt 2 (+ -1 16))) k))
           (not (sbvlt 64 k (bvsx 64 16 x))))
  :hints (("Goal" :in-theory (enable bvsx-alt-def-2 booland bvlt equal-of-slice sbvlt-rewrite))))

(defthm not-sbvlt-of-bvsx-of-constant-arg3-64-32
  (implies (and (syntaxp (quotep k))
                (sbvle 64 (+ -1 (expt 2 (+ -1 32))) k))
           (not (sbvlt 64 k (bvsx 64 32 x))))
  :hints (("Goal" :in-theory (enable bvsx-alt-def-2 booland bvlt equal-of-slice sbvlt-rewrite))))

(defthm not-sbvlt-of-bvsx-of-constant-arg3-128-64
  (implies (and (syntaxp (quotep k))
                (sbvle 128 (+ -1 (expt 2 (+ -1 64))) k))
           (not (sbvlt 128 k (bvsx 128 64 x))))
  :hints (("Goal" :in-theory (enable bvsx-alt-def-2 booland bvlt equal-of-slice sbvlt-rewrite))))

(defthm bvcat-of-repeatbit-tighten-64-32 ;gen!
  (equal (bvcat 64 (repeatbit 32 bit) 32 lowval)
         (bvcat 32 (repeatbit 32 bit) 32 lowval)))

(defthm sbvlt-of-bvsx-32-16-constant
  (implies (and (syntaxp (quotep k))
                (unsigned-byte-p 15 k) ;gen?
                )
           (equal (sbvlt 32 k (bvsx 32 16 x))
                  (and (sbvlt 16 k x)
                       (not (sbvlt 16 x 0)))))
  :hints (("Goal" :in-theory (enable bvlt BVSX-ALT-DEF-2 sbvlt-rewrite))))

;; todo: constant opener for X86ISA::!RFLAGSBITS->AF$INLINE

;todo: gen the 0
(defthm if-of-sbvlt-and-not-sbvlt-helper
  (implies (and (posp size)
                (sbvle size 0 k) ; gen?
                )
           (equal (if (sbvlt size k x)
                      (not (sbvlt size x 0))
                    else)
                  (if (sbvlt size k x)
                      t
                    else)))
  :hints (("Goal" :in-theory (disable))))

;; arises in array indexing -- try without this
(defthm logext-of-+-of-bvplus-same-size
  (implies (and (integerp k)
                (integerp text-offset)
                (integerp index))
           (equal (logext 64 (binary-+ k (bvplus 64 text-offset index)))
                  (logext 64 (binary-+ k (+ text-offset index)))))
  :hints (("Goal" :in-theory (enable equal-of-logext-and-logext bvplus))))

;slow!
;; arises in array indexing -- try without this
(defthm logext-of-+-of-+-of-mult-same-size ; alt versions?
  (implies (and (integerp k)
                (integerp text-offset)
                (integerp index)
                (integerp val))
           (equal (logext 64 (+ k (+ (bvmult 64 val index) text-offset)))
                  (logext 64 (+ k (+ (* val index) text-offset)))))
  :hints (("Goal" :in-theory (e/d (equal-of-logext-and-logext bvmult)
                                  (;X86ISA::LOGEXT-64-DOES-NOTHING-WHEN-CANONICAL-ADDRESS-P
                                   ;BVCHOP-TIGHTEN-WHEN-UNSIGNED-BYTE-P
                                   UNSIGNED-BYTE-P-FROM-BOUNDS
                                   )))))

;; (thm
;;  (implies (and (signed-byte-p 48 x)
;;                (signed-byte-p 48 y))
;;           (equal (equal (bvchop 48 x) (bvchop 48 y))
;;                  (equal x y)))
;;  :hints (("Goal" :in-theory (enable ))))

;; for when we have to disable the executable-counterpart
;; todo: doesn't limit-expt handle this?
(defthmd expt-of-2-and-48
  (equal (expt 2 48)
         281474976710656))

(defthm equal-of-constant-and-bvchop-when-signed-byte-p
  (implies (and (syntaxp (quotep k))
                (signed-byte-p size x))
           (equal (equal k (bvchop size x))
                  (and (unsigned-byte-p size k)
                       (equal (logext size k) x))))
  :hints (("Goal" :in-theory (enable signed-byte-p)
           :use (:instance logext-of-bvchop-same
                           (size size)))))

(defthmd equal-of-bvchop-when-signed-byte-p
  (implies (and ;; (syntaxp (quotep k))
                (signed-byte-p size x))
           (equal (equal k (bvchop size x))
                  (and (unsigned-byte-p size k)
                       (equal (logext size k) x))))
  :hints (("Goal" :in-theory (enable signed-byte-p)
           :use (:instance logext-of-bvchop-same
                                  (size size)))))

(defthm bvchop-when-signed-byte-p-and-<-of-0
  (implies (and (signed-byte-p 48 x)
                (< x 0))
           (equal (bvchop 48 x)
                  (+ x (expt 2 48))))
  :hints (("Goal" :in-theory (enable equal-of-bvchop-when-signed-byte-p signed-byte-p))))

;; Pretty aggressive
(defthmd bvchop-when-signed-byte-p-cases-cheap
  (implies (signed-byte-p 48 x)
           (equal (bvchop 48 x)
                  (if (< x 0)
                      (+ x (expt 2 48))
                    x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable equal-of-bvchop-when-signed-byte-p signed-byte-p))))

(defthm <-of-bvchop-and-bvchop-when->=-and-signed-byte-p-and-signed-byte-p
  (implies (and (<= x y)
                (signed-byte-p 48 x)
                (signed-byte-p 48 y))
           (equal (< (bvchop 48 y) (bvchop 48 x))
                  (and (< x 0)
                       (and (<= 0 y)
                            (< y (expt 2 47))))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil)))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

(defthm signed-byte-p-of-+-forward
  (implies (and (signed-byte-p 48 (+ k x))
                (syntaxp (quotep k)))
           (and (< x (- (expt 2 47) k))
                (<= (+ (- (expt 2 47)) (- k)) x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable signed-byte-p))))

;could do it when either arg is constant?
(defthm slice-of-bvand-of-constant
  (implies (and (syntaxp (and (quotep x)
                              (quotep high)
                              (quotep low)))
                (<= low high)
                (<= (+ 1 high) size) ;drop?
                (natp size)
                (natp low)
                (natp high))
           (equal (slice high low (bvand size x y))
                  (bvand size
                         (slice high low x) ; gets computed
                         (slice high low y))))
  :hints (("Goal" :in-theory (e/d (bvand)
                                  (;logand-of-bvchop-becomes-bvand-alt ;loop
                                   ;logand-of-bvchop-becomes-bvand ;loop
                                   )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: drop?
(defthm bvchop-of-bool-to-bit
  (implies (posp n)
           (equal (bvchop n (bool-to-bit bool))
                  (bool-to-bit bool))))

;todo: drop?
(defthm logext-of-bool-to-bit
  (implies (and (< 1 n)
                (integerp n))
           (equal (logext n (bool-to-bit bool))
                  (bool-to-bit bool))))
