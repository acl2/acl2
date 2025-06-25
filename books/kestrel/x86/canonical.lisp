; Theorems related to canonical-address-p.
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA") ;; unlike most books, this one is in the X86ISA package

(include-book "projects/x86isa/machine/application-level-memory" :dir :system) ; for canonical-address-p
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

;tighten?
(defthm x86isa::signed-byte-p-64-when-canonical-address-p-cheap
  (implies (canonical-address-p x)
           (signed-byte-p 64 x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable signed-byte-p canonical-address-p))))

(defthm x86isa::canonical-address-p-foward-to-signed-byte-p
  (implies (canonical-address-p lin-addr)
           (signed-byte-p 48 lin-addr))
  :rule-classes ((:forward-chaining))
  :hints (("Goal" :in-theory (enable canonical-address-p))))

(defthm canonical-address-p-of-if
  (equal (canonical-address-p (if test a1 a2))
         (if test
             (canonical-address-p a1)
           (canonical-address-p a2))))

;; k is between klow and khigh
;; one way to know that something (here, (+ klow load-offset)) is canonical is to know that it's equal to the RIP
;; we could forward-chain from equal rip to canonical (does forward-chaining happen during symsim?)
(defthm canonical-address-p-of-+-when-canonical-address-p-of-+-special
  (implies (and (equal (xr :rip nil x86) (+ klow load-offset)) ;klow is a free var
                (canonical-address-p (+ khigh load-offset))
                (x86p x86) ;implies that the RIP is canonical
                (<= klow k)
                (<= k khigh)
                (natp k)
                (natp klow)
                (natp khigh)
                (integerp load-offset))
           (canonical-address-p (+ k load-offset)))
  :hints (("Goal" :in-theory (enable canonical-address-p signed-byte-p))))

;pretty specific...
;think about possible loops here
(defthm canonical-address-p-of-plus-of-rip
  (implies (and (syntaxp (quotep k))
                (equal (xr :rip nil x86) (+ freek load-offset)) ;freek and load-offset are free vars
                (syntaxp (quotep freek))
                (canonical-address-p (+ (+ k freek) ;gets evaluated
                                        load-offset)))
           (canonical-address-p (+ k (xr :rip nil x86)))))

;for axe
(defthmd canonical-address-p-becomes-signed-byte-p-when-constant
  (implies (syntaxp (quotep ad))
           (equal (canonical-address-p ad)
                  (signed-byte-p 48 ad)))
  :hints (("Goal" :in-theory (enable canonical-address-p))))

;can this loop?  do we have any rules that backchain from < to signed-byte-p?
(defthm signed-byte-p-when-between-canonical-addresses
  (implies (and (signed-byte-p 48 low)
                (signed-byte-p 48 high)
                (<= low ad)
                (<= ad high))
           (equal (signed-byte-p 48 ad)
                  (integerp ad)))
  :hints
  (("Goal"
    :in-theory (enable canonical-address-p signed-byte-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; General rule.  Hyps may often fail to be relieved (so monitoring this rule
;; may cause many failures to be printed).
(defthm canonical-address-p-between
  (implies (and (canonical-address-p low) ; low is a free var
                (<= low ad)
                (canonical-address-p high) ; high is a free var
                (<= ad high))
           (equal (canonical-address-p ad)
                  (integerp ad)))
  :hints (("Goal" :in-theory (enable canonical-address-p SIGNED-BYTE-P))))

;; These are for showing that x plus an offset is canonical:

(defthm canonical-address-p-between-special1
  (implies (and (canonical-address-p (+ low-offset x))
                (<= low-offset offset)
                (canonical-address-p (+ high-offset x))
                (<= offset high-offset)
                (integerp low-offset)
                (integerp high-offset)
                (integerp offset))
           (canonical-address-p (+ offset x))))

;case when offset = 0
(defthm canonical-address-p-between-special2
  (implies (and (canonical-address-p (+ low-offset x))
                (<= low-offset 0)
                (canonical-address-p (+ high-offset x))
                (<= 0 high-offset)
                (integerp low-offset)
                (integerp high-offset))
           (equal (canonical-address-p x)
                  (integerp x))))

;case when low-offset = 0
(defthm canonical-address-p-between-special3
  (implies (and (canonical-address-p (+ high-offset x))
                (<= offset high-offset)
                (canonical-address-p x)
                (<= 0 offset)
                (integerp high-offset)
                (integerp offset))
           (canonical-address-p (+ offset x))))

;case when high-offset = 0
(defthm canonical-address-p-between-special4
  (implies (and (canonical-address-p (+ low-offset x))
                (<= low-offset offset)
                (canonical-address-p x)
                (<= offset 0)
                (integerp low-offset)
                (integerp offset))
           (canonical-address-p (+ offset x))))

(defthm canonical-address-p-between-special5
  (implies (and (canonical-address-p offset)
                (canonical-address-p (+ k2 offset)) ; k2 is a free var
                (<= (+ k x) k2)
                (natp k)
                (natp x)
                (natp k2))
           ;; ex (+ 192 (+ offset (ash (bvchop 32 (rdi x86)) 2)))
           (canonical-address-p (+ k offset x))))

(defthm canonical-address-p-between-special5-alt
  (implies (and (canonical-address-p offset)
                (canonical-address-p (+ k2 offset)) ; k2 is a free var
                (<= (+ k x) k2)
                (natp k)
                (natp x)
                (natp k2))
           (canonical-address-p (+ k x offset))))

(defthm canonical-address-p-between-special6
  (implies (and (canonical-address-p (+ k1 base))
                (syntaxp (quotep k1))
                (canonical-address-p (+ k2 base))
                (syntaxp (quotep k2))
                (< k1 k2) ; break symmetry
                (<= k1 (+ x1 x2))
                (<= (+ x1 x2) k2)
                (integerp k1)
                (integerp x1)
                (integerp x2)
                (integerp k2))
           (canonical-address-p (+ x1 x2 base))))

(defthm canonical-address-p-between-special7
  (implies (and (canonical-address-p (+ k1 base)) ; k1 is a free var
                (syntaxp (quotep k1))
                (<= k1 (+ x1 x2))
                (canonical-address-p (+ k2 base)) ; k2 is a free var
                (syntaxp (quotep k2))
                (< k1 k2) ; break symmetry (fail fast)
                (<= (+ x1 x2) k2)
                (integerp k1)
                (integerp x1)
                (integerp x2)
                (integerp k2))
           (canonical-address-p (+ x1 base x2))))

(defthm x86isa::logext-48-does-nothing-when-canonical-address-p
  (implies (canonical-address-p x)
           (equal (logext 48 x)
                  x)))

;; Seems needed because the model adds 7 to rsp-8 and tests whether
;; the result is canonical.  I guess it's testing the highest address
;; of the 8 byte block.
(defthm canonical-address-p-of-minus-1
  (implies (equal 0 (mod x 8))
           (equal (canonical-address-p (+ -1 x))
                  (canonical-address-p (+ -8 x))))
  :hints (("Goal"  :cases ((< X 140737488355336))
           :in-theory (enable canonical-address-p signed-byte-p ;acl2::mod-=-0
                              ACL2::FLOOR-MOD-ELIM-RULE
                                     ))))

;can loop with CANONICAL-ADDRESS-P-BETWEEN
(defthmd integerp-when-canonical-address-p
  (implies (canonical-address-p x)
           (integerp x)))

(defthmd integerp-when-canonical-address-p-cheap
  (implies (and (canonical-address-p free) ; poor man's backchain limit
                ;; todo: could require syntactic equality here:
                (equal free x))
           (integerp x)))


(defthm canonical-address-p-of-logext-64
  (implies (canonical-address-p x)
           (canonical-address-p (logext 64 x)))
  :hints (("Goal" :in-theory (enable canonical-address-p)))) ;when can we drop the logext completely?


;add one for the upper bound as well?
;looped with the between lemma?
(defthmd not-<-when-canonical-address-p
  (implies (and (syntaxp (quotep k))
                (< k (- (expt 2 47)))
                (canonical-address-p x))
           (not (< x k))))

;;todo #1
;; (CANONICAL-ADDRESS-P$INLINE (LOGEXT '64
;;                                           (ACL2::BVPLUS '64
;;                                                         '18446744073709551604
;;                                                         (XR ':RGF '4 X86))))


;todo: fix this rule
;; (defthm signed-byte-p-of-+-between
;;   (implies (and (canonical-address-p (+ big-neg-offset x))
;;                 (<= big-neg-offset small-neg-offset)
;;                 (canonical-address-p x)
;;                 ;(integerp x)
;;                 (integerp small-neg-offset)
;;                 (integerp big-neg-offset)
;;                 (<= 0 small-neg-offset) ;gen? ;TODO: This doesn't make sense
;;                 (signed-byte-p 16 small-neg-offset) ;gen
;;                 )
;;            (signed-byte-p '64 (+ small-neg-offset x)))
;;   :hints (("Goal" :in-theory (enable ;canonical-address-p signed-byte-p
;;                               ))))

; Maybe this is the loop: CANONICAL-ADDRESS-P-BETWEEN backchains from CANONICAL-ADDRESS-P to
; some < claims, but several rules (such as <-WHEN-CANONICAL-ADDRESS-P)
; backchain from < claims to CANONICAL-ADDRESS-P claims.

;; (DEFTHM CANONICAL-ADDRESS-P-OF-+-WHEN-CANONICAL-ADDRESS-P-OF-+-alt
;;   (IMPLIES (AND (CANONICAL-ADDRESS-P (+ K2 LOAD-OFFSET))
;;                 (<= K K2)
;;                 (NATP K)
;;                 (NATP K2)
;;                 (CANONICAL-ADDRESS-P LOAD-OFFSET))
;;            (CANONICAL-ADDRESS-P (+ K LOAD-OFFSET)))
;;   :HINTS
;;   (("Goal"
;;     :IN-THEORY (ENABLE CANONICAL-ADDRESS-P SIGNED-BYTE-P))))

(defthm canonical-address-p-of-one-more-when-between
  (implies (and (canonical-address-p base-addr)
                (canonical-address-p (+ -1 base-addr n))
                (< 1 n)
                (integerp n))
           (canonical-address-p (+ 1 base-addr)))
  :hints (("Goal" :in-theory (enable canonical-address-p signed-byte-p))))

;move
(defthm logext-64-does-nothing-when-canonical-address-p
  (implies (canonical-address-p x)
           (equal (logext 64 x)
                  x)))


;; We'll try keeping i48 disabled for now (the x86 books may do the opposite):
(in-theory (disable x86isa::i48$inline))

(defthm canonical-address-p-of-i48
  (canonical-address-p (x86isa::i48 x))
  :hints (("Goal" :in-theory (enable x86isa::i48 canonical-address-p))))

(defthm i48-when-canonical-address-p
  (implies (canonical-address-p x)
           (equal (x86isa::i48 x)
                  x))
  :hints (("Goal" :in-theory (enable x86isa::i48 canonical-address-p))))

(defthm canonical-address-p-when-unsigned-byte-p
  (implies (unsigned-byte-p 47 ad)
           (canonical-address-p ad))
  :hints (("Goal" :in-theory (enable canonical-address-p))))

(defthm canonical-address-p-of-sum-when-unsigned-byte-p-32
  (implies (and (unsigned-byte-p 32 ad)
                (unsigned-byte-p 32 k) ;gen
                )
           (canonical-address-p (+ k ad))))

(defthm canonical-address-p-of-+-of-constant-when-natp
  (implies (and (syntaxp (quotep k))
                (natp k)
                (natp x))
           (equal (canonical-address-p (+ k x))
                  (< x (- (expt 2 47) k))))
  :hints (("Goal" :cases ((< (+ K X) 140737488355328)) ; why?
           )))
