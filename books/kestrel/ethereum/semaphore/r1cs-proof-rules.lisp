; Rules to support R1CS proofs
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZKSEMAPHORE")

;todo: reduce:
(include-book "kestrel/ethereum/semaphore/printing" :dir :system) ; so we can refer to the constants below
(include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)
(include-book "kestrel/axe/axe-syntax" :dir :system) ; for acl2::axe-bind-free
(include-book "kestrel/axe/axe-syntax-functions-bv" :dir :system) ; for acl2::bind-bv-size-axe
(local (include-book "kestrel/prime-fields/bind-free-rules" :dir :system))
(local (include-book "kestrel/prime-fields/bv-rules" :dir :system))
(include-book "kestrel/crypto/r1cs/gadgets/xor-rules" :dir :system)
;(include-book "kestrel/crypto/r1cs/tools/axe-rules-r1cs" :dir :system)
(include-book "kestrel/bv/rules" :dir :system) ; for ACL2::BVXOR-WITH-SMALLER-ARG-1, drop
;(include-book "kestrel/axe/rules3" :dir :system) ;for ACL2::PLUS-OF-BVCAT-FITS-IN-LOW-BITS-CORE-NEGATIVE-K1
(include-book "kestrel/utilities/fix" :dir :system)
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-times" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/bv/arith" :dir :system)) ;for ACL2::COMMUTATIVITY-2-OF-+-WHEN-CONSTANT??
(local (include-book "kestrel/bv/logtail" :dir :system))
(include-book "kestrel/crypto/primes/bn-254-group-prime" :dir :system)

;todo: file these:

;todo: replace some instances of (expt 2 32) with the number

;; (thm
;;  (implies (and (syntaxp (and (quotep k1)
;;                              (quotep k2)))
;;                ..)
;;           (equal (div k1 k2 p)
;;                  (mod (/ k1 k2)
;;                       p)))
;;  :hints (("Goal" :in-theory (enable div))))


;;because he top bit gets stuck onto the wrong cat
(defthm swing-bit-onto-outer-cat
  (implies (unsigned-byte-p 32 x)
           (equal (ADD x (ADD (ACL2::BVCAT '1 bit 32 (ACL2::BVNOT '32 bv32)) z p) p)
                  (add (acl2::bvcat 1 bit 32 x) (add (ACL2::BVNOT '32 bv32) z p) p)))
  :hints (("Goal" :in-theory (e/d (add acl2::bvcat acl2::logapp) (;R1CS::BVCAT-OF-BVXOR-LOW-WHEN-QUOTEP ;looped
                                                                  )))))

;; x=y-z becomes x+z=y
;move
(defthm pfield::equal-of-add-of-neg-arg2-solve
  (implies (and (posp p)
                (integerp y))
           (equal (equal x (add y (neg z p) p))
                  (and (equal (add x z p)
                              (mod (ifix y) p))
                       (fep x p)))))

;gen.  see also the -8 version
(DEFTHM ACL2::ADDING-32-IDIOM
  (IMPLIES(AND (BITP R1CS::X)
               (UNSIGNED-BYTE-P 32 R1CS::Y)
               (UNSIGNED-BYTE-P 32 W)
               (UNSIGNED-BYTE-P 32 R1CS::Z)
               (POSP R1CS::P)
               (< (expt 2 (+ 1 32)) R1CS::P))
          (EQUAL (EQUAL (ACL2::BVCAT 1 R1CS::X 32 R1CS::Y)
                        (ADD W R1CS::Z R1CS::P))
                 (AND (EQUAL R1CS::X
                             (ACL2::GETBIT 32 (ACL2::BVPLUS (+ 1 32) W R1CS::Z)))
                      (EQUAL R1CS::Y (ACL2::BVPLUS 32 W R1CS::Z)))))
  :HINTS (("Goal" :IN-THEORY (ENABLE ADD ACL2::BVPLUS))))

;gen.  see also the -8 version
(DEFTHM ACL2::ADDING-32-IDIOM-alt
  (IMPLIES(AND (BITP R1CS::X)
               (UNSIGNED-BYTE-P 32 R1CS::Y)
               (UNSIGNED-BYTE-P 32 W)
               (UNSIGNED-BYTE-P 32 R1CS::Z)
               (POSP R1CS::P)
               (< (expt 2 (+ 1 32)) R1CS::P))
          (EQUAL (EQUAL (ADD W R1CS::Z R1CS::P)
                        (ACL2::BVCAT 1 R1CS::X 32 R1CS::Y))
                 (AND (EQUAL R1CS::X
                             (ACL2::GETBIT 32 (ACL2::BVPLUS (+ 1 32) W R1CS::Z)))
                      (EQUAL R1CS::Y (ACL2::BVPLUS 32 W R1CS::Z)))))
  :HINTS (("Goal" :IN-THEORY (ENABLE ADD ACL2::BVPLUS))))

(local (in-theory (disable acl2::bitp-becomes-unsigned-byte-p)))

(defthm add-of-neg-of-bvcat-of-0-and-neg-when-unsigned-byte-p
  (implies (and (unsigned-byte-p lowsize x)
                (posp p))
           (equal (add (neg (acl2::bvcat highsize highval lowsize 0) p)
                       (neg x p) p)
                  (neg (acl2::bvcat highsize highval lowsize x) p)))
  :hints (("Goal" :in-theory (e/d (add acl2::bvcat acl2::logapp neg
                                       acl2::mod-sum-cases)
                                  (pfield::mod-of-ifix-when-fep
                                   pfield::mod-when-fep)))))

;; (equal '1368015184586208377692962645747596915105636153469842199510504144919754569108
;;        (pfield::neg (pfield::inv #x100000000 21888242871839275222246405745257275088548364400416034343698204186575808495617) 21888242871839275222246405745257275088548364400416034343698204186575808495617))

;very odd
(defthmd add-of-mul-normalize-coeffs
  (implies (and (primep p)
                (fep y p) ;drop?
                (fep k p) ;drop?
                (not (equal 0 k)))
           (equal (add (mul k x p) y p)
                  (mul k (add x (mul (pfield::inv k p) y p) p) p)))
  :hints (("Goal" :in-theory (e/d (pfield::mul-combine-constants-alt)
                                  (;R1CS::MUL-WHEN-CONSTANTS
                                   PFIELD::MUL-OF-POWER-OF-2-WHEN-BITP
                                   PFIELD::MUL-ASSOCIATIVE
                                   PFIELD::MUL-COMMUTATIVE
                                   PFIELD::NEG-WHEN-CONSTANT-ARG1)))))

;; specific to the prime because *-1/2^32* is
(defthmd add-of-mul-normalize-coeffs-2
  (implies (and (equal p PRIMES::*BN-254-GROUP-PRIME*)
                ;(< (expt 2 32) p)
                (fep y p) ;drop?
                )
           (equal (add (mul *-1/2^32* x p) y p)
                  (mul *-1/2^32* (add x (mul (pfield::inv *-1/2^32* p) y p) p) p)))
  :hints (("Goal" :use (:instance add-of-mul-normalize-coeffs
                                  (k *-1/2^32*))
           :in-theory (disable ;R1CS::MUL-NORMALIZE-CONSTANT-ARG1 ;looped
                               ))))

;; specific to the prime because *-1/2^32* is
;can loop?
(defthmd bitp-of-add-of-mul-normalize-coeffs
  (implies (and (equal p PRIMES::*BN-254-GROUP-PRIME*) ; (primep p)
                (fep y p)
                ;(< (expt 2 32) p)
                )
           (equal (bitp (add (mul *-1/2^32* x p) y p))
                  (bitp (mul *-1/2^32* (add x (mul (pfield::inv *-1/2^32* p) y p) p) p))))
  :hints (("Goal" :use (:instance add-of-mul-normalize-coeffs-2)
           :in-theory (disable ;r1cs::mul-normalize-constant-arg1 ;looped
                               ))))

(defthmd bvcat-33-1-0-becomes-mul
  (implies (and (posp p)
                (< (expt 2 34) p))
           (equal (acl2::bvcat 33 x 1 0)
                  (mul 2 (acl2::bvchop 33 x) p)))
  :hints (("Goal" :in-theory (enable acl2::bvcat acl2::logapp mul))))

(defthm unsigned-byte-p-of-add-of-ones-33
  (implies (and (unsigned-byte-p 33 x)
                (integerp p)
                (< (expt 2 33) p))
           (unsigned-byte-p 33 (ADD 8589934591 (NEG x P) P)))
  :hints (("Goal" :in-theory (enable add neg ACL2::MOD-SUM-CASES))))

(defthm equal-of-mul-of-2-and-slice-32-1-same
 (implies (and (posp p)
               (< (expt 2 34) p)
               (integerp x) ;(unsigned-byte-p 34 x) ;gen?
               )
          (equal (equal (mul 2 (acl2::slice 32 1 x) p) x)
                 (and (unsigned-byte-p 33 x)
                      (evenp x))))
 :hints (("Goal" :in-theory (e/d (mul acl2::slice ACL2::LOGTAIL)
                                 (ACL2::BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

(in-theory (disable evenp))

(defthm slice-of-mul-of-2
  (implies (and (posp p)
                (< (expt 2 34) p)
                ;(integerp x) ;(unsigned-byte-p 34 x) ;gen?
                (natp x)
                (< (* 2 x) p)
                )
           (equal (acl2::slice 32 1 (mul 2 x p))
                  (acl2::bvchop 32 x)))
  :hints (("Goal" :in-theory (e/d (acl2::slice mul acl2::logtail)
                                  (acl2::bvchop-of-logtail-becomes-slice)))))

;;todo: change =0 to bitp
;;what if x is odd?
;; (thm
;;  (implies (and (posp p)
;;                (< (expt 2 34) p)
;;                (integerp x)
;;                (fep x p)
;;                (unsigned-byte-p 33 x) ;gen?
;;                (unsigned-byte-p 33 bv33) ;(integerp bv33)
;;                ;(natp kk) ;drop
;;                )
;;           (equal (bitp (add x (acl2::bvcat 33 (acl2::bvnot 33 bv33) 1 0) p))
;;                  (equal (acl2::bvchop 33 bv33)
;;                         (acl2::slice 32 1 (add
;;                                            kk ;(* 2 (+ -1 (expt 2 33))) ;kk
;;                                            x
;;                                            p)))))
;;  :otf-flg t
;;  :hints (("Goal" :in-theory (e/d (;add
;;                                   ;acl2::bvnot
;;                                   pfield::bvnot-becomes-add-of-neg
;;                                   bvcat-33-1-0-becomes-mul ;acl2::bvcat
;;                                   ;acl2::logapp
;;                                   ACL2::MOD-SUM-CASES
;;                                   ;lognot
;;                                   )
;;                                  (R1CS::BVCAT-OF-BVNOT-HIGH)))))

(defun acl2::get-addends (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (not (acl2::call-of 'add term))
      (list term)
    (append (acl2::get-addends (acl2::farg1 term))
            (acl2::get-addends (acl2::farg2 term)))))

;(set-fmt-soft-right-margin 1000 state)
;(set-fmt-hard-right-margin 1000 state)

(defthmd bitp-of-add-of-add-of-mul-normalize-coeffs
  (implies (and (equal p *bn-254-group-prime*)
;         (fep (+ y1 y2) p)
;                (< (expt 2 32) p)
                (integerp y1)
                (integerp y2)
                (integerp p))
           (equal (bitp (add y1 (add (mul *-1/2^32* x p) y2 p) p))
                  (bitp (mul *-1/2^32*
                             (add (mul (pfield::inv *-1/2^32* p)
                                       y1 p)
                                  (add x
                                       (mul (pfield::inv *-1/2^32* p)
                                            y2 p)
                                       p)
                                  p)
                             p))))
  :hints (("Goal" :use (:instance bitp-of-add-of-mul-normalize-coeffs (y (+ y1 y2)))
           :in-theory (disable ;r1cs::mul-normalize-constant-arg1
                               bitp-of-add-of-mul-normalize-coeffs
                               bitp))))

;; this version permutes the args to the ADD in the LHS
(defthmd bitp-of-add-of-mul-normalize-coeffs-alt
  (implies (and (equal p *bn-254-group-prime*)
                (fep y p)
                ;(< (expt 2 32) p)
                )
           (equal (bitp (add y (mul *-1/2^32* x p) p))
                  (bitp (mul *-1/2^32*
                             (add x
                                  (mul (pfield::inv *-1/2^32* p)
                                       y p)
                                  p)
                             p))))
  :hints (("Goal" :use (:instance bitp-of-add-of-mul-normalize-coeffs)
           :in-theory (disable bitp-of-add-of-mul-normalize-coeffs
                               ;r1cs::mul-normalize-constant-arg1-alt ;looped
                               ))))

(defthm mul-of-add-constant-special
  (implies (posp p)
           (equal (mul *-2^32* (add x y p) p)
                  (add (mul *-2^32* x p)
                       (mul *-2^32* y p)
                       p))))

(defthm mul-of-add-constant-special-alt
  (implies (posp p)
           (equal (mul *-2^32-neg* (add x y p) p)
                  (add (mul *-2^32-neg* x p)
                       (mul *-2^32-neg* y p)
                       p))))

(table acl2::axe-rule-priorities-table 'mul-of-add-constant-special-alt 1) ;try this late

(defthm bitp-of-mul-of-1/2^32
  (implies (and                               ;(posp p)
            (EQUAL P *BN-254-GROUP-PRIME*)    ;(PRIMEP P)
            (fep x p)
            ;(< (expt 2 33) p) ;needed?
            )
           (equal (bitp (mul *1/2^32* x p))
                  (or (equal x 0)
                      (equal x (expt 2 32)))))
  :hints (("Goal" :in-theory (disable ACL2::BITP-BECOMES-UNSIGNED-BYTE-P))))

(defthm equal-of-+-of-bvchop-same-33
  (implies (and (unsigned-byte-p 33 x)
                (integerp y))
           (equal (equal (+ y (bvchop 32 x)) x)
                  (equal y (* (expt 2 32) (getbit 32 x)))))
  :hints (("Goal" :use (:instance acl2::split-bv (y x)
                                  (n 33)
                                  (m 32))
           :in-theory (enable bvcat acl2::logapp))))

(defthmd acl2::split-bv-with-logapp
  (implies (integerp x)
           (equal (acl2::logapp size (bvchop size x) (acl2::logtail size x))
                  x)))

(defthm equal-of-+-of-bvchop-same-32-gen
  (implies (and (integerp x)
                (integerp y))
           (equal (equal (+ y (bvchop 32 x)) x)
                  (equal y (* (expt 2 32) (acl2::logtail 32 x)))))
  :hints (("Goal" :use (:instance acl2::split-bv-with-logapp (x x)
                                  (size 32))
           :in-theory (enable bvcat acl2::logapp))))

(defthmd equal-of-logtail-and-constant
  (implies (and (syntaxp (quotep k))
                (integerp x)
                (integerp k))
           (equal (equal (acl2::logtail 32 x) k)
                  (and (<= (* (expt 2 32) k) x)
                       (< x (* (expt 2 32) (+ 1 k))))))
  :hints (("Goal" :in-theory (enable acl2::logtail))))

;; The difference of the 33-bit thing and the 32-bit thing is either 0 or 2^32.
;; So the difference is the carry and the rest of the bits are equal.
(defthm bitp-of-mul-of-1/2^32-and-add-of-neg-33-32
  (implies (and (equal p *bn-254-group-prime*)
                ;;(posp p)
                (unsigned-byte-p 32 bv32)
                (unsigned-byte-p 33 bv33)
                ;;(< (expt 2 33) p) ;needed?
                )
           (equal (bitp (mul *1/2^32* (add bv33 (neg bv32 p) p) p))
                  (equal (bvchop 32 bv33) bv32)))
  :hints (("Goal" :expand ((UNSIGNED-BYTE-P 32
                                            (ADD -4294967296
                                                 BV33 *BN-254-GROUP-PRIME*))
                           (ADD -4294967296 BV33 *BN-254-GROUP-PRIME*)
                           (ADD 4294967296 BV32 *BN-254-GROUP-PRIME*))
           :in-theory (e/d (;add neg mul
                            ACL2::MOD-SUM-CASES
                            EQUAL-OF-LOGTAIL-AND-CONSTANT
                            ) (bitp
                            acl2::bitp-becomes-unsigned-byte-p
                            pfield::mul-of-add-arg2)))))

(defthm logtail-33-when-equal-of-logtail-32
  (IMPLIES (AND (EQUAL (ACL2::LOGTAIL 32 x) k)
                (syntaxp (quotep k))
                (integerp x))
           (EQUAL (ACL2::LOGTAIL 33 x)
                  (ACL2::LOGTAIL 1 k))))

;gen
(local
 (defthm unsigned-byte-p-helper
   (implies (and (equal (acl2::logtail 32 x) 1)
                 (natp x))
            (unsigned-byte-p 33 x))
   :hints (("Goal" :in-theory (enable acl2::logtail unsigned-byte-p)))))

(local
 (defthm unsigned-byte-p-helper-2
   (IMPLIES (AND (NOT (UNSIGNED-BYTE-P 32 BIG))
                 (NOT (EQUAL (ACL2::LOGTAIL 32 BIG) 1)))
            (NOT (UNSIGNED-BYTE-P 33 BIG)))
   :hints (("Goal" :in-theory (enable ACL2::LOGTAIL)
            :cases ((EQUAL (ACL2::LOGTAIL 32 BIG) 0))))))

;;generalizes the version with -33 above
(defthmd bitp-of-mul-of-1/2^32-and-add-of-neg-32
  (implies (and (equal p *bn-254-group-prime*)
                ;;(posp p)
                (unsigned-byte-p 32 bv32)
                ;;(< (expt 2 33) p) ;needed?
                (integerp big)
;                (unsigned-byte-p 253 big) ;less than the prime
                )
           (equal (bitp (mul *1/2^32* (add (neg bv32 p) big p) p))
                  (and (equal (bvchop 32 (mod big *bn-254-group-prime*)) bv32)
                       ;; everything but the carry and the low bits is 0:
                       (unsigned-byte-p 33 (mod big *bn-254-group-prime*)))))
  :otf-flg t
  :hints (("Goal" :expand ((UNSIGNED-BYTE-P 32
                                            (ADD -4294967296
                                                 BV33 *BN-254-GROUP-PRIME*))
                           (ADD -4294967296 BV33 *BN-254-GROUP-PRIME*)
                           (ADD 4294967296 BV32 *BN-254-GROUP-PRIME*))
           ;:use (:instance acl2::split-bv-with-logapp (x big) (size 32))
           :in-theory (e/d ( ;add neg mul
                            ACL2::MOD-SUM-CASES
                            ;;acl2::logtail
                            ) (bitp
                            acl2::bitp-becomes-unsigned-byte-p
                            pfield::mul-of-add-arg2)))))

;fairly specific
(DEFTHMd ADD-OF-MUL-NORMALIZE-based-on-second-coeff
  (IMPLIES (AND (PRIMEP P)
                (FEP Y P)
                (FEP Y0 P)
                (FEP K P)
                (NOT (EQUAL 0 K)))
           (EQUAL (ADD y0 (add (MUL K X P) Y P) p)
                  (MUL K (ADD (MUL (INV K P) Y0 P)
                              (add X (MUL (INV K P) Y P) P)
                              p)
                       P)))
  :HINTS
  (("Goal"
    :IN-THEORY (E/D (PFIELD::MUL-COMBINE-CONSTANTS-ALT)
                    (PFIELD::MUL-OF-POWER-OF-2-WHEN-BITP
                     PFIELD::MUL-ASSOCIATIVE
                     PFIELD::MUL-COMMUTATIVE
                     PFIELD::NEG-WHEN-CONSTANT-ARG1)))))



;;add of 2 small things, if a BV, is bvplus


(defthm add-of-mul-of-neg-shifted-carry-and-bvplus-34
  (implies (and (equal p *bn-254-group-prime*)
                (unsigned-byte-p free (add (mul *-2^33* bit p) (bvplus '34 x y) p)) ;avoid loop
                (equal free 33)
                (bitp bit)
                (posp p))
           (equal (add (mul *-2^33* bit p) (bvplus '34 x y) p)
                  (bvplus 33 x y)))
  :hints (("Goal"
           :use (:instance acl2::split-bv (y (BVPLUS 34 X Y))
                           (n 34) (m 33))
           :in-theory (enable add mul bvcat acl2::logapp ACL2::MOD-SUM-CASES))))

(defthm subtract-high-slice-helper-34
  (implies (unsigned-byte-p 34 x)
           (equal (+ x (- (* 2 (SLICE 33 1 x))))
                  (getbit 0 x)))
  :hints (("Goal" :in-theory (e/d (slice ACL2::LOGTAIL getbit bvchop mod)
                                  (ACL2::BVCHOP-1-BECOMES-GETBIT
                                   ACL2::SLICE-BECOMES-GETBIT)))))

(defthm equal-of-mod-of-+-of---and-0
  (implies (and (posp p)
                (integerp x)
                (integerp y))
           (equal (EQUAL (MOD (+ x (- y)) P) 0)
                  (equal (mod x p) (mod y p))))
  :hints (("Goal" :in-theory (enable acl2::mod-sum-cases))))

;(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local
 (defthm cancel-helper
   (implies (acl2-numberp x)
            (equal (EQUAL (+ x (- y)) 1)
                   (EQUAL x (+ 1 y))))))

;move
;gen
(defthm slice-of-+-of-1-and-*-2
  (implies (integerp x)
           (equal (slice 33 1 (+ 1 (* 2 x)))
                  (slice 32 0 x)))
  :hints (("Goal" :in-theory (enable slice))))

(defthmd bitp-of-add-of-mul-of--2-becomes-equal-of-slice
  (implies (and (syntaxp (quotep k))
                (equal k (- p 2)) ;to make this rule not prime-specific
                (unsigned-byte-p 34 bv34)
                (unsigned-byte-p 33 bv33)
                (< (expt 2 34) p)
                (posp p))
           (equal (bitp (add bv34 (mul k bv33 p) p))
                  (equal bv33 (slice 33 1 bv34))))
  :hints (("Goal" :in-theory (e/d (bitp add mul acl2::mod-sum-cases)
                                  (ACL2::BITP-BECOMES-UNSIGNED-BYTE-P)))))

(defthm bitp-of-add-of-mul-of--2-becomes-equal-of-slice-extra
  (implies (and (syntaxp (quotep k))
                (equal k (- p 2)) ;to make this rule not prime-specific
                (unsigned-byte-p 33 bv33a)
                (unsigned-byte-p 33 bv33b)
                (unsigned-byte-p 33 bv33)
                (< (expt 2 34) p)
                (posp p))
           (equal (bitp (add bv33a (add bv33b (mul k bv33 p) p) p))
                  (equal bv33 (slice 33 1 (bvplus 34 bv33a bv33b)))))
  :hints (("Goal" :use (:instance bitp-of-add-of-mul-of--2-becomes-equal-of-slice
                                  (bv34 (add bv33a bv33b p)))
           :in-theory (enable ;add
                       PFIELD::ADD-BECOMES-BVPLUS-34
                              ))))

(defthm UNSIGNED-BYTE-P-of-add-of-add
  (implies (and (unsigned-byte-p 32 bv32a)
                (unsigned-byte-p 32 bv32b)
                (unsigned-byte-p 32 bv32c)
                )
           (UNSIGNED-BYTE-P 34 (ADD BV32A (ADD BV32B BV32C P) P)))
  :hints (("Goal" :in-theory (enable add))))

(defthmd add-3-hack
  (implies (and (unsigned-byte-p 32 bv32a)
                (unsigned-byte-p 32 bv32b)
                (unsigned-byte-p 32 bv32c)
                (< (expt 2 34) p)
                (posp p))
           (equal (ADD BV32A (ADD BV32B BV32C P) P)
                  (BVPLUS 34 BV32A (BVPLUS 34 BV32B BV32C))))
  :hints (("Goal" :in-theory (enable add))))

(defthm bitp-of-add-of-mul-of--2-becomes-equal-of-slice-extra-2
  (implies (and (syntaxp (quotep k))
                (equal k (- p 2)) ;to make this rule not prime-specific
                (unsigned-byte-p 32 bv32a)
                (unsigned-byte-p 32 bv32b)
                (unsigned-byte-p 32 bv32c)
                (unsigned-byte-p 33 bv33)
                (< (expt 2 34) p)
                (posp p))
           (equal (bitp (add bv32a (add bv32b (add bv32c (mul k bv33 p) p) p) p))
                  (equal bv33 (slice 33 1 (bvplus 34 bv32a (bvplus 34 bv32b bv32c))))))
  :hints (("Goal" :use (:instance bitp-of-add-of-mul-of--2-becomes-equal-of-slice
                                  (bv34 (add bv32a (add bv32b bv32c p) p)))
           :in-theory (enable add-3-hack;add
                              ;acl2::mod-sum-cases
                              ;PFIELD::ADD-BECOMES-BVPLUS-33
                              ))))

;todo: more like this
(defthm pfield::xor-idiom-4-big-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep p)))
                (equal k (+ -2 p)) ;; to avoid making this rule prime-specific
                (bitp x)
                (bitp y)
                (< 2 p)
                (primep p))
           (equal (add (mul k (mul x y p) p)
                       (add x y p)
                       p)
                  (bitxor x y))))

;; todo: for these next rules, it might be better to let other rules solve for the nregated vars (other vars appear twice and can't be solved for) and then rescognize the xor idioms in solved form
;;or get rid of the adds?
(defthm xor-idiom-special
  (implies (and (bitp x)
                (bitp (add y1 (add y2 y3 p) p))
                (FEP z p)
                (posp p)
                (< 2 p)
                (primep p))
           (equal (equal (mul 2 (mul x (add y1 (add y2 y3 p) p) p) p)
                         (add (neg z p) (add y1 (add y2 (add x y3 p) p) p) p))
                  (equal z (bitxor x (add y1 (add y2 y3 p) p)))))
  :hints (("Goal" :use (:instance pfield::xor-idiom-1
                                  (y (add y1 (add y2 y3 p) p))
                                  (z z)
                                  (x x)
                                  (p p))
           :in-theory (disable PFIELD::ADD-OF-NEG-OF-WHEN-BITP)
           )))

(defthm xor-idiom-special-2
  (implies (and (bitp x)
                (bitp (add y1 (add y2 (add y3 y4 p) p) p))
                (fep z p)
                (posp p)
                (< 2 p)
                (primep p))
           (equal (equal (mul 2 (mul x (add y1 (add y2 (add y3 y4 p) p) p) p) p)
                         (add y1 (add y2 (add x (add y3 (add y4 (neg z p) p) p) p) p) p))
                  (equal z (bitxor x (add y1 (add y2 (add y3 y4 p) p) p)))))
  :hints (("Goal" :use (:instance pfield::xor-idiom-1
                                  (y (add y1 (add y2 (add y3 y4 p) p) p))
                                  (z z)
                                  (x x)
                                  (p p))
           :in-theory (disable pfield::add-of-neg-of-when-bitp
                               pfield::equal-of-add-move-negations-bind-free
                               pfield::add-subst-constant-arg1
                               PFIELD::MUL-OF-ADD-ARG2
                               ;; PFIELD::ADD-SUBST-CONSTANT-ARG2
                               ;; PFIELD::NEG-WHEN-CONSTANT-ARG1
                               ;; PFIELD::ADD-OF-CONSTANTS
                               )
           )))

(defthm xor-idiom-special-3
  (implies (and (bitp x)
                (bitp (add y1 (add y2 y3 p) p))
                (FEP z p)
                (posp p)
                (< 2 p)
                (primep p))
           (equal (equal (mul 2 (mul x (add y1 (add y2 y3 p) p) p) p)
                         (add x (add y1 (add y2 (add y3 (neg z p) p) p) p) p))
                  (equal z (bitxor x (add y1 (add y2 y3 p) p)))))
  :hints (("Goal" :use (:instance pfield::xor-idiom-1
                                  (y (add y1 (add y2 y3 p) p))
                                  (z z)
                                  (x x)
                                  (p p))
           :in-theory (disable PFIELD::ADD-OF-NEG-OF-WHEN-BITP
                               PFIELD::MUL-OF-ADD-ARG2
                               pfield::add-subst-constant-arg1
                               PFIELD::NEG-WHEN-CONSTANT-ARG1))))

(defthmd pull-out-inverse-coeff-32
  (implies (and ;(syntaxp (quotep k))
            (equal p *bn-254-group-prime*)
            (posp p))
           (equal (add x (mul *1/2^32* y p) p)
                  (mul *1/2^32* (add (mul (expt 2 32) x p) y p) p))))

(defthmd pull-out-inverse-coeff-32-alt
  (implies (and ;(syntaxp (quotep k))
            (equal p *bn-254-group-prime*)
            (posp p))
           (equal (add (mul *1/2^32* y p) x p)
                  (mul *1/2^32* (add y (mul (expt 2 32) x p) p) p))))

;;todo: oneify goes out to lunch trying to execute pow unless we disable the executable counterparts below
(defthmd pull-out-inverse-coeff-32-extra
  (implies (and ;(syntaxp (quotep k))
            (equal p *bn-254-group-prime*)
            (posp p))
           (equal (add x (add (mul *1/2^32* y p) extra p) p)
                  (add (mul *1/2^32* (add (mul (expt 2 32) x p) y p) p) extra p)))
  :hints (("Goal" :use (:instance pull-out-inverse-coeff-32)
           :in-theory (disable (:e pfield::pow)        ;todo
                               (:e pfield::inv)        ;todo
                               (:e pfield::div)        ;todo
                               ))))

(defthmd add-of-mul-of-65536
  (implies (and (unsigned-byte-p 16 x)
                (unsigned-byte-p 16 y)
                (integerp p)
                (< (expt 2 32) p))
           (equal (add (mul 65536 x p) y p)
                  (bvcat 16 x 16 y)))
  :hints (("Goal" :in-theory (e/d (add mul bvcat acl2::logapp)
                                  (ACL2::BVCAT-EQUAL-REWRITE
                                   ACL2::BVCAT-EQUAL-REWRITE-ALT)))))

(defthmd add-of-mul-of-65536-special
  (implies (and (acl2::axe-bind-free (acl2::bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (equal ysize 16)
                (unsigned-byte-p 16 x)
                (unsigned-byte-p 16 y)
                (integerp p)
                (< (expt 2 32) p))
           (equal (add (mul 65536 x p) y p)
                  (bvcat 16 x 16 y)))
  :hints (("Goal" :use add-of-mul-of-65536)))

;;why needed?
;gen?
(defthmd add-of-mul-of-65536-and-add-extra
  (implies (and (unsigned-byte-p 16 x)
                (unsigned-byte-p 16 y)
                (integerp p)
                (< (expt 2 32) p))
           (equal (add (mul 65536 x p) (add y extra p) p)
                  (add (bvcat 16 x 16 y) extra p)))
  :hints (("Goal" :in-theory (e/d (add mul bvcat acl2::logapp)
                                  (ACL2::BVCAT-EQUAL-REWRITE
                                   ACL2::BVCAT-EQUAL-REWRITE-ALT)))))

;; requires the low bits to a a bvcat of the extact right size
     ;use axe-syntaxp instead to check the size
;need to prevent things from being combined wrong
(defthm add-of-mul-of-65536-and-add-extra-special
  (implies (and (unsigned-byte-p 16 x)
                (integerp p)
                (< (expt 2 32) p))
           (equal (add (mul 65536 x p) (add (bvcat 1 yhigh 15 ylow) extra p) p)
                  (add (bvcat 16 x 16 (bvcat 1 yhigh 15 ylow)) extra p)))
  :hints (("Goal" :use (:instance add-of-mul-of-65536-and-add-extra
                                  (y (bvcat 1 yhigh 15 ylow)))
           :in-theory (disable ACL2::BVCAT-EQUAL-REWRITE-ALT
                               ACL2::BVCAT-EQUAL-REWRITE))))


(defthmd add-of-mul-of-1048576
  (implies (and (equal ysize 20)
                (unsigned-byte-p 12 x)
                (unsigned-byte-p 20 y)
                (integerp p)
                (< (expt 2 32) p))
           (equal (add (mul 1048576 x p) y p)
                  (bvcat 12 x 20 y)))
  :hints (("Goal" :in-theory (e/d (add mul bvcat acl2::logapp)
                                  (ACL2::BVCAT-EQUAL-REWRITE
                                   ACL2::BVCAT-EQUAL-REWRITE-ALT)))))

(defthmd add-of-mul-of-1048576-special
  (implies (and (acl2::axe-bind-free (acl2::bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (equal ysize 20)
                (unsigned-byte-p 12 x)
                (unsigned-byte-p 20 y)
                (integerp p)
                (< (expt 2 32) p))
           (equal (add (mul 1048576 x p) y p)
                  (bvcat 12 x 20 y)))
  :hints (("Goal" :use add-of-mul-of-1048576)))

(defthm add-of-mul-of-1048576-and-add-extra
  (implies (and (unsigned-byte-p 12 x)
                (unsigned-byte-p 20 y)
                (integerp p)
                (< (expt 2 32) p))
           (equal (add (mul 1048576 x p) (add y extra p) p)
                  (add (bvcat 12 x 20 y) extra p)))
  :hints (("Goal" :in-theory (e/d (add mul bvcat acl2::logapp)
                                  (ACL2::BVCAT-EQUAL-REWRITE
                                   ACL2::BVCAT-EQUAL-REWRITE-ALT)))))

(defthm add-of-mul-of-1048576-and-add-extra-special
  (implies (and (acl2::axe-bind-free (acl2::bind-bv-size-axe y 'ysize dag-array) '(ysize))
                (equal ysize 20)
                (unsigned-byte-p 12 x)
                (unsigned-byte-p 20 y)
                (integerp p)
                (< (expt 2 32) p))
           (equal (add (mul 1048576 x p) (add y extra p) p)
                  (add (bvcat 12 x 20 y) extra p)))
  :hints (("Goal" :use add-of-mul-of-1048576-and-add-extra)))


(defthmd add-when-no-overflow-helper
  (IMPLIES (AND (UNSIGNED-BYTE-P 40 BIG1)
                (UNSIGNED-BYTE-P 40 BIG2)
                (UNSIGNED-BYTE-P 33 (ADD BIG1 BIG2 p))
                (< (expt 2 41) p)
                (posp p))
           (EQUAL (ADD BIG1 BIG2 p)
                  (BVPLUS 33 BIG1 BIG2)))
  :hints (("Goal" :in-theory (enable add bvplus UNSIGNED-BYTE-P))))

;; this one has a bvplus in the lhs
(defthmd bitp-of-mul-of-1/2^32-and-add-of-neg-32-two-addends-with-bvplus
  (implies (and (equal p *bn-254-group-prime*)
                ;;(posp p)
                (unsigned-byte-p 32 bv32)
                ;;(< (expt 2 33) p) ;needed?
                (integerp big1)
                (integerp big2)
    ;                (unsigned-byte-p 253 big) ;less than the prime
                (unsigned-byte-p 40 big1) ;gen?
                (unsigned-byte-p 40 big2) ;gen?
                )
           (equal (bitp (mul *1/2^32* (add big1 (add (neg bv32 p) big2 p) p) p))
                  (and (equal (bvchop 32 (bvplus 33 big1 big2))
                              bv32)
                       ;; everything but the carry and the low bits is 0:
                       (unsigned-byte-p 33 (add big1 big2 *bn-254-group-prime*)))))
  :hints (("Goal" :use (:instance bitp-of-mul-of-1/2^32-and-add-of-neg-32
                                  (big (add big1 big2 *bn-254-group-prime*)))
           :in-theory (e/d (add-when-no-overflow-helper) ((:e pfield::pow) ;todo
                                                          (:e pfield::inv) ;todo
                                                          (:e pfield::div) ;todo
                                                          ))))
  )

(defthmd bitp-of-mul-of-1/2^32-and-add-of-neg-32-two-addends
  (implies (and (equal p *bn-254-group-prime*)
                ;;(posp p)
                (unsigned-byte-p 32 bv32)
                ;;(< (expt 2 33) p) ;needed?
                (integerp big1)
                (integerp big2)
    ;                (unsigned-byte-p 253 big) ;less than the prime
                )
           (equal (bitp (mul *1/2^32* (add big1 (add (neg bv32 p) big2 p) p) p))
                  (and (equal (bvchop 32 (add big1 big2 *bn-254-group-prime*))
                              bv32)
                       ;; everything but the carry and the low bits is 0:
                       (unsigned-byte-p 33 (add big1 big2 *bn-254-group-prime*)))))
  :hints (("Goal" :use (:instance bitp-of-mul-of-1/2^32-and-add-of-neg-32
                                  (big (add big1 big2 *bn-254-group-prime*)))
           :in-theory (e/d (                    ;add-when-no-overflow-helper
                            ) ((:e pfield::pow) ;todo
                            (:e pfield::inv)    ;todo
                            (:e pfield::div)    ;todo
                            )))))

(defthm bvchop-32-of-add-when-unsigned-byte-p-33
  (implies (and (unsigned-byte-p 33 (add x y p))
                (unsigned-byte-p 40 x) ;gen?
                (unsigned-byte-p 40 y) ;gen?
                (< (expt 2 41) p)
                (integerp p))
           (equal (bvchop 32 (add x y p))
                  (bvplus 32 x y)))
  :hints (("Goal" :in-theory (enable add bvplus UNSIGNED-BYTE-P))))

(defthmd bvplus-34-tighten-to-33
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (bvplus 34 x y)
                  (bvplus 33 x y)))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthmd bvplus-35-tighten-to-34
  (implies (and (unsigned-byte-p 33 x)
                (unsigned-byte-p 33 y))
           (equal (bvplus 35 x y)
                  (bvplus 34 x y)))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm tighten-helper
  (implies (and (unsigned-byte-p 32 x0)
                (unsigned-byte-p 32 x1)
                (unsigned-byte-p 32 x2)
                (unsigned-byte-p 32 x3))
           (equal (BVPLUS 35 x0 (BVPLUS 34 X1 (BVPLUS 33 x2 x3)))
                  (BVPLUS 34 x0 (BVPLUS 34 X1 (BVPLUS 33 x2 x3)))))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm add-of-+-same-arg1-arg1
  (implies (posp p)
           (equal (add (+ p x) y p)
                  (add x y p)))
  :hints (("Goal" :in-theory (enable add))))

;improve the rhs?
(defthm bitp-of-mul-of-1/2^32-and-add-of-neg-32-5-addends
  (implies (and (equal p *bn-254-group-prime*)
                (bitp bita)
                (bitp bitb)
                (bitp bitc)
                (unsigned-byte-p 32 bv32)
                ;;gen these?
                (unsigned-byte-p 32 inv0)
                (unsigned-byte-p 32 inv4)
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y)
                (unsigned-byte-p 32 rot))
           (equal (BITP (MUL *1/2^32*
                             (ADD (MUL '4294967296 (NEG bita p) p)
                                  (ADD (NEG bv32 p)
                                       (ADD inv0
                                            (ADD inv4
                                                 (ADD x
                                                      (ADD y
                                                           (ADD (MUL *-2^33* bitb p)
                                                                (ADD rot
                                                                     (MUL *-2^33* bitc p) p) p) p) p) p) p) p) p) p))
                  (and (equal (bvchop 32 (ADD (MUL '4294967296 (NEG bita p) p)
                                              (ADD inv0
                                                   (ADD inv4
                                                        (ADD x
                                                             (ADD y
                                                                  (ADD (MUL *-2^33* bitb p)
                                                                       (ADD rot
                                                                            (MUL *-2^33* bitc p) p) p) p) p) p) p) p))
                              bv32)
                       (unsigned-byte-p 33 (ADD (MUL '4294967296 (NEG bita p) p)
                                                (ADD inv0
                                                     (ADD inv4
                                                          (ADD x
                                                               (ADD y
                                                                    (ADD (MUL *-2^33* bitb p)
                                                                         (ADD rot
                                                                              (MUL *-2^33* bitc p) p) p) p) p) p) p) p)))))
  :hints (("Goal" :use (:instance bitp-of-mul-of-1/2^32-and-add-of-neg-32
                                  (big (ADD (MUL '4294967296 (NEG bita p) p)
                                            (ADD inv0
                                                 (ADD inv4
                                                      (ADD x
                                                           (ADD y
                                                                (ADD (MUL *-2^33* bitb p)
                                                                     (ADD rot
                                                                          (MUL *-2^33* bitc p) p) p) p) p) p) p) p)))
           :in-theory (disable ACL2::BVCAT-EQUAL-REWRITE
                               ACL2::BVCAT-EQUAL-REWRITE-ALT))))


;gen the -32 version
(DEFTHM EQUAL-OF-LOGTAIL-AND-CONSTANT-33
  (IMPLIES (AND (SYNTAXP (QUOTEP K))
                (INTEGERP X)
                (INTEGERP K))
           (EQUAL (EQUAL (ACL2::LOGTAIL 33 X) K)
                  (AND (<= (* (EXPT 2 33) K) X)
                       (< X (* (EXPT 2 33) (+ 1 K))))))
  :HINTS (("Goal" :IN-THEORY (ENABLE ACL2::LOGTAIL))))


;;slow
(defthmd add-helper-bv35
  (implies (and (equal p *bn-254-group-prime*)
                ;; free var avoid loop?
                (unsigned-byte-p free (add (mul *-2^33* bitc p)
                                           (add (mul *-2^33* bitb p)
                                                (add (mul *-2^32* bita p)
                                                     bv35 p)
                                                p)
                                           p))
                (equal free 33)
                (unsigned-byte-p 35 bv35)
                (<= bv35 (+ (expt 2 34) (expt 2 32))) ;101...
                (bitp bita)
                (bitp bitb)
                (bitp bitc)
                ;; (equal 1 (getbit 34 bv35)) ;drop!
                ;; (equal 0 (getbit 33 bv35)) ;drop!
                ;; (equal 0 (getbit 32 bv35)) ;drop!
                ;; (equal 1 bita) ;drop!
                ;; (equal 0 bitb) ;drop!
                ;; (equal 1 bitc) ;drop!
                (posp p))
           (equal (add (mul *-2^33* bitc p)
                       (add (mul *-2^33* bitb p)
                            (add (mul *-2^32* bita p)
                                 bv35 p)
                            p)
                       p)
                  ;; was (bvchop 33 (add (mul *-2^32* bita p) bv35 p))
                  (if (equal 1 bita)
                      (bvchop 33 (+ (- (expt 2 32)) bv35))
                    (bvchop 33 bv35))))
  :otf-flg t
  :hints (("Goal"
           :cases ((equal 0 (SLICE 34 33 BV35))
                   (equal 1 (SLICE 34 33 BV35))
                   (equal 2 (SLICE 34 33 BV35)))
           :use (:instance acl2::split-bv
                           (y bv35)
                           (n 35)
                           (m 33))
           :in-theory (enable add mul bvcat acl2::logapp ACL2::MOD-SUM-CASES slice ACL2::BVCHOP-OF-SUM-CASES
                              EQUAL-OF-LOGTAIL-AND-CONSTANT
                              EQUAL-OF-LOGTAIL-AND-CONSTANT-33))))


(defthm bound-helper
  (implies (and (unsigned-byte-p 32 inv0)
                (unsigned-byte-p 32 inv4)
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y)
                (unsigned-byte-p 32 rot))
           (not (< 21474836480
                   (ADD INV0
                        (ADD inv4
                             (add y (add rot x *BN-254-GROUP-PRIME*) *BN-254-GROUP-PRIME*)
                             *BN-254-GROUP-PRIME*)
                        *BN-254-GROUP-PRIME*))))
  :hints (("Goal" :in-theory (enable add bvplus))))

(defthm usb-helper
  (implies (and (unsigned-byte-p 32 inv0)
                (unsigned-byte-p 32 inv4)
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y)
                (unsigned-byte-p 32 rot))
           (unsigned-byte-p 35
                            (ADD INV0
                                 (ADD inv4
                                      (add y (add rot x *BN-254-GROUP-PRIME*) *BN-254-GROUP-PRIME*)
                                      *BN-254-GROUP-PRIME*)
                                 *BN-254-GROUP-PRIME*)))
  :hints (("Goal" :in-theory (enable add bvplus))))

(defthm add-helper-bv35-for-use
  (implies (and (unsigned-byte-p free (ADD (MUL '4294967296 (NEG bita p) p)
                                           (ADD inv0
                                                (ADD inv4
                                                     (ADD x
                                                          (ADD y
                                                               (ADD (MUL *-2^33* bitb p)
                                                                    (ADD rot
                                                                         (MUL *-2^33* bitc p) p) p) p) p) p) p) p))
                (equal free 33)
                (equal p *bn-254-group-prime*)
                (bitp bita)
                (bitp bitb)
                (bitp bitc)
                (unsigned-byte-p 32 inv0)
                (unsigned-byte-p 32 inv4)
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y)
                (unsigned-byte-p 32 rot))
           (equal (ADD (MUL '4294967296 (NEG bita p) p)
                       (ADD inv0
                            (ADD inv4
                                 (ADD x
                                      (ADD y
                                           (ADD (MUL *-2^33* bitb p)
                                                (ADD rot
                                                     (MUL *-2^33* bitc p) p) p) p) p) p) p) p)
                  (if (equal 1 bita)
                      (bvchop 33 (+ (- (expt 2 32))
                                    (ADD inv0
                                         (ADD inv4
                                              (ADD x
                                                   (ADD y
                                                        rot p) p) p) p)))
                    (bvchop 33 (ADD inv0
                                    (ADD inv4
                                         (ADD x
                                              (ADD y
                                                   rot p) p) p) p)))))
  :hints (("Goal" ;:in-theory (enable PFIELD::ADD-BECOMES-BVPLUS-34)
           :in-theory (disable)
           :use (:instance add-helper-bv35
                                  (bv35 (ADD inv0
                                             (ADD inv4
                                                  (ADD x
                                                       (ADD y
                                                            rot p) p) p) p))))))

(defthm add-helper-bv35-for-use-new
  (implies (and (unsigned-byte-p free (ADD (MUL '4294967296 (NEG bita p) p)
                                           (ADD inv0
                                                (ADD bv34
                                                     (ADD (MUL *-2^33* bitb p)
                                                          (ADD rot
                                                               (MUL *-2^33* bitc p) p) p) p) p) p))
                (equal free 33)
                (equal p *bn-254-group-prime*)
                (< bv34 12884901888)
                (bitp bita)
                (bitp bitb)
                (bitp bitc)
                (unsigned-byte-p 32 inv0)
                (unsigned-byte-p 34 bv34)
                (unsigned-byte-p 32 rot))
           (equal (ADD (MUL '4294967296 (NEG bita p) p)
                       (ADD inv0
                            (ADD bv34
                                 (ADD (MUL *-2^33* bitb p)
                                      (ADD rot
                                           (MUL *-2^33* bitc p) p)
                                      p) p) p) p)
                  (if (equal 1 bita)
                      (bvchop 33 (+ (- (expt 2 32))
                                    (ADD inv0
                                         (ADD bv34
                                              rot p) p)))
                    (bvchop 33 (ADD inv0
                                    (ADD bv34
                                         rot p) p)))))
  :hints (("Goal" ;:in-theory (enable PFIELD::ADD-BECOMES-BVPLUS-34)
           :in-theory (e/d (add) ((:e div)))
           :use (:instance add-helper-bv35
                           (bv35 (ADD inv0
                                      (ADD bv34
                                           rot p) p))))))


(defthm add-helper-bv33-for-use
  (implies (and (unsigned-byte-p free (add (mul '4294967296 (neg bit p) p) (add x (add y z p) p) p))
                (equal free 33)
                (equal p *bn-254-group-prime*)
                (bitp bit)
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y)
                (unsigned-byte-p 32 z))
           (equal (add (mul '4294967296 (neg bit p) p) (add x (add y z p) p) p)
                  (if (equal 1 bit)
                      (bvchop 33 (+ (- (expt 2 32)) (add x (add y z p) p)))
                    (bvchop 33 (add x (add y z p) p)))))
  :hints (("Goal" :in-theory (enable add ACL2::BVCHOP-OF-SUM-CASES
                                     acl2::mod-sum-cases))))

;;slow
(defthm add-helper-bv33-for-use-bv-version
  (implies (and (unsigned-byte-p free (add (mul '4294967296 (neg bit p) p) (bvplus 34 x (bvplus 33 y z)) p))
                (equal free 33)
                (equal p *bn-254-group-prime*)
                (bitp bit)
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y)
                (unsigned-byte-p 32 z))
           (equal (add (mul '4294967296 (neg bit p) p) (bvplus 34 x (bvplus 33 y z)) p)
                  (if (equal 1 bit)
                      (bvchop 33 (+ (- (expt 2 32)) (bvplus 34 x (bvplus 33 y z))))
                    (bvchop 33 (bvplus 34 x (bvplus 33 y z))))))
  :hints (("Goal" :in-theory (enable add ACL2::BVCHOP-OF-SUM-CASES
                                     bvplus
                                     acl2::mod-sum-cases))))

(defthm add-helper-bv35-for-use-special-1
  (implies (and (unsigned-byte-p free (ADD *-2^32*
                                           (ADD inv0
                                                (ADD inv4
                                                     (ADD x
                                                          (ADD y
                                                               (ADD (MUL *-2^33* bitb p)
                                                                    (ADD rot
                                                                         (MUL *-2^33* bitc p) p) p) p) p) p) p) p))
                (equal free 33)
                (equal p *bn-254-group-prime*)
                (bitp bitb)
                (bitp bitc)
                (unsigned-byte-p 32 inv0)
                (unsigned-byte-p 32 inv4)
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y)
                (unsigned-byte-p 32 rot))
           (equal (ADD *-2^32*
                       (ADD inv0
                            (ADD inv4
                                 (ADD x
                                      (ADD y
                                           (ADD (MUL *-2^33* bitb p)
                                                (ADD rot
                                                     (MUL *-2^33* bitc p) p) p) p) p) p) p) p)
                  (bvchop 33 (+ (- (expt 2 32))
                                (ADD inv0
                                     (ADD inv4
                                          (ADD x
                                               (ADD y
                                                    rot p) p) p) p)))))
  :hints (("Goal" :use (:instance add-helper-bv35-for-use
                                  (bita 1)))))


(defthm add-of-neg-of-bvplus-lemma
  (implies (and (unsigned-byte-p 32 inv8)
                (unsigned-byte-p 32 xor32)
                (unsigned-byte-p 32 extra)
                (posp p))
           (equal (add (neg (bvplus 33 inv8 xor32) p) (bvplus 34 inv8 (bvplus '33 xor32 extra)) p)
                  (mod extra p)))
  :hints (("Goal" :in-theory (enable add neg bvplus acl2::bvchop-of-sum-cases acl2::mod-sum-cases))))

;;slow
(defthm mod-of-sum-of-mod-4
  (implies (and (Integerp x)
                (Integerp y)
                (Integerp z)
                (Integerp w)
                (posp p))
           (equal (MOD (+ x y z (MOD w P)) P)
                  (MOD (+ x y z w) P)))
  :hints (("Goal" :in-theory (enable acl2::mod-sum-cases))))

(defthm add-of-neg-of-bvplus-lemma2
  (implies (and (unsigned-byte-p 32 inv0)
                (unsigned-byte-p 32 inv4)
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 extra)
                (posp p))
           (equal (add (neg (bvplus 34 inv0 (bvplus 33 inv4 x)) p)
                       (bvplus 35 inv0 (bvplus '34 inv4 (bvplus 33 x extra)))
                       p)
                  (mod extra p)))
  :hints (("Goal" :in-theory (enable add neg bvplus acl2::bvchop-of-sum-cases))))

(defthm add-of-neg-of-bvplus-lemma3
  (implies (and (unsigned-byte-p 32 inv8)
                (unsigned-byte-p 32 xor)
                (unsigned-byte-p 32 extra)
                (posp p))
           (equal (ADD (BVPLUS '34 inv8 (BVPLUS '33 xor extra)) (NEG (BVPLUS '33 inv8 xor) p) p)
                  (mod extra p)))
  :hints (("Goal" :in-theory (enable add neg bvplus acl2::bvchop-of-sum-cases))))

(defthm add-of-neg-of-bvplus-lemma4
  (implies (and (unsigned-byte-p 32 inv0)
                (unsigned-byte-p 32 inv4)
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 extra)
                (posp p))
           (equal (ADD inv0
                       (ADD (BVPLUS '34 inv4 (BVPLUS '33 x extra))
                            (NEG (BVPLUS '34 inv0 (BVPLUS '33 inv4 x)) p) p) p)
                  (mod extra p)))
  :hints (("Goal" :in-theory (enable add neg bvplus acl2::bvchop-of-sum-cases))))

;move
(defthm mod-of-bitxor
  (implies (and (<= 2 p)
                (integerp p))
           (equal (mod (bitxor x y) p)
                  (bitxor x y))))

(in-theory (disable ACL2::BVCHOP-1-BECOMES-GETBIT ;yuck
                    ACL2::SLICE-BECOMES-GETBIT; yuck
                    ))

;gen
(defthm *-of-2-and-slice-of-1
  (equal (* 2 (slice 33 1 x))
         (- (bvchop 34 x) (getbit 0 x)))
  :hints (("Goal" :use (:instance acl2::split-bv (y (bvchop 34 x)) (n 34) (m 1))
           :in-theory (enable bvcat acl2::logapp getbit))))

(defthm mul-of-2-and-slice-of-1
  (implies (and (< (expt 2 34) p)
                (integerp p))
           (equal (mul 2 (slice 33 1 x) p)
                  (- (bvchop 34 x) (getbit 0 x))))
  :hints (("Goal" :in-theory (enable mul))))

;; Does not require p to be constant
(DEFTHMd R1CS::MUL-NORMALIZE-CONSTANT-ARG1-gen
  (IMPLIES (AND (SYNTAXP (AND (QUOTEP X)
                              ;(QUOTEP P)
                              ))
                (< (FLOOR P 2) X))
           (EQUAL (MUL X Y P)
                  (MUL (- (neg X P)) Y P)))
  :HINTS
  (("Goal" :IN-THEORY (ENABLE MUL neg ACL2::MOD-SUM-CASES))))

(defthmd mul-of--2-becomes-neg-of-mul-of-2
  (equal (mul -2 x p)
         (neg (mul 2 x p) p))
  :hints (("Goal" :in-theory (enable neg mul))))

(defthm mul-of--2-and-slice-of-1
  (implies (and (< (expt 2 34) p)
                (integerp p))
           (equal (mul -2 (slice 33 1 x) p)
                  (mod (- (getbit 0 x) (bvchop 34 x)) p)))
  :hints (("Goal" :in-theory (e/d (mul-of--2-becomes-neg-of-mul-of-2
                                   neg)
                                  (ACL2::BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))


;quite specific
(defthm add-of-mul-of--2-helper
  (implies (and (equal sum (slice 33 1 bv34))
                (unsigned-byte-p 34 bv34)
                (equal p *bn-254-group-prime*) ;gen
                ;(< (expt 2 41) p)
                ;(integerp p)
                )
           (equal (add bv34 (mul *-2^1* sum p) p)
                  (getbit 0 bv34)))
  :hints (("Goal" :in-theory (e/d (add R1CS::MUL-NORMALIZE-CONSTANT-ARG1-gen
                                       )
                                  (;acl2::getbit-0-of-bvplus
                                   )))))

;very specific
;gets rid of SUM
;gen the (bvplus 33 inv4 x)?
(defthm add-of-bvplus-helper-when-equal-slice-34
 (implies (and (equal sum (slice 33 1 (bvplus 34 inv0 (bvplus 33 inv4 x))))
               ;(unsigned-byte-p 33 (add x y p))
               ;(unsigned-byte-p 40 x) ;gen?
               ;(unsigned-byte-p 40 y) ;gen?
               (equal p *bn-254-group-prime*) ;gen
               ;(< (expt 2 41) p)
               ;(integerp p)
               )
          (equal (add (bvplus 34 inv0 (bvplus 33 inv4 x)) (mul *-2^1* sum p) p)
                 (getbit 0 (bvplus 34 inv0 (bvplus 33 inv4 x)))))
 :hints (("Goal" :use (:instance add-of-mul-of--2-helper (bv34 (bvplus 34 inv0 (bvplus 33 inv4 x))))
          :in-theory (disable add-of-mul-of--2-helper))))

(defthm add-of-bvplus-helper-when-equal-slice-34-gen
 (implies (and (equal sum (slice 33 1 (bvplus 34 inv0 y)))
               ;(unsigned-byte-p 33 (add x y p))
               ;(unsigned-byte-p 40 x) ;gen?
               ;(unsigned-byte-p 40 y) ;gen?
               (equal p *bn-254-group-prime*) ;gen
               ;(< (expt 2 41) p)
               ;(integerp p)
               )
          (equal (add (bvplus 34 inv0 y) (mul *-2^1* sum p) p)
                 (getbit 0 (bvplus 34 inv0 y))))
 :hints (("Goal" :use (:instance add-of-mul-of--2-helper (bv34 (bvplus 34 inv0 y)))
          :in-theory (disable add-of-mul-of--2-helper))))

(defthm add-of-bvplus-helper-when-equal-slice-33
 (implies (and (equal sum (slice 33 1 (bvplus 33 inv0 y)))
               ;(unsigned-byte-p 33 (add x y p))
               ;(unsigned-byte-p 40 x) ;gen?
               ;(unsigned-byte-p 40 y) ;gen?
               (equal p *bn-254-group-prime*) ;gen
               ;(< (expt 2 41) p)
               ;(integerp p)
               )
          (equal (add (bvplus 33 inv0 y) (mul *-2^1* sum p) p)
                 (getbit 0 (bvplus 33 inv0 y))))
 :hints (("Goal" :use (:instance add-of-mul-of--2-helper (bv34 (bvplus 33 inv0 y)))
          :in-theory (disable add-of-mul-of--2-helper))))

;gets rid of a mul
;may subsume the ones above
(defthm mul-of--2-when-equal-of-slice
  (implies (and (equal x (slice 33 1 free))
                (equal p *bn-254-group-prime*) ;gen
                )
           (equal (mul *-2^1* x p)
                  ;;(neg (bvcat 33 (slice 33 1 free) 1 0) p)
                  ;;(mod (acl2::bvminus 34 (GETBIT 0 FREE) (BVCHOP 34 FREE)) p)
                  (add (GETBIT 0 FREE) (neg (BVCHOP 34 FREE) p) p)
                  ))
  :hints (("Goal" :in-theory (e/d (add R1CS::MUL-NORMALIZE-CONSTANT-ARG1-gen
                                       )
                                  (;acl2::getbit-0-of-bvplus
                                   )))))

(defthmd bvchop-of-if
  (equal (bvchop size (if test x y))
         (if test
             (bvchop size x)
           (bvchop size y))))

;move
;; The bvplus 1 in the LHS can then be turned into a bitxor
(defthm bitxor-of-bvplus-tighten-arg1
  (implies (and (< 1 size)
                (integerp size))
           (equal (bitxor (bvplus size x y) z)
                  (bitxor (bvplus 1 x y) z)))
  :hints (("Goal" :in-theory (e/d (bitxor BVXOR) (ACL2::BVXOR-1-BECOMES-BITXOR)))))

;move
;; The bvplus 1 in the LHS can then be turned into a bitxor
(defthm bitxor-of-bvplus-tighten-arg2
  (implies (and (< 1 size)
                (integerp size))
           (equal (bitxor z (bvplus size x y))
                  (bitxor z (bvplus 1 x y))))
  :hints (("Goal" :in-theory (e/d (bitxor BVXOR) (ACL2::BVXOR-1-BECOMES-BITXOR)))))

(defthm add-of-mul-of-256-becomes-bvcat
  (implies (and (unsigned-byte-p 8 x)
                (unsigned-byte-p 24 y)
                (integerp p)
                (< (expt 2 32) p)
                )
           (equal (add x (add (mul 256 y p) z p) p)
                  (add (bvcat 24 y 8 x)
                       z
                       p)))
  :hints (("Goal" :in-theory (e/d (add mul
                                     acl2::bvchop-of-sum-cases
                                     acl2::slice-of-sum-cases
                                     bvcat acl2::logapp)
                                  (ACL2::BVCAT-EQUAL-REWRITE
                                   ACL2::BVCAT-EQUAL-REWRITE-ALT)))))

(defthm combine-special ;todo: why needed?
  (implies (and (bitp bit)
                (unsigned-byte-p 15 bv15)
                (unsigned-byte-p 16 bv16)
                (equal p *baby-jubjub-prime*))
           (equal (add (mul *2^16* bit p) (add (mul *2^17* bv15 p) bv16 p) p)
                  (bvcat 15 bv15
                         17 (bvcat 1 bit 16 bv16))))
  :hints (("Goal" :in-theory (enable add mul
                                     ACL2::BVCHOP-OF-SUM-CASES ;todo: prove without
                                     ACL2::SLICE-OF-SUM-CASES
                                     ))))
