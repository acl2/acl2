; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "support")
(include-book "../samples/sha3-component-samples")

;; (aleo::p1cs (aleovm::keccak256-round-chi--constraints))

;; todo: are there any unnecesary constraints and vars?

(defconst *chi-input-vars*
    (acl2::make-var-names '|w| 1600))

;; The output vars represent the state array (25 lanes of 64 bits each).  Each
;; lane seems to be contiguous, and the lanes seem to be separated in the
;; variable numbering by 128.
(defconst *chi-output-vars*
  (append (acl2::make-var-names-from '|w| 1664 64)
          (acl2::make-var-names-from '|w| 1792 64)
          (acl2::make-var-names-from '|w| 1920 64)
          (acl2::make-var-names-from '|w| 2048 64)
          (acl2::make-var-names-from '|w| 2176 64)

          (acl2::make-var-names-from '|w| 2304 64)
          (acl2::make-var-names-from '|w| 2432 64)
          (acl2::make-var-names-from '|w| 2560 64)
          (acl2::make-var-names-from '|w| 2688 64)
          (acl2::make-var-names-from '|w| 2816 64)

          (acl2::make-var-names-from '|w| 2944 64)
          (acl2::make-var-names-from '|w| 3072 64)
          (acl2::make-var-names-from '|w| 3200 64)
          (acl2::make-var-names-from '|w| 3328 64)
          (acl2::make-var-names-from '|w| 3456 64)

          (acl2::make-var-names-from '|w| 3584 64)
          (acl2::make-var-names-from '|w| 3712 64)
          (acl2::make-var-names-from '|w| 3840 64)
          (acl2::make-var-names-from '|w| 3968 64)
          (acl2::make-var-names-from '|w| 4096 64)

          (acl2::make-var-names-from '|w| 4224 64)
          (acl2::make-var-names-from '|w| 4352 64)
          (acl2::make-var-names-from '|w| 4480 64)
          (acl2::make-var-names-from '|w| 4608 64)
          (acl2::make-var-names-from '|w| 4736 64)))

(set-rewrite-stack-limit 10000)

(make-event
  `(defun spec-chi (,@*chi-input-vars* ,@*chi-output-vars*)
     (declare (xargs ;; :guard (and ,@(acl2::make-bitp-claims *chi-input-vars*)
                     ;;             ,@(acl2::make-bitp-claims *chi-output-vars*)
                     ;;             ) ; todo: put back
                     :verify-guards nil ; todo: too slow!
                     :guard-hints (("Goal" :do-not '(preprocess) :in-theory (e/d (acl2::unsigned-byte-p-becomes-bitp)
                                                                                 (bitp acl2::bitp-becomes-unsigned-byte-p))))))
     (equal (sha3::chi (sha3::bits-to-state-array (list ,@*chi-input-vars*) 64)
                       64)
            (sha3::bits-to-state-array (list ,@*chi-output-vars*) 64))))


(local
  (r1cs::lift-r1cs *keccak256-round-chi*
                   (r1cs-constraint-list-vars (aleovm::keccak256-round-chi--constraints))
                   ;; todo: only include the constraints that we need:
                   ;; ex: of the 4800 constraints, we may only need the first 1920 and the last 1600?
                   (aleovm::keccak256-round-chi--constraints)
                   ;; (append (take 1920 (aleovm::keccak256-round-chi--constraints))
                   ;;         (take 1600 (nthcdr 3200 (aleovm::keccak256-round-chi--constraints))))
                   8444461749428370424248824938781546531375899335154063827935233455917409239041
                   :remove-rules '(pfield::neg-of-mul-when-constant ;makes it harder to move terms to the other side?
                                   pfield::equal-of-add-of-add-of-neg-arg2-arg2 ;for now, to try to combine more stuff
                                   PFIELD::ADD-COMMUTATIVE-2-AXE
                                   PFIELD::ADD-COMMUTATIVE-axe
                                   )
                   :extra-rules '(bitp-idiom
                                  pfield::introduce-bitp-alt-2-alt
                                  pfield::introduce-bitp-alt-2
                                  primes::primep-of-bls12-377-scalar-field-prime-constant
                                  ;; acl2::bool-fix-when-booleanp
                                  acl2::booleanp-of-bitp
                                  ;pfield::mul-of-2
                                  bitxor-idiom-1
                                  bitxor-idiom-2
                                  bitxor-idiom-1-alt
                                  bitxor-idiom-2-alt
                                  bitnot-idiom-1)))

;; Assumes:
;; 1. The R1CS holds
;; 2. x0 is the constant 1
;; 3. All the vars are field elements
;; Proves that the spec (spec-chi) holds.
(acl2::prove-implication-with-r1cs-prover
  (acl2::make-conjunction-dag! (acl2::make-term-into-dag-basic! '(equal |x0| '1) ; x0 is always equal to 1 !
                                                                nil)
                               (acl2::make-conjunction-dag! (acl2::make-term-into-dag-basic!
                                                              ;; todo: tool could translate the fe-listp assumption
                                                              (pfield::gen-fe-listp-assumption (acl2::dag-vars *keccak256-round-chi*)
                                                                                               ''8444461749428370424248824938781546531375899335154063827935233455917409239041)
                                                              nil)
                                                            *keccak256-round-chi*))
  `(spec-chi ,@*chi-input-vars* ,@*chi-output-vars*)
;  :monitor '(bitxor-idiom-1)
  :no-splitp t
 ;; todo: the tool should build the alist:
 ;; todo: better to use a custom instantiate-hyp function:
  ;; some of these may be needed only for ground proofs:
  :interpreted-function-alist
  (acl2::make-interpreted-function-alist
    '(neg pfield::add pfield::pos-fix BVCAT acl2::logapp ash ACL2::EXPT2$INLINE ACL2::LOGHEAD$INLINE ACL2::IMOD$INLINE INTEGER-RANGE-P POWER-OF-2P fep unsigned-byte-p getbit slice ACL2::LOGTAIL$INLINE ACL2::IFLOOR$INLINE bitnot sub bvnot lognot bitxor POWER-OF-2P ACL2::BVSHR ACL2::BVSHL TRUE-LIST-FIX
      acl2::booland)
    (w state))
  :extra-global-rules *global-proof-rules*
  :rule-lists '(;;First, solve and subsitute using all the bitxor and bitnot constraints.  Requires several rounds of substitution:
                (;; These introduce BITXOR (not all of these are used):
                 pfield::bitxor-constraint-intro
                 pfield::bitxor-constraint-intro-alt
                 pfield::bitxor-constraint-intro-b
                 pfield::bitxor-constraint-intro-b-alt
                 pfield::bitxor-constraint-intro-2
                 pfield::bitxor-constraint-intro-2-alt
                 pfield::bitxor-constraint-intro-2b
                 pfield::bitxor-constraint-intro-2b-alt
                ;; These 2 introduce BITNOT (e.g., for output vars):
                 pfield::equal-of-1-and-add-when-bitp-arg1
                 pfield::equal-of-1-and-add-when-bitp-arg2
                 bitxor-idiom-1
                 bitxor-idiom-2
                 bitxor-idiom-1-alt
                 bitxor-idiom-2-alt
                 bitnot-idiom-1
                 bitand-idiom-1
                 )
                ;; open the spec:
                (spec-chi
                  sha3::chi
                  sha3::chi-planes-base sha3::chi-planes-unroll
                  sha3::chi-lanes-base sha3::chi-lanes-unroll
                  sha3::chi-lane-base sha3::chi-lane-unroll
                  acl2::bitxor$ ; todo: add these 2 to a basic rule set
                  acl2::bitand$
                  sha3::a sha3::nth-lane sha3::nth-plane sha3::nth-bit
                  sha3::bit-string-to-plane
                  sha3::bits-to-state-array
                  sha3::map-bit-string-to-plane-base
                  sha3::map-bit-string-to-plane-unroll
                  acl2::group-base acl2::group-unroll
                  acl2::atom
                  acl2::consp-of-cons
                  acl2::nthcdr-of-cons
                  acl2::firstn-base-1 acl2::firstn-base-2 acl2::firstn-unroll
                  acl2::endp
                  acl2::car-cons acl2::cdr-cons
                  acl2::nth-of-cons-constant-version
                  acl2::equal-of-cons-and-cons
                  acl2::bitxor-commutative-2-increasing-axe
                  acl2::bitxor-associative
                  acl2::bitxor-of-1-becomes-bitnot-arg2)))
