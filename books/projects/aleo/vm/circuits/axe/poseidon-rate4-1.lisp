; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "../samples/poseidon-samples")
(include-book "poseidon-support")
(include-book "projects/poseidon/rate-4-alpha-17" :dir :system) ;spec

;; (aleo::p1cs (aleovm::psd-rate4-1-wef--constraints))

;; Lift the R1CS into logic:
(local
  (r1cs::lift-r1cs *psd-rate4-1*
                   (r1cs-constraint-list-vars (aleovm::psd-rate4-1-wef--constraints))
                   (aleovm::psd-rate4-1-wef--constraints)
                   8444461749428370424248824938781546531375899335154063827935233455917409239041
                   :remove-rules '(pfield::neg-of-mul-when-constant ;makes it harder to move terms to the other side?
                                   pfield::equal-of-add-of-add-of-neg-arg2-arg2 ;for now, to try to combine more stuff
                                   pfield::add-commutative-2-axe
                                   pfield::add-commutative-axe)
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

(defun spec (in out)
  (declare (xargs :guard (and (fep in primes::*bls12-377-scalar-field-prime*)
                              (fep out primes::*bls12-377-scalar-field-prime*))))
  (equal out
         (poseidon::hash4 (list in))))

;; Assumes:
;; 1. The R1CS holds
;; 2. w336 is the constant 1
;; 3. All the vars are field elements
;; Proves that the spec holds.
;; (acl2::prove-implication-with-r1cs-prover
;;   (acl2::make-conjunction-dag! (acl2::make-term-into-dag-basic! '(equal |w336| '1) nil)
;;   (acl2::make-conjunction-dag! (acl2::make-term-into-dag-basic!
;;                                  ;; todo: tool could translate the fe-listp assumption
;;                                  (pfield::gen-fe-listp-assumption (acl2::dag-vars *psd-rate4-1*)
;;                                                                   ''8444461749428370424248824938781546531375899335154063827935233455917409239041)
;;                                  nil)
;;                                *psd-rate4-1*))
;;     `(spec |w0| |w337|)
;;     :no-splitp t
;;     :no-print-fns '(fe-listp)
;;     ;; todo: the tool should build the alist:
;;     ;; todo: better to use a custom instantiate-hyp function:
;;     ;; some of these may be needed only for ground proofs:
;;     :interpreted-function-alist
;;     (acl2::make-interpreted-function-alist
;;       '(neg pfield::add pfield::pos-fix BVCAT acl2::logapp ash ACL2::EXPT2$INLINE ACL2::LOGHEAD$INLINE ACL2::IMOD$INLINE INTEGER-RANGE-P POWER-OF-2P fep unsigned-byte-p getbit slice ACL2::LOGTAIL$INLINE ACL2::IFLOOR$INLINE bitnot sub bvnot lognot bitxor POWER-OF-2P ACL2::BVSHR ACL2::BVSHL TRUE-LIST-FIX
;;         acl2::booland
;;         fe-listp)
;;       (w state))
;;   :extra-global-rules (append '(pfield::integerp-of-pow) *global-proof-rules*)
;;   :count-hits t
;; ;  :print t
;;   :rule-lists '(;;First, solve and subsitute using all the bitxor and bitnot constraints.  Requires several rounds of substitution:
;;                 (;; These introduce BITXOR (not all of these are used):
;;                  pfield::bitxor-constraint-intro
;;                  pfield::bitxor-constraint-intro-alt
;;                  pfield::bitxor-constraint-intro-b
;;                  pfield::bitxor-constraint-intro-b-alt
;;                  pfield::bitxor-constraint-intro-2
;;                  pfield::bitxor-constraint-intro-2-alt
;;                  pfield::bitxor-constraint-intro-2b
;;                  pfield::bitxor-constraint-intro-2b-alt
;;                 ;; These 2 introduce BITNOT (e.g., for output vars):
;;                  pfield::equal-of-1-and-add-when-bitp-arg1
;;                  pfield::equal-of-1-and-add-when-bitp-arg2
;;                  bitxor-idiom-1
;;                  bitxor-idiom-2
;;                  bitxor-idiom-1-alt
;;                  bitxor-idiom-2-alt
;;                  bitnot-idiom-1
;;                  bitand-idiom-1)
;;                 ;; Now open the spec:
;;                 (spec
;;                   poseidon::hash4
;;                   poseidon::hash4-many
;;                   poseidon::hash
;;                   poseidon::rate-4-alpha-17-parameters
;;                   poseidon::rate-4-domain-fe
;;                   poseidon::param
;;                   poseidon::param->size
;;                   poseidon::init-sponge
;;                   poseidon::mode-absorb
;;                   poseidon::squeeze-base poseidon::squeeze-unroll
;;                   poseidon::absorb-base poseidon::absorb-unroll
;;                   poseidon::param->capacity$inline
;;                   poseidon::param->rate$inline
;;                   pos-fix
;;                   cdr-cons
;;                   car-cons
;;                   poseidon::sponge
;;                   poseidon::sponge-fix$inline
;;                   acl2::prime-fix ; build in?
;;                   pfield::fe-listp-constant-opener
;;                   pfield::fe-list-listp-constant-opener
;;                   acl2::all-len-equal-p-base-1 acl2::all-len-equal-p-base-2 acl2::all-len-equal-p-unroll
;;                   pfield::fe-list-listp-base-1 pfield::fe-list-listp-base-2 pfield::fe-list-listp-unroll
;;                   pfield::fe-list-listp-base-2 pfield::fe-list-listp-base-1 pfield::fe-list-listp-unroll
;;                   null
;;                   poseidon::squeeze1
;;                   poseidon::mode-fix$inline
;;                   ;acl2::nat-list-fix$inline
;;                   poseidon::mode-squeeze
;;                   acl2::nat-list-fix$inline-base acl2::nat-list-fix$inline-unroll
;;                   acl2::mv-nth-of-cons-safe
;;                   poseidon::mode-kind$inline
;;                   poseidon::sponge->mode$inline
;;                   poseidon::sponge->stat$inline
;;                   poseidon::sponge->index$inline
;;                   atom
;;                   endp
;;                   acl2::consp-of-cons
;;                   poseidon::permute
;;                   poseidon::param->constants$inline
;;                   poseidon::param->alpha$inline
;;                   poseidon::param->partial-first-p$inline
;;                   poseidon::param->mds$inline
;;                   poseidon::param->full-rounds-half$inline
;;                   poseidon::param->partial-rounds$inline
;;                   poseidon::param->prime$inline
;;                   poseidon::param->rate-then-capacity-p$inline
;;                   poseidon::param->ascending-p$inline
;;                   poseidon::all-rounds
;;                   poseidon::full-rounds-base poseidon::full-rounds-unroll
;;                   poseidon::partial-rounds-base poseidon::partial-rounds-unroll
;;                   poseidon::round
;;                   poseidon::absorb1
;;                   poseidon::add-round-constants-base poseidon::add-round-constants-unroll
;;                   poseidon::mix-layer-base poseidon::mix-layer-unroll
;;                   acl2::nat-list-fix$inline-base acl2::nat-list-fix$inline-unroll
;;                   poseidon::dot-product-base poseidon::dot-product-unroll
;;                   acl2::update-nth-unroll acl2::update-nth-base
;;                   poseidon::sub-words
;;                   poseidon::sub-words-partial
;;                   poseidon::sub-words-full-base poseidon::sub-words-full-unroll
;;                   poseidon::pow-by-alpha

;;                   ;;pfield::pow-base pfield::pow-unroll ; or recollapse pow from the efficient idiom
;;                   mul-of-same-becomes-pow pow-of-pow-arg1 mul-of-pow-same-arg1 mul-of-pow-same-arg2

;;                   acl2::nth-of-cons-safe
;;                   acl2::explode$inline
;;                   acl2::chars=>nats-base acl2::chars=>nats-unroll
;;                   acl2::lendian=>nat-base acl2::lendian=>nat-unroll
;;                   nfix
;;                   pfield::add-of-0-arg1
;;                   acl2::dab-digit-fix
;;                   acl2::dab-base-fix
;;                   acl2::len-of-cons
;;                   acl2::dab-digitp
;;                   not-<-of-add-and-0
;;                   pfield::mul-of-1-arg2
;;                   pfield::mul-associative ; address efficient exponentiation
;;                   add-of-constant-normalize-to-fep ; package
;;                   pfield::mul-of-constant-normalize-to-fep
;;                   ; (lift-r1cs-rules) ; slow or loop

;;                   acl2::integerp-when-natp
;;                   integerp-when-fep-special
;;                   not-<-of-0-when-fep-special

;;                   ;;needed?
;;                   poseidon::hashp
;;                   acl2::append-of-cons
;;                   pfield::mul-of-mul-combine-constants-alt

;;                   ;pfield::mul-of-add-arg1 ; bad?
;;                   pfield::mul-of-add-of-mul-combine-constants ; drop?
;;                   mul-of-add-combine-constants
;;                   add-combine-constant-factors-3-extra ; rationalize this set
;;                   add-combine-constant-factors-3
;;                   add-combine-constant-factors-2-extra
;;                   add-combine-constant-factors-2
;;                   pfield::add-of-mul-and-mul-combine-constants-2
;;                   pfield::add-of-mul-and-mul-combine-constants
;;                   ;mul-of-constant-and-add ; bad
;;                   )
;;                 (pfield::add-commutative-axe
;;                   ;pfield::add-commutative-2-axe ; expensive if we get rid of the intervening MULs  -- TODO: We need this, but I haven't seen the proof finish with it on
;;                   pfield::add-associative
;;                   add-combine-constant-factors-3-extra
;;                   add-combine-constant-factors-3
;;                   add-combine-constant-factors-2-extra
;;                   add-combine-constant-factors-2
;;                   pfield::add-of-mul-and-mul-combine-constants-2
;;                   pfield::add-of-mul-and-mul-combine-constants
;;                   ;mul-of-constant-and-add
;;                   helper0
;;                   helper0-extra
;;                   pfield::mul-of-mul-combine-constants-alt
;;                   add-of-constant-normalize-to-fep ; package
;;                   pfield::mul-of-constant-normalize-to-fep
;;                   )
;;                 ;; simplify type assumption (gets rid of many unneeded nodes, this helps debugging, in part because
;;                 ;; the remaining DAG has no gaps in the numbering):
;;                 ;; (pfield::fe-listp-of-append-with-key
;;                 ;;   acl2::append-with-key ; todo
;;                 ;;   pfield::fe-listp-of-append
;;                 ;;   acl2::true-listp-of-cons
;;                 ;;   acl2::true-list-fix-when-true-listp
;;                 ;;   pfield::fe-listp-of-cons
;;                 ;;   acl2::true-listp-of-append
;;                 ;;   pfield::fep-of-pow
;;                 ;;   pfield::fe-listp-when-not-consp
;;                 ;;   null
;;                 ;;   pfield::fe-listp-constant-opener
;;                 ;;   )
;;                 ))
