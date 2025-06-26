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

;; (aleo::p1cs (aleovm::keccak256-round--constraints))

;; todo: are there any unnecesary constraints and vars?

;; the first 1600 input variables are the state array A
(defconst *round-input-vars-a*
  (acl2::make-var-names '|w| 1600))

;; the next 64 input variables are the round constant
(defconst *round-input-vars-rc*
  (acl2::make-var-names-from '|w| 1600 64))

(defconst *round-input-vars*
  (append *round-input-vars-a*
          *round-input-vars-rc*))

;; The 1600 output vars represent the state array (25 lanes of 64 bits each).
;; This was very hard to figure out, due to the vars for lane (0,0) coming last
;; in the numbering.  (This might be because lane (0,0) is the only lane into
;; which the round constant is xored in the iota operation.)
(defconst *round-output-vars*
  (append
    (acl2::make-var-names-from '|w| 8064 64) ;; special treatment for lane (0,0)
    (acl2::make-var-names-from '|w| 5056 64)
    (acl2::make-var-names-from '|w| 5184 64)
    (acl2::make-var-names-from '|w| 5312 64)
    (acl2::make-var-names-from '|w| 5440 64)
    (acl2::make-var-names-from '|w| 5568 64)
    (acl2::make-var-names-from '|w| 5696 64)
    (acl2::make-var-names-from '|w| 5824 64)
    (acl2::make-var-names-from '|w| 5952 64)
    (acl2::make-var-names-from '|w| 6080 64)
    (acl2::make-var-names-from '|w| 6208 64)
    (acl2::make-var-names-from '|w| 6336 64)
    (acl2::make-var-names-from '|w| 6464 64)
    (acl2::make-var-names-from '|w| 6592 64)
    (acl2::make-var-names-from '|w| 6720 64)
    (acl2::make-var-names-from '|w| 6848 64)
    (acl2::make-var-names-from '|w| 6976 64)
    (acl2::make-var-names-from '|w| 7104 64)
    (acl2::make-var-names-from '|w| 7232 64)
    (acl2::make-var-names-from '|w| 7360 64)
    (acl2::make-var-names-from '|w| 7488 64)
    (acl2::make-var-names-from '|w| 7616 64)
    (acl2::make-var-names-from '|w| 7744 64)
    (acl2::make-var-names-from '|w| 7872 64)
    (acl2::make-var-names-from '|w| 8000 64)))

(set-rewrite-stack-limit 10000)

;; I have to rephrase the specification a bit, since the R1CS for the round
;; takes the round constant, rc, rather than the round number, i_r, as in the
;; spec.

;; like iota from the spec but takes the round constant, rc, instead of the round number i_r
(defund iota-with-rc (a rc w)
  (declare (xargs :guard (and (sha3::w-valp w)
                              (sha3::state-arrayp a w)
                              (sha3::bit-stringp rc)
                              (equal (len rc) w))
                  :guard-hints (("Goal" :in-theory (enable sha3::w-valp)))))
  (let* ((a-prime a)
         ;; (rc (repeat w 0))
         ;; (l (lg w))
         ;; (rc (iota-aux 0 l rc i_r w))
         (a-prime (sha3::iota-aux2 0 a-prime a rc w)))
    a-prime))

;; like rnd from the spec but takes the round constant, rc, instead of the round number i_r
(defun rnd-with-rc (a rc w)
  (declare (xargs :guard (and (sha3::w-valp w)
                              (sha3::state-arrayp a w)
                              (sha3::bit-stringp rc)
                              (equal (len rc) w))))
  (iota-with-rc (sha3::chi (sha3::pi-fn (sha3::rho (sha3::theta a w) w) w) w) rc w))

;; The claim to prove.  This says that the output vars are correct wrt the input vars.
(make-event
  `(defun spec-round (,@*round-input-vars* ,@*round-output-vars*)
     (declare (xargs ;; :guard (and ,@(acl2::make-bitp-claims *round-input-vars*)
                     ;;             ,@(acl2::make-bitp-claims *round-output-vars*)
                     ;;             ) ; todo: put back
                :verify-guards nil ; todo: too slow!
                :guard-hints (("Goal" :do-not '(preprocess) :in-theory (e/d (acl2::unsigned-byte-p-becomes-bitp)
                                                                            (bitp acl2::bitp-becomes-unsigned-byte-p))))))
     (equal (rnd-with-rc (sha3::bits-to-state-array (list ,@*round-input-vars-a*) 64)
                         (list ,@*round-input-vars-rc*)
                         64)
            (sha3::bits-to-state-array (list ,@*round-output-vars*) 64)
            )))

;; Lift the R1CS into logic:
(local
  (r1cs::lift-r1cs *keccak256-round*
                   (r1cs-constraint-list-vars (aleovm::keccak256-round--constraints))
                   ;; todo: only include the constraints that we need:
                   ;; ex: of the 4800 constraints, we may only need the first 1920 and the last 1600?
                   (aleovm::keccak256-round--constraints)
                   ;; (append (take 1920 (aleovm::keccak256-round--constraints))
                   ;;         (take 1600 (nthcdr 3200 (aleovm::keccak256-round--constraints))))
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

;; Assumes:
;; 1. The R1CS holds
;; 2. x0 is the constant 1
;; 3. All the vars are field elements
;; Proves that the spec (spec-round) holds.
(acl2::prove-implication-with-r1cs-prover
  (acl2::make-conjunction-dag! (acl2::make-term-into-dag-basic! '(equal |x0| '1) ; x0 is always equal to 1 !
                                                                nil)
                               (acl2::make-conjunction-dag! (acl2::make-term-into-dag-basic!
                                                              ;; todo: tool could translate the fe-listp assumption
                                                              (pfield::gen-fe-listp-assumption (acl2::dag-vars *keccak256-round*)
                                                                                               ''8444461749428370424248824938781546531375899335154063827935233455917409239041)
                                                              nil)
                                                            *keccak256-round*))
  `(spec-round ,@*round-input-vars* ,@*round-output-vars*)
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
                (
                 spec-round
                 rnd-with-rc
                 iota-with-rc
                 sha3::iota-aux2-base sha3::iota-aux2-unroll
                 sha3::get-lane
                 sha3::set-lane
                 sha3::nth-bit
                 sha3::update-bit
                 sha3::update-nth-bit
                 sha3::update-nth-lane
                 sha3::update-nth-plane
                 sha3::chi
                 sha3::chi-planes-base sha3::chi-planes-unroll
                 sha3::chi-lanes-base sha3::chi-lanes-unroll
                 sha3::chi-lane-base sha3::chi-lane-unroll
                 sha3::theta
                 sha3::theta-planes-base sha3::theta-planes-unroll
                 sha3::theta-lanes-base sha3::theta-lanes-unroll
                 sha3::theta-lane-base sha3::theta-lane-unroll
                 sha3::theta-d-lanes-base sha3::theta-d-lanes-unroll
                 sha3::theta-d-lane
                 sha3::theta-d
                 sha3::theta-c
                 sha3::theta-c-lanes-base sha3::theta-c-lanes-unroll
                 sha3::theta-c-lane-base sha3::theta-c-lane-unroll
                 sha3::rho
                 sha3::rho-aux-aux-base sha3::rho-aux-aux-unroll
                 sha3::rho-aux-base sha3::rho-aux-unroll
                 sha3::pi-fn
                 sha3::pi-planes-base sha3::pi-planes-unroll
                 sha3::pi-lanes-base sha3::pi-lanes-unroll
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
                 ;acl2::equal-of-cons-and-cons
                 acl2::bitxor-commutative-2-increasing-axe
                 acl2::bitxor-associative
                 acl2::bitxor-of-1-becomes-bitnot-arg2
                 acl2::update-nth-base acl2::update-nth-unroll ; since we have a cons nest on one side an update-nth on the other side
                                                               ;acl2::nth-update-nth-safe
                 acl2::bitxor-of-bitnot-arg1
                 acl2::bitxor-of-bitnot-arg2
                 )))
