; A proof of an R1CS for 32-bit xor
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZKSEMAPHORE")

(include-book "kestrel/ethereum/semaphore/r1cs-proof-support" :dir :system)
(include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)
(include-book "kestrel/crypto/r1cs/tools/axe-rules-r1cs" :dir :system)
(include-book "kestrel/crypto/r1cs/proof-support" :dir :system)

;; Load the R1CS:
;; (depends-on "json/uint32xor.json")
(local (acl2::load-circom-json "json/uint32xor.json" *BABY-JUBJUB-PRIME*))

;; Print some common numbers more clearly:
;; TODO: Put in a more central place?  Use #. ?
(table acl2::evisc-table 21888242871839275222246405745257275088548364400416034343698204186575808495617 "<p>") ;a bit scary since it makes p look like a var

;;;
;;; Unroll the R1CS
;;;

(local
 (lift-semaphore-r1cs *uint32xor-r1cs-lifted*
                      (acl2::uint32xor-vars)
                      (acl2::uint32xor-constraints)))

;;;
;;; The spec
;;;

(defun spec (|main.a_bits[0]| |main.a_bits[1]| |main.a_bits[2]| |main.a_bits[3]|
             |main.a_bits[4]| |main.a_bits[5]| |main.a_bits[6]| |main.a_bits[7]|
             |main.a_bits[8]| |main.a_bits[9]| |main.a_bits[10]| |main.a_bits[11]|
             |main.a_bits[12]| |main.a_bits[13]| |main.a_bits[14]| |main.a_bits[15]|
             |main.a_bits[16]| |main.a_bits[17]| |main.a_bits[18]| |main.a_bits[19]|
             |main.a_bits[20]| |main.a_bits[21]| |main.a_bits[22]| |main.a_bits[23]|
             |main.a_bits[24]| |main.a_bits[25]| |main.a_bits[26]| |main.a_bits[27]|
             |main.a_bits[28]| |main.a_bits[29]| |main.a_bits[30]| |main.a_bits[31]|
             |main.b_bits[0]| |main.b_bits[1]| |main.b_bits[2]| |main.b_bits[3]|
             |main.b_bits[4]| |main.b_bits[5]| |main.b_bits[6]| |main.b_bits[7]|
             |main.b_bits[8]| |main.b_bits[9]| |main.b_bits[10]| |main.b_bits[11]|
             |main.b_bits[12]| |main.b_bits[13]| |main.b_bits[14]| |main.b_bits[15]|
             |main.b_bits[16]| |main.b_bits[17]| |main.b_bits[18]| |main.b_bits[19]|
             |main.b_bits[20]| |main.b_bits[21]| |main.b_bits[22]| |main.b_bits[23]|
             |main.b_bits[24]| |main.b_bits[25]| |main.b_bits[26]| |main.b_bits[27]|
             |main.b_bits[28]| |main.b_bits[29]| |main.b_bits[30]| |main.b_bits[31]|
             |main.out_bits[0]| |main.out_bits[1]| |main.out_bits[2]| |main.out_bits[3]|
             |main.out_bits[4]| |main.out_bits[5]| |main.out_bits[6]| |main.out_bits[7]|
             |main.out_bits[8]| |main.out_bits[9]| |main.out_bits[10]| |main.out_bits[11]|
             |main.out_bits[12]| |main.out_bits[13]| |main.out_bits[14]| |main.out_bits[15]|
             |main.out_bits[16]| |main.out_bits[17]| |main.out_bits[18]| |main.out_bits[19]|
             |main.out_bits[20]| |main.out_bits[21]| |main.out_bits[22]| |main.out_bits[23]|
             |main.out_bits[24]| |main.out_bits[25]| |main.out_bits[26]| |main.out_bits[27]|
             |main.out_bits[28]| |main.out_bits[29]| |main.out_bits[30]| |main.out_bits[31]|)
  (equal (acl2::packbv '32 '1
                       (list |main.out_bits[31]| |main.out_bits[30]|
                             |main.out_bits[29]| |main.out_bits[28]|
                             |main.out_bits[27]| |main.out_bits[26]|
                             |main.out_bits[25]| |main.out_bits[24]|
                             |main.out_bits[23]| |main.out_bits[22]|
                             |main.out_bits[21]| |main.out_bits[20]|
                             |main.out_bits[19]| |main.out_bits[18]|
                             |main.out_bits[17]| |main.out_bits[16]|
                             |main.out_bits[15]| |main.out_bits[14]|
                             |main.out_bits[13]| |main.out_bits[12]|
                             |main.out_bits[11]| |main.out_bits[10]|
                             |main.out_bits[9]| |main.out_bits[8]|
                             |main.out_bits[7]| |main.out_bits[6]|
                             |main.out_bits[5]| |main.out_bits[4]|
                             |main.out_bits[3]| |main.out_bits[2]|
                             |main.out_bits[1]| |main.out_bits[0]|))
         (acl2::bvxor 32 (acl2::packbv '32 '1
                                       (list |main.a_bits[31]| |main.a_bits[30]|
                                             |main.a_bits[29]| |main.a_bits[28]|
                                             |main.a_bits[27]| |main.a_bits[26]|
                                             |main.a_bits[25]| |main.a_bits[24]|
                                             |main.a_bits[23]| |main.a_bits[22]|
                                             |main.a_bits[21]| |main.a_bits[20]|
                                             |main.a_bits[19]| |main.a_bits[18]|
                                             |main.a_bits[17]| |main.a_bits[16]|
                                             |main.a_bits[15]| |main.a_bits[14]|
                                             |main.a_bits[13]| |main.a_bits[12]|
                                             |main.a_bits[11]| |main.a_bits[10]|
                                             |main.a_bits[9]| |main.a_bits[8]|
                                             |main.a_bits[7]| |main.a_bits[6]|
                                             |main.a_bits[5]| |main.a_bits[4]|
                                             |main.a_bits[3]| |main.a_bits[2]|
                                             |main.a_bits[1]| |main.a_bits[0]|))
                      (acl2::packbv '32 '1
                                    (list |main.b_bits[31]| |main.b_bits[30]|
                                          |main.b_bits[29]| |main.b_bits[28]|
                                          |main.b_bits[27]| |main.b_bits[26]|
                                          |main.b_bits[25]| |main.b_bits[24]|
                                          |main.b_bits[23]| |main.b_bits[22]|
                                          |main.b_bits[21]| |main.b_bits[20]|
                                          |main.b_bits[19]| |main.b_bits[18]|
                                          |main.b_bits[17]| |main.b_bits[16]|
                                          |main.b_bits[15]| |main.b_bits[14]|
                                          |main.b_bits[13]| |main.b_bits[12]|
                                          |main.b_bits[11]| |main.b_bits[10]|
                                          |main.b_bits[9]| |main.b_bits[8]|
                                          |main.b_bits[7]| |main.b_bits[6]|
                                          |main.b_bits[5]| |main.b_bits[4]|
                                          |main.b_bits[3]| |main.b_bits[2]|
                                          |main.b_bits[1]| |main.b_bits[0]|)))))

;; TODO: Can we do the unrolling as part of this, instead of separately above?
(acl2::prove-implication-with-r1cs-prover
 (acl2::conjoin-term-with-dag! (acl2::make-conjunction-from-list
                                (cons
                                 (pfield::gen-fe-listp-assumption (acl2::dag-vars *uint32xor-r1cs-lifted*)
                                                                ''21888242871839275222246405745257275088548364400416034343698204186575808495617)
                                 ;; TODO: We probably shouldn't need this:
                                 (acl2::make-bitp-claims (acl2::dag-vars *uint32xor-r1cs-lifted*))))
                               *uint32xor-r1cs-lifted*)
 `(spec |main.a_bits[0]| |main.a_bits[1]| |main.a_bits[2]| |main.a_bits[3]|
    |main.a_bits[4]| |main.a_bits[5]| |main.a_bits[6]| |main.a_bits[7]|
    |main.a_bits[8]| |main.a_bits[9]| |main.a_bits[10]| |main.a_bits[11]|
    |main.a_bits[12]| |main.a_bits[13]| |main.a_bits[14]| |main.a_bits[15]|
    |main.a_bits[16]| |main.a_bits[17]| |main.a_bits[18]| |main.a_bits[19]|
    |main.a_bits[20]| |main.a_bits[21]| |main.a_bits[22]| |main.a_bits[23]|
    |main.a_bits[24]| |main.a_bits[25]| |main.a_bits[26]| |main.a_bits[27]|
    |main.a_bits[28]| |main.a_bits[29]| |main.a_bits[30]| |main.a_bits[31]|
    |main.b_bits[0]| |main.b_bits[1]| |main.b_bits[2]| |main.b_bits[3]|
    |main.b_bits[4]| |main.b_bits[5]| |main.b_bits[6]| |main.b_bits[7]|
    |main.b_bits[8]| |main.b_bits[9]| |main.b_bits[10]| |main.b_bits[11]|
    |main.b_bits[12]| |main.b_bits[13]| |main.b_bits[14]| |main.b_bits[15]|
    |main.b_bits[16]| |main.b_bits[17]| |main.b_bits[18]| |main.b_bits[19]|
    |main.b_bits[20]| |main.b_bits[21]| |main.b_bits[22]| |main.b_bits[23]|
    |main.b_bits[24]| |main.b_bits[25]| |main.b_bits[26]| |main.b_bits[27]|
    |main.b_bits[28]| |main.b_bits[29]| |main.b_bits[30]| |main.b_bits[31]|
    |main.out_bits[0]| |main.out_bits[1]| |main.out_bits[2]| |main.out_bits[3]|
    |main.out_bits[4]| |main.out_bits[5]| |main.out_bits[6]| |main.out_bits[7]|
    |main.out_bits[8]| |main.out_bits[9]| |main.out_bits[10]| |main.out_bits[11]|
    |main.out_bits[12]| |main.out_bits[13]| |main.out_bits[14]| |main.out_bits[15]|
    |main.out_bits[16]| |main.out_bits[17]| |main.out_bits[18]| |main.out_bits[19]|
    |main.out_bits[20]| |main.out_bits[21]| |main.out_bits[22]| |main.out_bits[23]|
    |main.out_bits[24]| |main.out_bits[25]| |main.out_bits[26]| |main.out_bits[27]|
    |main.out_bits[28]| |main.out_bits[29]| |main.out_bits[30]| |main.out_bits[31]|)
 :no-splitp t
 :global-rules '(acl2::integerp-of-bvcat
                 acl2::integerp-of-bitxor
                 acl2::integerp-of-bvnot
                 acl2::integerp-of-bvchop
                 pfield::integerp-of-add
                 pfield::integerp-of-mul
                 pfield::integerp-of-neg
                 ;; fep rules:
                 pfield::fep-of-mod ;todo: more fep rules?
                 pfield::fep-of-add
                 pfield::fep-of-mul
                 pfield::fep-of-neg
                 pfield::fep-of-bitxor
                 pfield::fep-of-bvcat
                 pfield::fep-of-bvxor
                 pfield::fep-of-bvchop
                 ;; rules to remove mod (todo: perhaps avoid introducing it):
                 pfield::neg-of-mod
                 pfield::add-of-mod-arg1
                 pfield::add-of-mod-arg2
                 pfield::mul-of-mod-arg1
                 pfield::mul-of-mod-arg1
                 ;; booleanp rules:
                 (acl2::booleanp-rules)
                 pfield::booleanp-of-fe-listp
                 ;; usigned-byte-p rules:
                 acl2::unsigned-byte-p-of-bvcat
                 acl2::unsigned-byte-p-of-bvnot
                 ;; bitp rules:
                 r1cs::bitp-of-bitxor
                 acl2::bitp-of-bitnot
                 acl2::bitp-of-getbit
                 ;; acl2::bitp-of-bvchop-of-1 ; drop?
                 ;;misc rules:
                 PRIMEP-OF-BABY-JUBJUB-PRIME-constant
                 acl2::equal-same
                 pfield::add-of-0-arg1
                 pfield::neg-of-0
;pfield::add-associative-when-constant ; at least move constants forward, so they can be combined
;pfield::add-combine-constants
;pfield::equal-of-add-combine-constants
                 acl2::ifix-when-integerp
                 pfield::mod-of-ifix-when-fep ; which rules introduce this?
                 acl2::if-of-nil-becomes-booland
                 acl2::slice-becomes-bvchop
                 (pfield::fe-listp-rules-axe)
                 r1cs::mul-normalize-constant-arg1
                 ;;r1cs::mul-normalize-constant-arg1-alt
                 acl2::bvcat-when-lowsize-is-not-positive
                 acl2::bvchop-1-becomes-getbit
                 acl2::getbit-0-of-bitnot
                 )
 :rule-lists '( ;; recognize bitp idioms before we start changing things:
               (r1cs::bitp-idiom-1
                r1cs::bitp-idiom-2)
               ;; introduce xors:
               (pfield::xor-idiom-1
                pfield::xor-idiom-2
                pfield::xor-idiom-3
                pfield::xor-idiom-3-alt
                pfield::xor-idiom-4
                pfield::xor-idiom-4-alt
                R1CS::EQUAL-OF-XOR-IDIOM
                r1cs::equal-of-xor-idiom-alt
                r1cs::equal-of-xor-idiom-b
                r1cs::equal-of-xor-idiom-b-alt
                )
               (spec
                 car-cons
                 cdr-cons
                 acl2::equal-same
                 acl2::packbv-opener
                 acl2::bvcat-equal-rewrite
                 acl2::bvcat-equal-rewrite-alt
                 acl2::bvchop-of-bvcat-cases
                 acl2::slice-becomes-getbit
                 acl2::getbit-of-bvxor
                 acl2::bvchop-of-bvxor
                 (acl2::unsigned-byte-p-rules)
                 acl2::getbit-of-bitxor-all-cases
                 acl2::getbit-of-bvcat-all
                 acl2::getbit-of-0-when-bitp
                 acl2::bvxor-1-becomes-bitxor
                 acl2::bitxor-of-bvcat-irrel-arg1
                 acl2::bitxor-of-bvcat-irrel-arg2
                 acl2::bitxor-commutative-increasing-dag)))
