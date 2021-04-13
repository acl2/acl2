; A proof of an R1CS for 32-bit addition
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZKSEMAPHORE")

(include-book "kestrel/ethereum/semaphore/r1cs-proof-support" :dir :system)
(include-book "kestrel/ethereum/semaphore/r1cs-proof-rules" :dir :system)
(include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(include-book "kestrel/bv/rules7" :dir :system) ; for BVCAT-OF-BVNOT-AND-BVNOT
(include-book "kestrel/crypto/r1cs/tools/axe-prover-r1cs" :dir :system)
(include-book "kestrel/crypto/r1cs/proof-support" :dir :system)
(include-book "kestrel/crypto/r1cs/tools/axe-rules-r1cs" :dir :system)
(include-book "kestrel/bv/rules9" :dir :system)

;; Print some common numbers more clearly:
;; TODO: Put in a more central place?  Use #. ?
(table acl2::evisc-table 21888242871839275222246405745257275088548364400416034343698204186575808495617 "<p>") ;a bit scary since it makes p look like a var

;; Load the R1CS:
;; (depends-on "json/binsum-32-2.json")
(local (acl2::load-circom-json "json/binsum-32-2.json" *baby-jubjub-prime*))

(local (lift-semaphore-r1cs *binsum-32-2-r1cs-lifted*
                            (acl2::binsum-32-2-vars)
                            (acl2::binsum-32-2-constraints)
                            :extra-rules '(primep-of-baby-jubjub-prime)
                            :remove-rules '(pfield::add-commutative-2-axe
                                            pfield::add-commutative-axe)))

(defun spec (|main.in[0][0]| |main.in[0][1]| |main.in[0][2]| |main.in[0][3]|
             |main.in[0][4]| |main.in[0][5]| |main.in[0][6]| |main.in[0][7]|
             |main.in[0][8]| |main.in[0][9]| |main.in[0][10]| |main.in[0][11]|
             |main.in[0][12]| |main.in[0][13]| |main.in[0][14]| |main.in[0][15]|
             |main.in[0][16]| |main.in[0][17]| |main.in[0][18]| |main.in[0][19]|
             |main.in[0][20]| |main.in[0][21]| |main.in[0][22]| |main.in[0][23]|
             |main.in[0][24]| |main.in[0][25]| |main.in[0][26]| |main.in[0][27]|
             |main.in[0][28]| |main.in[0][29]| |main.in[0][30]| |main.in[0][31]|

             |main.in[1][0]| |main.in[1][1]| |main.in[1][2]| |main.in[1][3]|
             |main.in[1][4]| |main.in[1][5]| |main.in[1][6]| |main.in[1][7]|
             |main.in[1][8]| |main.in[1][9]| |main.in[1][10]| |main.in[1][11]|
             |main.in[1][12]| |main.in[1][13]| |main.in[1][14]| |main.in[1][15]|
             |main.in[1][16]| |main.in[1][17]| |main.in[1][18]| |main.in[1][19]|
             |main.in[1][20]| |main.in[1][21]| |main.in[1][22]| |main.in[1][23]|
             |main.in[1][24]| |main.in[1][25]| |main.in[1][26]| |main.in[1][27]|
             |main.in[1][28]| |main.in[1][29]| |main.in[1][30]| |main.in[1][31]|

             |main.out[0]| |main.out[1]| |main.out[2]| |main.out[3]|
             |main.out[4]| |main.out[5]| |main.out[6]| |main.out[7]|
             |main.out[8]| |main.out[9]| |main.out[10]| |main.out[11]|
             |main.out[12]| |main.out[13]| |main.out[14]| |main.out[15]|
             |main.out[16]| |main.out[17]| |main.out[18]| |main.out[19]|
             |main.out[20]| |main.out[21]| |main.out[22]| |main.out[23]|
             |main.out[24]| |main.out[25]| |main.out[26]| |main.out[27]|
             |main.out[28]| |main.out[29]| |main.out[30]| |main.out[31]|)
  (equal (acl2::packbv '32 '1
                       (list |main.out[31]| |main.out[30]|
                             |main.out[29]| |main.out[28]|
                             |main.out[27]| |main.out[26]|
                             |main.out[25]| |main.out[24]|
                             |main.out[23]| |main.out[22]|
                             |main.out[21]| |main.out[20]|
                             |main.out[19]| |main.out[18]|
                             |main.out[17]| |main.out[16]|
                             |main.out[15]| |main.out[14]|
                             |main.out[13]| |main.out[12]|
                             |main.out[11]| |main.out[10]|
                             |main.out[9]| |main.out[8]|
                             |main.out[7]| |main.out[6]|
                             |main.out[5]| |main.out[4]|
                             |main.out[3]| |main.out[2]|
                             |main.out[1]| |main.out[0]|))
         (acl2::bvplus 32 (acl2::packbv '32 '1
                                        (list |main.in[0][31]| |main.in[0][30]|
                                              |main.in[0][29]| |main.in[0][28]|
                                              |main.in[0][27]| |main.in[0][26]|
                                              |main.in[0][25]| |main.in[0][24]|
                                              |main.in[0][23]| |main.in[0][22]|
                                              |main.in[0][21]| |main.in[0][20]|
                                              |main.in[0][19]| |main.in[0][18]|
                                              |main.in[0][17]| |main.in[0][16]|
                                              |main.in[0][15]| |main.in[0][14]|
                                              |main.in[0][13]| |main.in[0][12]|
                                              |main.in[0][11]| |main.in[0][10]|
                                              |main.in[0][9]| |main.in[0][8]|
                                              |main.in[0][7]| |main.in[0][6]|
                                              |main.in[0][5]| |main.in[0][4]|
                                              |main.in[0][3]| |main.in[0][2]|
                                              |main.in[0][1]| |main.in[0][0]|))
                       (acl2::packbv '32 '1
                                     (list |main.in[1][31]| |main.in[1][30]|
                                           |main.in[1][29]| |main.in[1][28]|
                                           |main.in[1][27]| |main.in[1][26]|
                                           |main.in[1][25]| |main.in[1][24]|
                                           |main.in[1][23]| |main.in[1][22]|
                                           |main.in[1][21]| |main.in[1][20]|
                                           |main.in[1][19]| |main.in[1][18]|
                                           |main.in[1][17]| |main.in[1][16]|
                                           |main.in[1][15]| |main.in[1][14]|
                                           |main.in[1][13]| |main.in[1][12]|
                                           |main.in[1][11]| |main.in[1][10]|
                                           |main.in[1][9]| |main.in[1][8]|
                                           |main.in[1][7]| |main.in[1][6]|
                                           |main.in[1][5]| |main.in[1][4]|
                                           |main.in[1][3]| |main.in[1][2]|
                                           |main.in[1][1]| |main.in[1][0]|)))))

(acl2::prove-implication-with-r1cs-prover
 (acl2::conjoin-term-with-dag! (acl2::make-conjunction-from-list
                                (cons
                                 (pfield::gen-fe-listp-assumption (acl2::dag-vars *binsum-32-2-r1cs-lifted*)
                                                                ''21888242871839275222246405745257275088548364400416034343698204186575808495617)
                                 (acl2::make-bitp-claims (acl2::dag-vars *binsum-32-2-r1cs-lifted*))))
                               *binsum-32-2-r1cs-lifted*)
 `(spec |main.in[0][0]| |main.in[0][1]| |main.in[0][2]| |main.in[0][3]|
    |main.in[0][4]| |main.in[0][5]| |main.in[0][6]| |main.in[0][7]|
    |main.in[0][8]| |main.in[0][9]| |main.in[0][10]| |main.in[0][11]|
    |main.in[0][12]| |main.in[0][13]| |main.in[0][14]| |main.in[0][15]|
    |main.in[0][16]| |main.in[0][17]| |main.in[0][18]| |main.in[0][19]|
    |main.in[0][20]| |main.in[0][21]| |main.in[0][22]| |main.in[0][23]|
    |main.in[0][24]| |main.in[0][25]| |main.in[0][26]| |main.in[0][27]|
    |main.in[0][28]| |main.in[0][29]| |main.in[0][30]| |main.in[0][31]|

    |main.in[1][0]| |main.in[1][1]| |main.in[1][2]| |main.in[1][3]|
    |main.in[1][4]| |main.in[1][5]| |main.in[1][6]| |main.in[1][7]|
    |main.in[1][8]| |main.in[1][9]| |main.in[1][10]| |main.in[1][11]|
    |main.in[1][12]| |main.in[1][13]| |main.in[1][14]| |main.in[1][15]|
    |main.in[1][16]| |main.in[1][17]| |main.in[1][18]| |main.in[1][19]|
    |main.in[1][20]| |main.in[1][21]| |main.in[1][22]| |main.in[1][23]|
    |main.in[1][24]| |main.in[1][25]| |main.in[1][26]| |main.in[1][27]|
    |main.in[1][28]| |main.in[1][29]| |main.in[1][30]| |main.in[1][31]|

    |main.out[0]| |main.out[1]| |main.out[2]| |main.out[3]|
    |main.out[4]| |main.out[5]| |main.out[6]| |main.out[7]|
    |main.out[8]| |main.out[9]| |main.out[10]| |main.out[11]|
    |main.out[12]| |main.out[13]| |main.out[14]| |main.out[15]|
    |main.out[16]| |main.out[17]| |main.out[18]| |main.out[19]|
    |main.out[20]| |main.out[21]| |main.out[22]| |main.out[23]|
    |main.out[24]| |main.out[25]| |main.out[26]| |main.out[27]|
    |main.out[28]| |main.out[29]| |main.out[30]| |main.out[31]|)
 :INTERPRETED-FUNCTION-ALIST (acl2::make-interpreted-function-alist '(acl2::expt2$inline
                                                                      ;;pfield::pow INV ;bad: can overflow the stack!
                                                                      pfield::minus1
                                                                      acl2::power-of-2p PFIELD::POS-FIX) (w state))
 :no-splitp t
 :monitor '(ACL2::ADDING-32-IDIOM
            ACL2::ADDING-32-IDIOM-alt)
 :global-rules '(acl2::rationalp-when-integerp
                 acl2::integerp-of-bvcat
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
                 acl2::unsigned-byte-p-of-bvchop
                 acl2::unsigned-byte-p-of-bvnot
                 acl2::unsigned-byte-p-of-bvplus
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
                 acl2::slice-becomes-getbit
                 ACL2::GETBIT-OF-BVCHOP
                 acl2::getbit-of-0-when-bitp
                 ACL2::BVCHOP-OF-BVCAT-CASES-GEN
                 ;;ACL2::BVCHOP-OF-BVplus ;this trims the bvplus, which causes problems in reassembly
                 ACL2::BVCHOP-IDENTITY
                 acl2::bvcat-of-bvchop-low
                 acl2::bvcat-of-bvchop-high
                 acl2::mod-when-<
                 acl2::bvcat-numeric-bound
                 ACL2::NOT-<-OF-BVCAT-AND-0)
 :rule-lists '( ;; recognize bitp idioms before we start changing things:
               (r1cs::bitp-idiom-1
                r1cs::bitp-idiom-2)
               (pfield::mul-of-power-of-2-when-bitp          ; introduces bvcat
                pfield::mul-of-negative-power-of-2-when-bitp ; introduces bvcat and bitnot
                pfield::add-commutative-2-when-constant
                pfield::add-commutative-when-constant
                pfield::add-associative-when-constant ; at least move constants forward, so they can be combined
                pfield::add-combine-constants
                pfield::add-of-bvcat-1-of-0-and-add-of-bvcat-1-of-0-extra ; combine the bvcats
                ;;r1cs::add-of-bvcat-and-add-of-bvcat-combine-interloper-gen
                ;; these are for when one argument fits into the zeroes of the other:
                pfield::add-of-bvcat-of-0-when-unsigned-byte-p-arg1
                pfield::add-of-bvcat-of-0-when-unsigned-byte-p-arg2
                pfield::add-of-bvcat-of-0-when-unsigned-byte-p-arg1-bitp ; for lowsize=1
                pfield::add-of-bvcat-of-0-when-unsigned-byte-p-arg2-bitp ; for lowsize=1
                pfield::add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra
                pfield::add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special ; for lowsize=1
                pfield::add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-alt
                pfield::add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special-alt
                acl2::bvcat-associative-helper ;; not the usual rule, since we want to expose the low zeros
                ;; Lift nots above bvcats:
                acl2::bvcat-of-bvnot-and-bvnot
                acl2::bvcat-of-bitnot-and-bvnot
                acl2::bvcat-of-bvnot-and-bitnot
                acl2::bvcat-of-bitnot-and-bitnot
                pfield::add-of-bvnot-becomes-add-of-neg
                pfield::add-of-bvnot-becomes-add-of-neg-arg2
                add-of-neg-of-add-of-bvcat-of-0
                add-of-neg-of-add-of-bvcat-of-0-extra
                swing-bit-onto-outer-cat ;todo: awkward.  why needed?
                pfield::equal-of-0-and-add-of-add-of-neg-lemma
                pfield::equal-of-add-of-neg-arg2-solve)
               ;; Now handle the addition
               (acl2::bvcat-associative ;opposite of what we do above
                acl2::adding-32-idiom
                acl2::adding-32-idiom-alt)
               ;; Now split the bvcats:
               (acl2::bvcat-equal-rewrite
                acl2::bvcat-equal-rewrite-alt)
               ;; Now open the spec and finish the proof:
               (spec
                 car-cons
                 cdr-cons
                 acl2::packbv-opener
                 ;;reassemble larger bvs:
                 acl2::bvcat-of-getbit-and-getbit-adjacent
                 acl2::bvcat-of-slice-and-slice-adjacent
                 acl2::bvcat-of-getbit-and-slice-adjacent
                 acl2::bvcat-of-slice-and-getbit-adjacent
                 acl2::bvcat-of-getbit-and-x-adjacent-2
                 acl2::bvcat-of-getbit-and-x-adjacent
                 acl2::bvcat-of-slice-and-x-adjacent-2
                 acl2::bvcat-of-slice-and-x-adjacent)))
