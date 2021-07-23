; A proof of an R1CS for adding 2 32-bit values
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZKSEMAPHORE")

(include-book "kestrel/ethereum/semaphore/r1cs-proof-support" :dir :system)
(include-book "kestrel/crypto/r1cs/sparse/rules-axe" :dir :system) ;todo: reduce
(include-book "kestrel/crypto/r1cs/sparse/rules" :dir :system) ;todo: reduce
(include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)
(include-book "kestrel/crypto/r1cs/tools/axe-rules-r1cs" :dir :system)
(include-book "kestrel/crypto/r1cs/proof-support" :dir :system)
(include-book "kestrel/bv/rules9" :dir :system)
(include-book "kestrel/ethereum/semaphore/r1cs-proof-rules" :dir :system)

;; Load the R1CS:
;; (depends-on "json/uint32add-2.json")
(local (acl2::load-circom-json "json/uint32add-2.json" *BABY-JUBJUB-PRIME*))

;;;
;;; Unroll the R1CS
;;;

(local
 (lift-semaphore-r1cs *uint32add-2-r1cs-lifted*
                      (acl2::uint32add-2-vars)
                      (acl2::uint32add-2-constraints)
                      ;; todo: think about this:
                      :remove-rules '(r1cs::mul-normalize-constant-arg1)))

(defmacro acl2::make-cons-nest-mac (&rest terms)
  (acl2::make-cons-nest terms))

;;;
;;; The spec
;;;

(defun spec (|main.nums_bits[0][0]| |main.nums_bits[0][1]| |main.nums_bits[0][2]| |main.nums_bits[0][3]|
             |main.nums_bits[0][4]| |main.nums_bits[0][5]| |main.nums_bits[0][6]| |main.nums_bits[0][7]|
             |main.nums_bits[0][8]| |main.nums_bits[0][9]| |main.nums_bits[0][10]| |main.nums_bits[0][11]|
             |main.nums_bits[0][12]| |main.nums_bits[0][13]| |main.nums_bits[0][14]| |main.nums_bits[0][15]|
             |main.nums_bits[0][16]| |main.nums_bits[0][17]| |main.nums_bits[0][18]| |main.nums_bits[0][19]|
             |main.nums_bits[0][20]| |main.nums_bits[0][21]| |main.nums_bits[0][22]| |main.nums_bits[0][23]|
             |main.nums_bits[0][24]| |main.nums_bits[0][25]| |main.nums_bits[0][26]| |main.nums_bits[0][27]|
             |main.nums_bits[0][28]| |main.nums_bits[0][29]| |main.nums_bits[0][30]| |main.nums_bits[0][31]|
             |main.nums_bits[1][0]| |main.nums_bits[1][1]| |main.nums_bits[1][2]| |main.nums_bits[1][3]|
             |main.nums_bits[1][4]| |main.nums_bits[1][5]| |main.nums_bits[1][6]| |main.nums_bits[1][7]|
             |main.nums_bits[1][8]| |main.nums_bits[1][9]| |main.nums_bits[1][10]| |main.nums_bits[1][11]|
             |main.nums_bits[1][12]| |main.nums_bits[1][13]| |main.nums_bits[1][14]| |main.nums_bits[1][15]|
             |main.nums_bits[1][16]| |main.nums_bits[1][17]| |main.nums_bits[1][18]| |main.nums_bits[1][19]|
             |main.nums_bits[1][20]| |main.nums_bits[1][21]| |main.nums_bits[1][22]| |main.nums_bits[1][23]|
             |main.nums_bits[1][24]| |main.nums_bits[1][25]| |main.nums_bits[1][26]| |main.nums_bits[1][27]|
             |main.nums_bits[1][28]| |main.nums_bits[1][29]| |main.nums_bits[1][30]| |main.nums_bits[1][31]|
             |main.out_bits[0]| |main.out_bits[1]| |main.out_bits[2]| |main.out_bits[3]|
             |main.out_bits[4]| |main.out_bits[5]| |main.out_bits[6]| |main.out_bits[7]|
             |main.out_bits[8]| |main.out_bits[9]| |main.out_bits[10]| |main.out_bits[11]|
             |main.out_bits[12]| |main.out_bits[13]| |main.out_bits[14]| |main.out_bits[15]|
             |main.out_bits[16]| |main.out_bits[17]| |main.out_bits[18]| |main.out_bits[19]|
             |main.out_bits[20]| |main.out_bits[21]| |main.out_bits[22]| |main.out_bits[23]|
             |main.out_bits[24]| |main.out_bits[25]| |main.out_bits[26]| |main.out_bits[27]|
             |main.out_bits[28]| |main.out_bits[29]| |main.out_bits[30]| |main.out_bits[31]|)
  (equal (acl2::packbv '32 '1
                       (acl2::make-cons-nest-mac |main.out_bits[31]| |main.out_bits[30]|
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
         (acl2::bvplus 32 (acl2::packbv '32 '1
                                        (acl2::make-cons-nest-mac |main.nums_bits[0][31]| |main.nums_bits[0][30]|
                                                                  |main.nums_bits[0][29]| |main.nums_bits[0][28]|
                                                                  |main.nums_bits[0][27]| |main.nums_bits[0][26]|
                                                                  |main.nums_bits[0][25]| |main.nums_bits[0][24]|
                                                                  |main.nums_bits[0][23]| |main.nums_bits[0][22]|
                                                                  |main.nums_bits[0][21]| |main.nums_bits[0][20]|
                                                                  |main.nums_bits[0][19]| |main.nums_bits[0][18]|
                                                                  |main.nums_bits[0][17]| |main.nums_bits[0][16]|
                                                                  |main.nums_bits[0][15]| |main.nums_bits[0][14]|
                                                                  |main.nums_bits[0][13]| |main.nums_bits[0][12]|
                                                                  |main.nums_bits[0][11]| |main.nums_bits[0][10]|
                                                                  |main.nums_bits[0][9]| |main.nums_bits[0][8]|
                                                                  |main.nums_bits[0][7]| |main.nums_bits[0][6]|
                                                                  |main.nums_bits[0][5]| |main.nums_bits[0][4]|
                                                                  |main.nums_bits[0][3]| |main.nums_bits[0][2]|
                                                                  |main.nums_bits[0][1]| |main.nums_bits[0][0]|))
                       (acl2::packbv '32 '1
                                     (acl2::make-cons-nest-mac |main.nums_bits[1][31]| |main.nums_bits[1][30]|
                                                               |main.nums_bits[1][29]| |main.nums_bits[1][28]|
                                                               |main.nums_bits[1][27]| |main.nums_bits[1][26]|
                                                               |main.nums_bits[1][25]| |main.nums_bits[1][24]|
                                                               |main.nums_bits[1][23]| |main.nums_bits[1][22]|
                                                               |main.nums_bits[1][21]| |main.nums_bits[1][20]|
                                                               |main.nums_bits[1][19]| |main.nums_bits[1][18]|
                                                               |main.nums_bits[1][17]| |main.nums_bits[1][16]|
                                                               |main.nums_bits[1][15]| |main.nums_bits[1][14]|
                                                               |main.nums_bits[1][13]| |main.nums_bits[1][12]|
                                                               |main.nums_bits[1][11]| |main.nums_bits[1][10]|
                                                               |main.nums_bits[1][9]| |main.nums_bits[1][8]|
                                                               |main.nums_bits[1][7]| |main.nums_bits[1][6]|
                                                               |main.nums_bits[1][5]| |main.nums_bits[1][4]|
                                                               |main.nums_bits[1][3]| |main.nums_bits[1][2]|
                                                               |main.nums_bits[1][1]| |main.nums_bits[1][0]|)))))

;; TODO: Can we do the unrolling as part of this, instead of separately above?
(verify-semaphore-r1cs
 *uint32add-2-r1cs-lifted*
 (spec |main.nums_bits[0][0]| |main.nums_bits[0][1]| |main.nums_bits[0][2]| |main.nums_bits[0][3]|
   |main.nums_bits[0][4]| |main.nums_bits[0][5]| |main.nums_bits[0][6]| |main.nums_bits[0][7]|
   |main.nums_bits[0][8]| |main.nums_bits[0][9]| |main.nums_bits[0][10]| |main.nums_bits[0][11]|
   |main.nums_bits[0][12]| |main.nums_bits[0][13]| |main.nums_bits[0][14]| |main.nums_bits[0][15]|
   |main.nums_bits[0][16]| |main.nums_bits[0][17]| |main.nums_bits[0][18]| |main.nums_bits[0][19]|
   |main.nums_bits[0][20]| |main.nums_bits[0][21]| |main.nums_bits[0][22]| |main.nums_bits[0][23]|
   |main.nums_bits[0][24]| |main.nums_bits[0][25]| |main.nums_bits[0][26]| |main.nums_bits[0][27]|
   |main.nums_bits[0][28]| |main.nums_bits[0][29]| |main.nums_bits[0][30]| |main.nums_bits[0][31]|
   |main.nums_bits[1][0]| |main.nums_bits[1][1]| |main.nums_bits[1][2]| |main.nums_bits[1][3]|
   |main.nums_bits[1][4]| |main.nums_bits[1][5]| |main.nums_bits[1][6]| |main.nums_bits[1][7]|
   |main.nums_bits[1][8]| |main.nums_bits[1][9]| |main.nums_bits[1][10]| |main.nums_bits[1][11]|
   |main.nums_bits[1][12]| |main.nums_bits[1][13]| |main.nums_bits[1][14]| |main.nums_bits[1][15]|
   |main.nums_bits[1][16]| |main.nums_bits[1][17]| |main.nums_bits[1][18]| |main.nums_bits[1][19]|
   |main.nums_bits[1][20]| |main.nums_bits[1][21]| |main.nums_bits[1][22]| |main.nums_bits[1][23]|
   |main.nums_bits[1][24]| |main.nums_bits[1][25]| |main.nums_bits[1][26]| |main.nums_bits[1][27]|
   |main.nums_bits[1][28]| |main.nums_bits[1][29]| |main.nums_bits[1][30]| |main.nums_bits[1][31]|
   |main.out_bits[0]| |main.out_bits[1]| |main.out_bits[2]| |main.out_bits[3]|
   |main.out_bits[4]| |main.out_bits[5]| |main.out_bits[6]| |main.out_bits[7]|
   |main.out_bits[8]| |main.out_bits[9]| |main.out_bits[10]| |main.out_bits[11]|
   |main.out_bits[12]| |main.out_bits[13]| |main.out_bits[14]| |main.out_bits[15]|
   |main.out_bits[16]| |main.out_bits[17]| |main.out_bits[18]| |main.out_bits[19]|
   |main.out_bits[20]| |main.out_bits[21]| |main.out_bits[22]| |main.out_bits[23]|
   |main.out_bits[24]| |main.out_bits[25]| |main.out_bits[26]| |main.out_bits[27]|
   |main.out_bits[28]| |main.out_bits[29]| |main.out_bits[30]| |main.out_bits[31]|)
 :bit-inputs '(|main.nums_bits[0][0]| |main.nums_bits[0][1]|
               |main.nums_bits[0][2]| |main.nums_bits[0][3]| |main.nums_bits[0][4]|
               |main.nums_bits[0][5]| |main.nums_bits[0][6]| |main.nums_bits[0][7]|
               |main.nums_bits[0][8]| |main.nums_bits[0][9]| |main.nums_bits[0][10]|
               |main.nums_bits[0][11]| |main.nums_bits[0][12]| |main.nums_bits[0][13]|
               |main.nums_bits[0][14]| |main.nums_bits[0][15]| |main.nums_bits[0][16]|
               |main.nums_bits[0][17]| |main.nums_bits[0][18]| |main.nums_bits[0][19]|
               |main.nums_bits[0][20]| |main.nums_bits[0][21]| |main.nums_bits[0][22]|
               |main.nums_bits[0][23]| |main.nums_bits[0][24]| |main.nums_bits[0][25]|
               |main.nums_bits[0][26]| |main.nums_bits[0][27]| |main.nums_bits[0][28]|
               |main.nums_bits[0][29]| |main.nums_bits[0][30]| |main.nums_bits[0][31]|
               |main.nums_bits[1][0]| |main.nums_bits[1][1]| |main.nums_bits[1][2]|
               |main.nums_bits[1][3]| |main.nums_bits[1][4]| |main.nums_bits[1][5]|
               |main.nums_bits[1][6]| |main.nums_bits[1][7]| |main.nums_bits[1][8]|
               |main.nums_bits[1][9]| |main.nums_bits[1][10]| |main.nums_bits[1][11]|
               |main.nums_bits[1][12]| |main.nums_bits[1][13]| |main.nums_bits[1][14]|
               |main.nums_bits[1][15]| |main.nums_bits[1][16]| |main.nums_bits[1][17]|
               |main.nums_bits[1][18]| |main.nums_bits[1][19]| |main.nums_bits[1][20]|
               |main.nums_bits[1][21]| |main.nums_bits[1][22]| |main.nums_bits[1][23]|
               |main.nums_bits[1][24]| |main.nums_bits[1][25]| |main.nums_bits[1][26]|
               |main.nums_bits[1][27]| |main.nums_bits[1][28]| |main.nums_bits[1][29]|
               |main.nums_bits[1][30]| |main.nums_bits[1][31]| )
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
                 pfield::fep-of-bitxor ;todo: package
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
                 primep-of-baby-jubjub-prime-constant
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
                 ;;r1cs::mul-normalize-constant-arg1
                 ;;r1cs::mul-normalize-constant-arg1-alt
                 acl2::bvcat-when-lowsize-is-not-positive
                 acl2::bvchop-1-becomes-getbit
                 acl2::getbit-0-of-bitnot
                 PFIELD::MUL-COMBINE-CONSTANTS
                 PFIELD::MUL-COMBINE-CONSTANTS-alt
                 PFIELD::MUL-OF-CONSTANT-NORMALIZE-TO-FEP
                 PFIELD::MUL-OF-1-ARG1
                 pfield::mul-of--1-becomes-neg-alt
                 (acl2::unsigned-byte-p-rules)
                 ACL2::BVCHOP-OF-BVCHOP
                 ACL2::GETBIT-OF-BVCHOP
                 ACL2::BVCHOP-OF-BVPLUS-SAME
                 ACL2::GETBIT-OF-0-WHEN-BITP
                 ACL2::SLICE-BECOMES-GETBIT
                 ACL2::BVCHOP-OF-BVCAT-CASES-GEN
                 ACL2::BVCAT-OF-BVCHOP-LOW
                 ACL2::BVCAT-OF-BVCHOP-high
                 )
 :rule-lists '( ;; recognize bitp idioms before we start changing things:
               (pfield::bitp-idiom-1
                pfield::bitp-idiom-1-alt)
               ;; introduce bvcats:
               ((pfield::bvcat-intro-rules)
                acl2::bvcat-associative)
               ( ;;pull out the coeffs:
                ADD-OF-MUL-NORMALIZE-COEFFS
                )
;introduce bvplus:
               (pfield::ADD-BECOMES-BVPLUS-33-extra
                )
               ;; deal with carry bit:
               (bitp-of-mul-of-1/2^32-and-add-of-neg-33-32
                acl2::BVCHOP-OF-BVPLUS-TIGHTEN-TO-32
                )
               ;; blast the equality of the bvcat:
               (acl2::bvcat-equal-rewrite
                acl2::bvcat-equal-rewrite-alt
                )
               ;; ;; introduce xors:
               ;; (pfield::xor-idiom-1
               ;;  pfield::xor-idiom-2
               ;;  pfield::xor-idiom-3
               ;;  pfield::xor-idiom-3-alt
               ;;  pfield::xor-idiom-4
               ;;  pfield::xor-idiom-4-alt
               ;;  R1CS::EQUAL-OF-XOR-IDIOM
               ;;  r1cs::equal-of-xor-idiom-alt
               ;;  r1cs::equal-of-xor-idiom-b
               ;;  r1cs::equal-of-xor-idiom-b-alt
               ;;  )
               (spec
                 car-cons
                 cdr-cons
                 acl2::equal-same
                 acl2::packbv-opener
                 acl2::bvchop-of-bvcat-cases
                 acl2::slice-becomes-getbit
                 acl2::getbit-of-bvxor
                 acl2::bvchop-of-bvxor

                 acl2::getbit-of-bitxor-all-cases
                 acl2::getbit-of-bvcat-all
                 acl2::getbit-of-0-when-bitp
                 acl2::bvxor-1-becomes-bitxor
                 acl2::bitxor-of-bvcat-irrel-arg1
                 acl2::bitxor-of-bvcat-irrel-arg2
                 acl2::bitxor-commutative-increasing-dag

                 ;; now that we have substituted for the bits, recreate the bvcats:
                 ACL2::BVCAT-OF-SLICE-AND-SLICE-ADJACENT
                 ACL2::BVCAT-OF-SLICE-AND-getbit-ADJACENT
                 ACL2::BVCAT-OF-getbit-AND-SLICE-ADJACENT
                 ACL2::BVCAT-OF-getbit-AND-getbit-ADJACENT
                 ACL2::BVCAT-OF-GETBIT-AND-X-ADJACENT
                 ACL2::BVCAT-OF-slice-AND-X-ADJACENT
                 ACL2::BVCAT-OF-GETBIT-AND-X-ADJACENT-2
                 ACL2::BVCAT-OF-slice-AND-X-ADJACENT-2
                 ACL2::BVPLUS-COMMUTATIVE-DAG
                 )
               ))
