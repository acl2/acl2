; A proof of an R1CS for adding 3 32-bit values
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
;; (depends-on "json/uint32add-3.json")
(local (acl2::load-circom-json "json/uint32add-3.json" *BABY-JUBJUB-PRIME*))

;;;
;;; Unroll the R1CS
;;;

(local
 (lift-semaphore-r1cs *uint32add-3-r1cs-lifted*
                      (acl2::uint32add-3-vars)
                      (acl2::uint32add-3-constraints)
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
             |main.nums_bits[2][0]| |main.nums_bits[2][1]| |main.nums_bits[2][2]| |main.nums_bits[2][3]|
             |main.nums_bits[2][4]| |main.nums_bits[2][5]| |main.nums_bits[2][6]| |main.nums_bits[2][7]|
             |main.nums_bits[2][8]| |main.nums_bits[2][9]| |main.nums_bits[2][10]| |main.nums_bits[2][11]|
             |main.nums_bits[2][12]| |main.nums_bits[2][13]| |main.nums_bits[2][14]| |main.nums_bits[2][15]|
             |main.nums_bits[2][16]| |main.nums_bits[2][17]| |main.nums_bits[2][18]| |main.nums_bits[2][19]|
             |main.nums_bits[2][20]| |main.nums_bits[2][21]| |main.nums_bits[2][22]| |main.nums_bits[2][23]|
             |main.nums_bits[2][24]| |main.nums_bits[2][25]| |main.nums_bits[2][26]| |main.nums_bits[2][27]|
             |main.nums_bits[2][28]| |main.nums_bits[2][29]| |main.nums_bits[2][30]| |main.nums_bits[2][31]|
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
                       (acl2::bvplus 32
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
                                                                             |main.nums_bits[1][1]| |main.nums_bits[1][0]|))
                                     (acl2::packbv '32 '1
                                                   (acl2::make-cons-nest-mac |main.nums_bits[2][31]| |main.nums_bits[2][30]|
                                                                             |main.nums_bits[2][29]| |main.nums_bits[2][28]|
                                                                             |main.nums_bits[2][27]| |main.nums_bits[2][26]|
                                                                             |main.nums_bits[2][25]| |main.nums_bits[2][24]|
                                                                             |main.nums_bits[2][23]| |main.nums_bits[2][22]|
                                                                             |main.nums_bits[2][21]| |main.nums_bits[2][20]|
                                                                             |main.nums_bits[2][19]| |main.nums_bits[2][18]|
                                                                             |main.nums_bits[2][17]| |main.nums_bits[2][16]|
                                                                             |main.nums_bits[2][15]| |main.nums_bits[2][14]|
                                                                             |main.nums_bits[2][13]| |main.nums_bits[2][12]|
                                                                             |main.nums_bits[2][11]| |main.nums_bits[2][10]|
                                                                             |main.nums_bits[2][9]| |main.nums_bits[2][8]|
                                                                             |main.nums_bits[2][7]| |main.nums_bits[2][6]|
                                                                             |main.nums_bits[2][5]| |main.nums_bits[2][4]|
                                                                             |main.nums_bits[2][3]| |main.nums_bits[2][2]|
                                                                             |main.nums_bits[2][1]| |main.nums_bits[2][0]|))))))

;; TODO: Can we do the unrolling as part of this, instead of separately above?
(verify-semaphore-r1cs
 *uint32add-3-r1cs-lifted*
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
    |main.nums_bits[2][0]| |main.nums_bits[2][1]| |main.nums_bits[2][2]| |main.nums_bits[2][3]|
    |main.nums_bits[2][4]| |main.nums_bits[2][5]| |main.nums_bits[2][6]| |main.nums_bits[2][7]|
    |main.nums_bits[2][8]| |main.nums_bits[2][9]| |main.nums_bits[2][10]| |main.nums_bits[2][11]|
    |main.nums_bits[2][12]| |main.nums_bits[2][13]| |main.nums_bits[2][14]| |main.nums_bits[2][15]|
    |main.nums_bits[2][16]| |main.nums_bits[2][17]| |main.nums_bits[2][18]| |main.nums_bits[2][19]|
    |main.nums_bits[2][20]| |main.nums_bits[2][21]| |main.nums_bits[2][22]| |main.nums_bits[2][23]|
    |main.nums_bits[2][24]| |main.nums_bits[2][25]| |main.nums_bits[2][26]| |main.nums_bits[2][27]|
    |main.nums_bits[2][28]| |main.nums_bits[2][29]| |main.nums_bits[2][30]| |main.nums_bits[2][31]|
    |main.out_bits[0]| |main.out_bits[1]| |main.out_bits[2]| |main.out_bits[3]|
    |main.out_bits[4]| |main.out_bits[5]| |main.out_bits[6]| |main.out_bits[7]|
    |main.out_bits[8]| |main.out_bits[9]| |main.out_bits[10]| |main.out_bits[11]|
    |main.out_bits[12]| |main.out_bits[13]| |main.out_bits[14]| |main.out_bits[15]|
    |main.out_bits[16]| |main.out_bits[17]| |main.out_bits[18]| |main.out_bits[19]|
    |main.out_bits[20]| |main.out_bits[21]| |main.out_bits[22]| |main.out_bits[23]|
    |main.out_bits[24]| |main.out_bits[25]| |main.out_bits[26]| |main.out_bits[27]|
    |main.out_bits[28]| |main.out_bits[29]| |main.out_bits[30]| |main.out_bits[31]|)
 :bit-inputs '(|main.nums_bits[0][0]| |main.nums_bits[0][1]| |main.nums_bits[0][2]| |main.nums_bits[0][3]|
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
               |main.nums_bits[2][0]| |main.nums_bits[2][1]| |main.nums_bits[2][2]| |main.nums_bits[2][3]|
               |main.nums_bits[2][4]| |main.nums_bits[2][5]| |main.nums_bits[2][6]| |main.nums_bits[2][7]|
               |main.nums_bits[2][8]| |main.nums_bits[2][9]| |main.nums_bits[2][10]| |main.nums_bits[2][11]|
               |main.nums_bits[2][12]| |main.nums_bits[2][13]| |main.nums_bits[2][14]| |main.nums_bits[2][15]|
               |main.nums_bits[2][16]| |main.nums_bits[2][17]| |main.nums_bits[2][18]| |main.nums_bits[2][19]|
               |main.nums_bits[2][20]| |main.nums_bits[2][21]| |main.nums_bits[2][22]| |main.nums_bits[2][23]|
               |main.nums_bits[2][24]| |main.nums_bits[2][25]| |main.nums_bits[2][26]| |main.nums_bits[2][27]|
               |main.nums_bits[2][28]| |main.nums_bits[2][29]| |main.nums_bits[2][30]| |main.nums_bits[2][31]|)
 :global-rules '(;; integerp rules:
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
                 (acl2::unsigned-byte-p-rules)
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
                 ;;pfield::add-associative-when-constant ; at least move constants forward, so they can be combined
                 ;;pfield::add-of-add-combine-constants
                 ;;pfield::equal-of-add-combine-constants
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
                 pfield::mul-of-mul-combine-constants
                 pfield::mul-of-mul-combine-constants-alt
                 pfield::mul-of-constant-normalize-to-fep
                 pfield::mul-of-1-arg1
                 pfield::mul-of--1-becomes-neg-alt
                 acl2::bvchop-of-bvchop
                 acl2::getbit-of-bvchop
                 acl2::bvchop-of-bvplus-same
                 acl2::getbit-of-0-when-bitp
                 acl2::slice-becomes-getbit
                 acl2::bvchop-of-bvcat-cases-gen
                 acl2::bvcat-of-bvchop-low
                 acl2::bvcat-of-bvchop-high
                 pfield::mod-of-add)
 :rule-lists '( ;; recognize bitp idioms before we start changing things:
               (pfield::bitp-idiom-1
                pfield::bitp-idiom-1-alt)
               ;; introduce bvcats:
               ((pfield::bvcat-intro-rules)
                acl2::bvcat-associative)
               ;;pull out the coeffs:
               (add-of-mul-normalize-based-on-second-coeff)
               ;; commute negs forward and deal with carry bit:
               (pfield::add-of-neg-commute   ;careful
                pfield::add-of-neg-commute-2 ;careful
                bitp-of-mul-of-1/2^32-and-add-of-neg-32)
               ;; introduce bvplus:
               (pfield::add-becomes-bvplus-33-extra
                pfield::add-becomes-bvplus-34-special
                ;;pfield::add-becomes-bvplus-34
                )
               ;; handle carry:
               (add-of-mul-of-neg-shifted-carry-and-bvplus-34
                acl2::bvchop-of-bvplus-tighten-to-32
                acl2::bvplus-of-bvplus-trim-to-32-arg1
                acl2::bvplus-of-bvplus-trim-to-32-arg2)
               ;; ;; deal with carry bit:
               ;; (bitp-of-mul-of-1/2^32-and-add-of-neg-33-32
               ;;  ACL2::BVCHOP-OF-BVPLUS-TIGHTEN-TO-32
               ;;  )
               ;; blast the equality of the bvcat:
               (acl2::bvcat-equal-rewrite
                acl2::bvcat-equal-rewrite-alt
                )
               ;; Open the spec and finish the proof:
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
                 acl2::bvcat-of-slice-and-slice-adjacent
                 acl2::bvcat-of-slice-and-getbit-adjacent
                 acl2::bvcat-of-getbit-and-slice-adjacent
                 acl2::bvcat-of-getbit-and-getbit-adjacent
                 acl2::bvcat-of-getbit-and-x-adjacent
                 acl2::bvcat-of-slice-and-x-adjacent
                 acl2::bvcat-of-getbit-and-x-adjacent-2
                 acl2::bvcat-of-slice-and-x-adjacent-2
                 acl2::bvplus-commutative-dag)))
