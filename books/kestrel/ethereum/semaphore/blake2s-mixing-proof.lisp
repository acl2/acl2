; A proof of an R1CS for a mixing function from blake2s
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZKSEMAPHORE")

;; STATUS: COMPLETE

(include-book "r1cs-proof-support")
(include-book "r1cs-proof-rules")
(include-book "kestrel/crypto/r1cs/sparse/rules-axe" :dir :system)
(include-book "kestrel/crypto/r1cs/sparse/rules" :dir :system)
(include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)
(include-book "kestrel/crypto/r1cs/gadgets/xor-rules" :dir :system)
(include-book "kestrel/crypto/r1cs/tools/axe-rules-r1cs" :dir :system)
(include-book "kestrel/crypto/blake/blake2s" :dir :system) ;the spec
(include-book "kestrel/bv/rules9" :dir :system)
(include-book "kestrel/bv-lists/packbv-little" :dir :system)
(local (include-book "kestrel/lists-light/cons" :dir :system)) ; for equal-of-cons

;; Load the R1CS:
;; (depends-on "json/blake2s-mixingg-0.json")
;; This is for MixingG(0, 4, 8, 12)
(local (acl2::load-circom-json "json/blake2s-mixingg-0.json" *baby-jubjub-prime*))

;; 1218 vars
;; 646 constraints

;;;
;;; Lift the R1CS
;;;

(local
 (lift-semaphore-r1cs *blake2s-mixingg-0-r1cs-lifted*
                      (acl2::blake2s-mixingg-0-vars)
                      (acl2::blake2s-mixingg-0-constraints)
                      ;; :extra-rules '(primep-of-baby-jubjub-prime-constant)
                      ;; todo: remove these as default rules
                      :remove-rules '(pfield::add-commutative-axe
                                      pfield::add-commutative-2-axe)))

;; Takes 32 bits (least signficant bit first) and packs them into a 32-bit word
(defun pack-blake-word (bit0 bit1 bit2 bit3
                             bit4 bit5 bit6 bit7
                             bit8 bit9 bit10 bit11
                             bit12 bit13 bit14 bit15
                             bit16 bit17 bit18 bit19
                             bit20 bit21 bit22 bit23
                             bit24 bit25 bit26 bit27
                             bit28 bit29 bit30 bit31)
  (declare (xargs :guard (and (bitp bit0) (bitp bit1) (bitp bit2) (bitp bit3)
                              (bitp bit4) (bitp bit5) (bitp bit6) (bitp bit7)
                              (bitp bit8) (bitp bit9) (bitp bit10) (bitp bit11)
                              (bitp bit12) (bitp bit13) (bitp bit14) (bitp bit15)
                              (bitp bit16) (bitp bit17) (bitp bit18) (bitp bit19)
                              (bitp bit20) (bitp bit21) (bitp bit22) (bitp bit23)
                              (bitp bit24) (bitp bit25) (bitp bit26) (bitp bit27)
                              (bitp bit28) (bitp bit29) (bitp bit30) (bitp bit31))))
  (acl2::packbv-little 32 1 (list bit0 bit1 bit2 bit3
                                  bit4 bit5 bit6 bit7
                                  bit8 bit9 bit10 bit11
                                  bit12 bit13 bit14 bit15
                                  bit16 bit17 bit18 bit19
                                  bit20 bit21 bit22 bit23
                                  bit24 bit25 bit26 bit27
                                  bit28 bit29 bit30 bit31)))

;; The spec for this R1CS.  Conceptually, this takes inputs v_in, x and y, and
;; also takes the expected output, v_out.  But the values come in as individual
;; bits.  For the values of A, B, C, and D (passed to the BLAKE2s mixing
;; function), this uses 0, 4, 8, and 12.  This packs the input bits, then calls
;; g (the mixing function from blake2s) on the packed inputs, then checks
;; whether the output of g is equal to the (likewise packed) output bits.  The
;; proof will show that if the R1CS holds, then this spec function will always
;; return true when applied to the appropriate R1CS variables.
(defun blake2s-mixing-0-4-8-12 (|main.in_v[0][0]| |main.in_v[0][1]| |main.in_v[0][2]| |main.in_v[0][3]|
                                                |main.in_v[0][4]| |main.in_v[0][5]| |main.in_v[0][6]| |main.in_v[0][7]|
                                                |main.in_v[0][8]| |main.in_v[0][9]| |main.in_v[0][10]| |main.in_v[0][11]|
                                                |main.in_v[0][12]| |main.in_v[0][13]| |main.in_v[0][14]| |main.in_v[0][15]|
                                                |main.in_v[0][16]| |main.in_v[0][17]| |main.in_v[0][18]| |main.in_v[0][19]|
                                                |main.in_v[0][20]| |main.in_v[0][21]| |main.in_v[0][22]| |main.in_v[0][23]|
                                                |main.in_v[0][24]| |main.in_v[0][25]| |main.in_v[0][26]| |main.in_v[0][27]|
                                                |main.in_v[0][28]| |main.in_v[0][29]| |main.in_v[0][30]| |main.in_v[0][31]|

                                                |main.in_v[1][0]| |main.in_v[1][1]| |main.in_v[1][2]| |main.in_v[1][3]|
                                                |main.in_v[1][4]| |main.in_v[1][5]| |main.in_v[1][6]| |main.in_v[1][7]|
                                                |main.in_v[1][8]| |main.in_v[1][9]| |main.in_v[1][10]| |main.in_v[1][11]|
                                                |main.in_v[1][12]| |main.in_v[1][13]| |main.in_v[1][14]| |main.in_v[1][15]|
                                                |main.in_v[1][16]| |main.in_v[1][17]| |main.in_v[1][18]| |main.in_v[1][19]|
                                                |main.in_v[1][20]| |main.in_v[1][21]| |main.in_v[1][22]| |main.in_v[1][23]|
                                                |main.in_v[1][24]| |main.in_v[1][25]| |main.in_v[1][26]| |main.in_v[1][27]|
                                                |main.in_v[1][28]| |main.in_v[1][29]| |main.in_v[1][30]| |main.in_v[1][31]|

                                                |main.in_v[2][0]| |main.in_v[2][1]| |main.in_v[2][2]| |main.in_v[2][3]|
                                                |main.in_v[2][4]| |main.in_v[2][5]| |main.in_v[2][6]| |main.in_v[2][7]|
                                                |main.in_v[2][8]| |main.in_v[2][9]| |main.in_v[2][10]| |main.in_v[2][11]|
                                                |main.in_v[2][12]| |main.in_v[2][13]| |main.in_v[2][14]| |main.in_v[2][15]|
                                                |main.in_v[2][16]| |main.in_v[2][17]| |main.in_v[2][18]| |main.in_v[2][19]|
                                                |main.in_v[2][20]| |main.in_v[2][21]| |main.in_v[2][22]| |main.in_v[2][23]|
                                                |main.in_v[2][24]| |main.in_v[2][25]| |main.in_v[2][26]| |main.in_v[2][27]|
                                                |main.in_v[2][28]| |main.in_v[2][29]| |main.in_v[2][30]| |main.in_v[2][31]|

                                                |main.in_v[3][0]| |main.in_v[3][1]| |main.in_v[3][2]| |main.in_v[3][3]|
                                                |main.in_v[3][4]| |main.in_v[3][5]| |main.in_v[3][6]| |main.in_v[3][7]|
                                                |main.in_v[3][8]| |main.in_v[3][9]| |main.in_v[3][10]| |main.in_v[3][11]|
                                                |main.in_v[3][12]| |main.in_v[3][13]| |main.in_v[3][14]| |main.in_v[3][15]|
                                                |main.in_v[3][16]| |main.in_v[3][17]| |main.in_v[3][18]| |main.in_v[3][19]|
                                                |main.in_v[3][20]| |main.in_v[3][21]| |main.in_v[3][22]| |main.in_v[3][23]|
                                                |main.in_v[3][24]| |main.in_v[3][25]| |main.in_v[3][26]| |main.in_v[3][27]|
                                                |main.in_v[3][28]| |main.in_v[3][29]| |main.in_v[3][30]| |main.in_v[3][31]|

                                                |main.in_v[4][0]| |main.in_v[4][1]| |main.in_v[4][2]| |main.in_v[4][3]|
                                                |main.in_v[4][4]| |main.in_v[4][5]| |main.in_v[4][6]| |main.in_v[4][7]|
                                                |main.in_v[4][8]| |main.in_v[4][9]| |main.in_v[4][10]| |main.in_v[4][11]|
                                                |main.in_v[4][12]| |main.in_v[4][13]| |main.in_v[4][14]| |main.in_v[4][15]|
                                                |main.in_v[4][16]| |main.in_v[4][17]| |main.in_v[4][18]| |main.in_v[4][19]|
                                                |main.in_v[4][20]| |main.in_v[4][21]| |main.in_v[4][22]| |main.in_v[4][23]|
                                                |main.in_v[4][24]| |main.in_v[4][25]| |main.in_v[4][26]| |main.in_v[4][27]|
                                                |main.in_v[4][28]| |main.in_v[4][29]| |main.in_v[4][30]| |main.in_v[4][31]|

                                                |main.in_v[5][0]| |main.in_v[5][1]| |main.in_v[5][2]| |main.in_v[5][3]|
                                                |main.in_v[5][4]| |main.in_v[5][5]| |main.in_v[5][6]| |main.in_v[5][7]|
                                                |main.in_v[5][8]| |main.in_v[5][9]| |main.in_v[5][10]| |main.in_v[5][11]|
                                                |main.in_v[5][12]| |main.in_v[5][13]| |main.in_v[5][14]| |main.in_v[5][15]|
                                                |main.in_v[5][16]| |main.in_v[5][17]| |main.in_v[5][18]| |main.in_v[5][19]|
                                                |main.in_v[5][20]| |main.in_v[5][21]| |main.in_v[5][22]| |main.in_v[5][23]|
                                                |main.in_v[5][24]| |main.in_v[5][25]| |main.in_v[5][26]| |main.in_v[5][27]|
                                                |main.in_v[5][28]| |main.in_v[5][29]| |main.in_v[5][30]| |main.in_v[5][31]|

                                                |main.in_v[6][0]| |main.in_v[6][1]| |main.in_v[6][2]| |main.in_v[6][3]|
                                                |main.in_v[6][4]| |main.in_v[6][5]| |main.in_v[6][6]| |main.in_v[6][7]|
                                                |main.in_v[6][8]| |main.in_v[6][9]| |main.in_v[6][10]| |main.in_v[6][11]|
                                                |main.in_v[6][12]| |main.in_v[6][13]| |main.in_v[6][14]| |main.in_v[6][15]|
                                                |main.in_v[6][16]| |main.in_v[6][17]| |main.in_v[6][18]| |main.in_v[6][19]|
                                                |main.in_v[6][20]| |main.in_v[6][21]| |main.in_v[6][22]| |main.in_v[6][23]|
                                                |main.in_v[6][24]| |main.in_v[6][25]| |main.in_v[6][26]| |main.in_v[6][27]|
                                                |main.in_v[6][28]| |main.in_v[6][29]| |main.in_v[6][30]| |main.in_v[6][31]|

                                                |main.in_v[7][0]| |main.in_v[7][1]| |main.in_v[7][2]| |main.in_v[7][3]|
                                                |main.in_v[7][4]| |main.in_v[7][5]| |main.in_v[7][6]| |main.in_v[7][7]|
                                                |main.in_v[7][8]| |main.in_v[7][9]| |main.in_v[7][10]| |main.in_v[7][11]|
                                                |main.in_v[7][12]| |main.in_v[7][13]| |main.in_v[7][14]| |main.in_v[7][15]|
                                                |main.in_v[7][16]| |main.in_v[7][17]| |main.in_v[7][18]| |main.in_v[7][19]|
                                                |main.in_v[7][20]| |main.in_v[7][21]| |main.in_v[7][22]| |main.in_v[7][23]|
                                                |main.in_v[7][24]| |main.in_v[7][25]| |main.in_v[7][26]| |main.in_v[7][27]|
                                                |main.in_v[7][28]| |main.in_v[7][29]| |main.in_v[7][30]| |main.in_v[7][31]|

                                                |main.in_v[8][0]| |main.in_v[8][1]| |main.in_v[8][2]| |main.in_v[8][3]|
                                                |main.in_v[8][4]| |main.in_v[8][5]| |main.in_v[8][6]| |main.in_v[8][7]|
                                                |main.in_v[8][8]| |main.in_v[8][9]| |main.in_v[8][10]| |main.in_v[8][11]|
                                                |main.in_v[8][12]| |main.in_v[8][13]| |main.in_v[8][14]| |main.in_v[8][15]|
                                                |main.in_v[8][16]| |main.in_v[8][17]| |main.in_v[8][18]| |main.in_v[8][19]|
                                                |main.in_v[8][20]| |main.in_v[8][21]| |main.in_v[8][22]| |main.in_v[8][23]|
                                                |main.in_v[8][24]| |main.in_v[8][25]| |main.in_v[8][26]| |main.in_v[8][27]|
                                                |main.in_v[8][28]| |main.in_v[8][29]| |main.in_v[8][30]| |main.in_v[8][31]|

                                                |main.in_v[9][0]| |main.in_v[9][1]| |main.in_v[9][2]| |main.in_v[9][3]|
                                                |main.in_v[9][4]| |main.in_v[9][5]| |main.in_v[9][6]| |main.in_v[9][7]|
                                                |main.in_v[9][8]| |main.in_v[9][9]| |main.in_v[9][10]| |main.in_v[9][11]|
                                                |main.in_v[9][12]| |main.in_v[9][13]| |main.in_v[9][14]| |main.in_v[9][15]|
                                                |main.in_v[9][16]| |main.in_v[9][17]| |main.in_v[9][18]| |main.in_v[9][19]|
                                                |main.in_v[9][20]| |main.in_v[9][21]| |main.in_v[9][22]| |main.in_v[9][23]|
                                                |main.in_v[9][24]| |main.in_v[9][25]| |main.in_v[9][26]| |main.in_v[9][27]|
                                                |main.in_v[9][28]| |main.in_v[9][29]| |main.in_v[9][30]| |main.in_v[9][31]|

                                                |main.in_v[10][0]| |main.in_v[10][1]| |main.in_v[10][2]| |main.in_v[10][3]|
                                                |main.in_v[10][4]| |main.in_v[10][5]| |main.in_v[10][6]| |main.in_v[10][7]|
                                                |main.in_v[10][8]| |main.in_v[10][9]| |main.in_v[10][10]| |main.in_v[10][11]|
                                                |main.in_v[10][12]| |main.in_v[10][13]| |main.in_v[10][14]| |main.in_v[10][15]|
                                                |main.in_v[10][16]| |main.in_v[10][17]| |main.in_v[10][18]| |main.in_v[10][19]|
                                                |main.in_v[10][20]| |main.in_v[10][21]| |main.in_v[10][22]| |main.in_v[10][23]|
                                                |main.in_v[10][24]| |main.in_v[10][25]| |main.in_v[10][26]| |main.in_v[10][27]|
                                                |main.in_v[10][28]| |main.in_v[10][29]| |main.in_v[10][30]| |main.in_v[10][31]|

                                                |main.in_v[11][0]| |main.in_v[11][1]| |main.in_v[11][2]| |main.in_v[11][3]|
                                                |main.in_v[11][4]| |main.in_v[11][5]| |main.in_v[11][6]| |main.in_v[11][7]|
                                                |main.in_v[11][8]| |main.in_v[11][9]| |main.in_v[11][10]| |main.in_v[11][11]|
                                                |main.in_v[11][12]| |main.in_v[11][13]| |main.in_v[11][14]| |main.in_v[11][15]|
                                                |main.in_v[11][16]| |main.in_v[11][17]| |main.in_v[11][18]| |main.in_v[11][19]|
                                                |main.in_v[11][20]| |main.in_v[11][21]| |main.in_v[11][22]| |main.in_v[11][23]|
                                                |main.in_v[11][24]| |main.in_v[11][25]| |main.in_v[11][26]| |main.in_v[11][27]|
                                                |main.in_v[11][28]| |main.in_v[11][29]| |main.in_v[11][30]| |main.in_v[11][31]|

                                                |main.in_v[12][0]| |main.in_v[12][1]| |main.in_v[12][2]| |main.in_v[12][3]|
                                                |main.in_v[12][4]| |main.in_v[12][5]| |main.in_v[12][6]| |main.in_v[12][7]|
                                                |main.in_v[12][8]| |main.in_v[12][9]| |main.in_v[12][10]| |main.in_v[12][11]|
                                                |main.in_v[12][12]| |main.in_v[12][13]| |main.in_v[12][14]| |main.in_v[12][15]|
                                                |main.in_v[12][16]| |main.in_v[12][17]| |main.in_v[12][18]| |main.in_v[12][19]|
                                                |main.in_v[12][20]| |main.in_v[12][21]| |main.in_v[12][22]| |main.in_v[12][23]|
                                                |main.in_v[12][24]| |main.in_v[12][25]| |main.in_v[12][26]| |main.in_v[12][27]|
                                                |main.in_v[12][28]| |main.in_v[12][29]| |main.in_v[12][30]| |main.in_v[12][31]|

                                                |main.in_v[13][0]| |main.in_v[13][1]| |main.in_v[13][2]| |main.in_v[13][3]|
                                                |main.in_v[13][4]| |main.in_v[13][5]| |main.in_v[13][6]| |main.in_v[13][7]|
                                                |main.in_v[13][8]| |main.in_v[13][9]| |main.in_v[13][10]| |main.in_v[13][11]|
                                                |main.in_v[13][12]| |main.in_v[13][13]| |main.in_v[13][14]| |main.in_v[13][15]|
                                                |main.in_v[13][16]| |main.in_v[13][17]| |main.in_v[13][18]| |main.in_v[13][19]|
                                                |main.in_v[13][20]| |main.in_v[13][21]| |main.in_v[13][22]| |main.in_v[13][23]|
                                                |main.in_v[13][24]| |main.in_v[13][25]| |main.in_v[13][26]| |main.in_v[13][27]|
                                                |main.in_v[13][28]| |main.in_v[13][29]| |main.in_v[13][30]| |main.in_v[13][31]|

                                                |main.in_v[14][0]| |main.in_v[14][1]| |main.in_v[14][2]| |main.in_v[14][3]|
                                                |main.in_v[14][4]| |main.in_v[14][5]| |main.in_v[14][6]| |main.in_v[14][7]|
                                                |main.in_v[14][8]| |main.in_v[14][9]| |main.in_v[14][10]| |main.in_v[14][11]|
                                                |main.in_v[14][12]| |main.in_v[14][13]| |main.in_v[14][14]| |main.in_v[14][15]|
                                                |main.in_v[14][16]| |main.in_v[14][17]| |main.in_v[14][18]| |main.in_v[14][19]|
                                                |main.in_v[14][20]| |main.in_v[14][21]| |main.in_v[14][22]| |main.in_v[14][23]|
                                                |main.in_v[14][24]| |main.in_v[14][25]| |main.in_v[14][26]| |main.in_v[14][27]|
                                                |main.in_v[14][28]| |main.in_v[14][29]| |main.in_v[14][30]| |main.in_v[14][31]|

                                                |main.in_v[15][0]| |main.in_v[15][1]| |main.in_v[15][2]| |main.in_v[15][3]|
                                                |main.in_v[15][4]| |main.in_v[15][5]| |main.in_v[15][6]| |main.in_v[15][7]|
                                                |main.in_v[15][8]| |main.in_v[15][9]| |main.in_v[15][10]| |main.in_v[15][11]|
                                                |main.in_v[15][12]| |main.in_v[15][13]| |main.in_v[15][14]| |main.in_v[15][15]|
                                                |main.in_v[15][16]| |main.in_v[15][17]| |main.in_v[15][18]| |main.in_v[15][19]|
                                                |main.in_v[15][20]| |main.in_v[15][21]| |main.in_v[15][22]| |main.in_v[15][23]|
                                                |main.in_v[15][24]| |main.in_v[15][25]| |main.in_v[15][26]| |main.in_v[15][27]|
                                                |main.in_v[15][28]| |main.in_v[15][29]| |main.in_v[15][30]| |main.in_v[15][31]|

                                                |main.x[0]| |main.x[1]| |main.x[2]| |main.x[3]|
                                                |main.x[4]| |main.x[5]| |main.x[6]| |main.x[7]|
                                                |main.x[8]| |main.x[9]| |main.x[10]| |main.x[11]|
                                                |main.x[12]| |main.x[13]| |main.x[14]| |main.x[15]|
                                                |main.x[16]| |main.x[17]| |main.x[18]| |main.x[19]|
                                                |main.x[20]| |main.x[21]| |main.x[22]| |main.x[23]|
                                                |main.x[24]| |main.x[25]| |main.x[26]| |main.x[27]|
                                                |main.x[28]| |main.x[29]| |main.x[30]| |main.x[31]|

                                                |main.y[0]| |main.y[1]| |main.y[2]| |main.y[3]|
                                                |main.y[4]| |main.y[5]| |main.y[6]| |main.y[7]|
                                                |main.y[8]| |main.y[9]| |main.y[10]| |main.y[11]|
                                                |main.y[12]| |main.y[13]| |main.y[14]| |main.y[15]|
                                                |main.y[16]| |main.y[17]| |main.y[18]| |main.y[19]|
                                                |main.y[20]| |main.y[21]| |main.y[22]| |main.y[23]|
                                                |main.y[24]| |main.y[25]| |main.y[26]| |main.y[27]|
                                                |main.y[28]| |main.y[29]| |main.y[30]| |main.y[31]|

                                                |main.out_v[0][0]| |main.out_v[0][1]| |main.out_v[0][2]| |main.out_v[0][3]|
                                                |main.out_v[0][4]| |main.out_v[0][5]| |main.out_v[0][6]| |main.out_v[0][7]|
                                                |main.out_v[0][8]| |main.out_v[0][9]| |main.out_v[0][10]| |main.out_v[0][11]|
                                                |main.out_v[0][12]| |main.out_v[0][13]| |main.out_v[0][14]| |main.out_v[0][15]|
                                                |main.out_v[0][16]| |main.out_v[0][17]| |main.out_v[0][18]| |main.out_v[0][19]|
                                                |main.out_v[0][20]| |main.out_v[0][21]| |main.out_v[0][22]| |main.out_v[0][23]|
                                                |main.out_v[0][24]| |main.out_v[0][25]| |main.out_v[0][26]| |main.out_v[0][27]|
                                                |main.out_v[0][28]| |main.out_v[0][29]| |main.out_v[0][30]| |main.out_v[0][31]|

                                                |main.out_v[1][0]| |main.out_v[1][1]| |main.out_v[1][2]| |main.out_v[1][3]|
                                                |main.out_v[1][4]| |main.out_v[1][5]| |main.out_v[1][6]| |main.out_v[1][7]|
                                                |main.out_v[1][8]| |main.out_v[1][9]| |main.out_v[1][10]| |main.out_v[1][11]|
                                                |main.out_v[1][12]| |main.out_v[1][13]| |main.out_v[1][14]| |main.out_v[1][15]|
                                                |main.out_v[1][16]| |main.out_v[1][17]| |main.out_v[1][18]| |main.out_v[1][19]|
                                                |main.out_v[1][20]| |main.out_v[1][21]| |main.out_v[1][22]| |main.out_v[1][23]|
                                                |main.out_v[1][24]| |main.out_v[1][25]| |main.out_v[1][26]| |main.out_v[1][27]|
                                                |main.out_v[1][28]| |main.out_v[1][29]| |main.out_v[1][30]| |main.out_v[1][31]|

                                                |main.out_v[2][0]| |main.out_v[2][1]| |main.out_v[2][2]| |main.out_v[2][3]|
                                                |main.out_v[2][4]| |main.out_v[2][5]| |main.out_v[2][6]| |main.out_v[2][7]|
                                                |main.out_v[2][8]| |main.out_v[2][9]| |main.out_v[2][10]| |main.out_v[2][11]|
                                                |main.out_v[2][12]| |main.out_v[2][13]| |main.out_v[2][14]| |main.out_v[2][15]|
                                                |main.out_v[2][16]| |main.out_v[2][17]| |main.out_v[2][18]| |main.out_v[2][19]|
                                                |main.out_v[2][20]| |main.out_v[2][21]| |main.out_v[2][22]| |main.out_v[2][23]|
                                                |main.out_v[2][24]| |main.out_v[2][25]| |main.out_v[2][26]| |main.out_v[2][27]|
                                                |main.out_v[2][28]| |main.out_v[2][29]| |main.out_v[2][30]| |main.out_v[2][31]|

                                                |main.out_v[3][0]| |main.out_v[3][1]| |main.out_v[3][2]| |main.out_v[3][3]|
                                                |main.out_v[3][4]| |main.out_v[3][5]| |main.out_v[3][6]| |main.out_v[3][7]|
                                                |main.out_v[3][8]| |main.out_v[3][9]| |main.out_v[3][10]| |main.out_v[3][11]|
                                                |main.out_v[3][12]| |main.out_v[3][13]| |main.out_v[3][14]| |main.out_v[3][15]|
                                                |main.out_v[3][16]| |main.out_v[3][17]| |main.out_v[3][18]| |main.out_v[3][19]|
                                                |main.out_v[3][20]| |main.out_v[3][21]| |main.out_v[3][22]| |main.out_v[3][23]|
                                                |main.out_v[3][24]| |main.out_v[3][25]| |main.out_v[3][26]| |main.out_v[3][27]|
                                                |main.out_v[3][28]| |main.out_v[3][29]| |main.out_v[3][30]| |main.out_v[3][31]|

                                                |main.out_v[4][0]| |main.out_v[4][1]| |main.out_v[4][2]| |main.out_v[4][3]|
                                                |main.out_v[4][4]| |main.out_v[4][5]| |main.out_v[4][6]| |main.out_v[4][7]|
                                                |main.out_v[4][8]| |main.out_v[4][9]| |main.out_v[4][10]| |main.out_v[4][11]|
                                                |main.out_v[4][12]| |main.out_v[4][13]| |main.out_v[4][14]| |main.out_v[4][15]|
                                                |main.out_v[4][16]| |main.out_v[4][17]| |main.out_v[4][18]| |main.out_v[4][19]|
                                                |main.out_v[4][20]| |main.out_v[4][21]| |main.out_v[4][22]| |main.out_v[4][23]|
                                                |main.out_v[4][24]| |main.out_v[4][25]| |main.out_v[4][26]| |main.out_v[4][27]|
                                                |main.out_v[4][28]| |main.out_v[4][29]| |main.out_v[4][30]| |main.out_v[4][31]|

                                                |main.out_v[5][0]| |main.out_v[5][1]| |main.out_v[5][2]| |main.out_v[5][3]|
                                                |main.out_v[5][4]| |main.out_v[5][5]| |main.out_v[5][6]| |main.out_v[5][7]|
                                                |main.out_v[5][8]| |main.out_v[5][9]| |main.out_v[5][10]| |main.out_v[5][11]|
                                                |main.out_v[5][12]| |main.out_v[5][13]| |main.out_v[5][14]| |main.out_v[5][15]|
                                                |main.out_v[5][16]| |main.out_v[5][17]| |main.out_v[5][18]| |main.out_v[5][19]|
                                                |main.out_v[5][20]| |main.out_v[5][21]| |main.out_v[5][22]| |main.out_v[5][23]|
                                                |main.out_v[5][24]| |main.out_v[5][25]| |main.out_v[5][26]| |main.out_v[5][27]|
                                                |main.out_v[5][28]| |main.out_v[5][29]| |main.out_v[5][30]| |main.out_v[5][31]|

                                                |main.out_v[6][0]| |main.out_v[6][1]| |main.out_v[6][2]| |main.out_v[6][3]|
                                                |main.out_v[6][4]| |main.out_v[6][5]| |main.out_v[6][6]| |main.out_v[6][7]|
                                                |main.out_v[6][8]| |main.out_v[6][9]| |main.out_v[6][10]| |main.out_v[6][11]|
                                                |main.out_v[6][12]| |main.out_v[6][13]| |main.out_v[6][14]| |main.out_v[6][15]|
                                                |main.out_v[6][16]| |main.out_v[6][17]| |main.out_v[6][18]| |main.out_v[6][19]|
                                                |main.out_v[6][20]| |main.out_v[6][21]| |main.out_v[6][22]| |main.out_v[6][23]|
                                                |main.out_v[6][24]| |main.out_v[6][25]| |main.out_v[6][26]| |main.out_v[6][27]|
                                                |main.out_v[6][28]| |main.out_v[6][29]| |main.out_v[6][30]| |main.out_v[6][31]|

                                                |main.out_v[7][0]| |main.out_v[7][1]| |main.out_v[7][2]| |main.out_v[7][3]|
                                                |main.out_v[7][4]| |main.out_v[7][5]| |main.out_v[7][6]| |main.out_v[7][7]|
                                                |main.out_v[7][8]| |main.out_v[7][9]| |main.out_v[7][10]| |main.out_v[7][11]|
                                                |main.out_v[7][12]| |main.out_v[7][13]| |main.out_v[7][14]| |main.out_v[7][15]|
                                                |main.out_v[7][16]| |main.out_v[7][17]| |main.out_v[7][18]| |main.out_v[7][19]|
                                                |main.out_v[7][20]| |main.out_v[7][21]| |main.out_v[7][22]| |main.out_v[7][23]|
                                                |main.out_v[7][24]| |main.out_v[7][25]| |main.out_v[7][26]| |main.out_v[7][27]|
                                                |main.out_v[7][28]| |main.out_v[7][29]| |main.out_v[7][30]| |main.out_v[7][31]|

                                                |main.out_v[8][0]| |main.out_v[8][1]| |main.out_v[8][2]| |main.out_v[8][3]|
                                                |main.out_v[8][4]| |main.out_v[8][5]| |main.out_v[8][6]| |main.out_v[8][7]|
                                                |main.out_v[8][8]| |main.out_v[8][9]| |main.out_v[8][10]| |main.out_v[8][11]|
                                                |main.out_v[8][12]| |main.out_v[8][13]| |main.out_v[8][14]| |main.out_v[8][15]|
                                                |main.out_v[8][16]| |main.out_v[8][17]| |main.out_v[8][18]| |main.out_v[8][19]|
                                                |main.out_v[8][20]| |main.out_v[8][21]| |main.out_v[8][22]| |main.out_v[8][23]|
                                                |main.out_v[8][24]| |main.out_v[8][25]| |main.out_v[8][26]| |main.out_v[8][27]|
                                                |main.out_v[8][28]| |main.out_v[8][29]| |main.out_v[8][30]| |main.out_v[8][31]|

                                                |main.out_v[9][0]| |main.out_v[9][1]| |main.out_v[9][2]| |main.out_v[9][3]|
                                                |main.out_v[9][4]| |main.out_v[9][5]| |main.out_v[9][6]| |main.out_v[9][7]|
                                                |main.out_v[9][8]| |main.out_v[9][9]| |main.out_v[9][10]| |main.out_v[9][11]|
                                                |main.out_v[9][12]| |main.out_v[9][13]| |main.out_v[9][14]| |main.out_v[9][15]|
                                                |main.out_v[9][16]| |main.out_v[9][17]| |main.out_v[9][18]| |main.out_v[9][19]|
                                                |main.out_v[9][20]| |main.out_v[9][21]| |main.out_v[9][22]| |main.out_v[9][23]|
                                                |main.out_v[9][24]| |main.out_v[9][25]| |main.out_v[9][26]| |main.out_v[9][27]|
                                                |main.out_v[9][28]| |main.out_v[9][29]| |main.out_v[9][30]| |main.out_v[9][31]|

                                                |main.out_v[10][0]| |main.out_v[10][1]| |main.out_v[10][2]| |main.out_v[10][3]|
                                                |main.out_v[10][4]| |main.out_v[10][5]| |main.out_v[10][6]| |main.out_v[10][7]|
                                                |main.out_v[10][8]| |main.out_v[10][9]| |main.out_v[10][10]| |main.out_v[10][11]|
                                                |main.out_v[10][12]| |main.out_v[10][13]| |main.out_v[10][14]| |main.out_v[10][15]|
                                                |main.out_v[10][16]| |main.out_v[10][17]| |main.out_v[10][18]| |main.out_v[10][19]|
                                                |main.out_v[10][20]| |main.out_v[10][21]| |main.out_v[10][22]| |main.out_v[10][23]|
                                                |main.out_v[10][24]| |main.out_v[10][25]| |main.out_v[10][26]| |main.out_v[10][27]|
                                                |main.out_v[10][28]| |main.out_v[10][29]| |main.out_v[10][30]| |main.out_v[10][31]|

                                                |main.out_v[11][0]| |main.out_v[11][1]| |main.out_v[11][2]| |main.out_v[11][3]|
                                                |main.out_v[11][4]| |main.out_v[11][5]| |main.out_v[11][6]| |main.out_v[11][7]|
                                                |main.out_v[11][8]| |main.out_v[11][9]| |main.out_v[11][10]| |main.out_v[11][11]|
                                                |main.out_v[11][12]| |main.out_v[11][13]| |main.out_v[11][14]| |main.out_v[11][15]|
                                                |main.out_v[11][16]| |main.out_v[11][17]| |main.out_v[11][18]| |main.out_v[11][19]|
                                                |main.out_v[11][20]| |main.out_v[11][21]| |main.out_v[11][22]| |main.out_v[11][23]|
                                                |main.out_v[11][24]| |main.out_v[11][25]| |main.out_v[11][26]| |main.out_v[11][27]|
                                                |main.out_v[11][28]| |main.out_v[11][29]| |main.out_v[11][30]| |main.out_v[11][31]|

                                                |main.out_v[12][0]| |main.out_v[12][1]| |main.out_v[12][2]| |main.out_v[12][3]|
                                                |main.out_v[12][4]| |main.out_v[12][5]| |main.out_v[12][6]| |main.out_v[12][7]|
                                                |main.out_v[12][8]| |main.out_v[12][9]| |main.out_v[12][10]| |main.out_v[12][11]|
                                                |main.out_v[12][12]| |main.out_v[12][13]| |main.out_v[12][14]| |main.out_v[12][15]|
                                                |main.out_v[12][16]| |main.out_v[12][17]| |main.out_v[12][18]| |main.out_v[12][19]|
                                                |main.out_v[12][20]| |main.out_v[12][21]| |main.out_v[12][22]| |main.out_v[12][23]|
                                                |main.out_v[12][24]| |main.out_v[12][25]| |main.out_v[12][26]| |main.out_v[12][27]|
                                                |main.out_v[12][28]| |main.out_v[12][29]| |main.out_v[12][30]| |main.out_v[12][31]|

                                                |main.out_v[13][0]| |main.out_v[13][1]| |main.out_v[13][2]| |main.out_v[13][3]|
                                                |main.out_v[13][4]| |main.out_v[13][5]| |main.out_v[13][6]| |main.out_v[13][7]|
                                                |main.out_v[13][8]| |main.out_v[13][9]| |main.out_v[13][10]| |main.out_v[13][11]|
                                                |main.out_v[13][12]| |main.out_v[13][13]| |main.out_v[13][14]| |main.out_v[13][15]|
                                                |main.out_v[13][16]| |main.out_v[13][17]| |main.out_v[13][18]| |main.out_v[13][19]|
                                                |main.out_v[13][20]| |main.out_v[13][21]| |main.out_v[13][22]| |main.out_v[13][23]|
                                                |main.out_v[13][24]| |main.out_v[13][25]| |main.out_v[13][26]| |main.out_v[13][27]|
                                                |main.out_v[13][28]| |main.out_v[13][29]| |main.out_v[13][30]| |main.out_v[13][31]|

                                                |main.out_v[14][0]| |main.out_v[14][1]| |main.out_v[14][2]| |main.out_v[14][3]|
                                                |main.out_v[14][4]| |main.out_v[14][5]| |main.out_v[14][6]| |main.out_v[14][7]|
                                                |main.out_v[14][8]| |main.out_v[14][9]| |main.out_v[14][10]| |main.out_v[14][11]|
                                                |main.out_v[14][12]| |main.out_v[14][13]| |main.out_v[14][14]| |main.out_v[14][15]|
                                                |main.out_v[14][16]| |main.out_v[14][17]| |main.out_v[14][18]| |main.out_v[14][19]|
                                                |main.out_v[14][20]| |main.out_v[14][21]| |main.out_v[14][22]| |main.out_v[14][23]|
                                                |main.out_v[14][24]| |main.out_v[14][25]| |main.out_v[14][26]| |main.out_v[14][27]|
                                                |main.out_v[14][28]| |main.out_v[14][29]| |main.out_v[14][30]| |main.out_v[14][31]|

                                                |main.out_v[15][0]| |main.out_v[15][1]| |main.out_v[15][2]| |main.out_v[15][3]|
                                                |main.out_v[15][4]| |main.out_v[15][5]| |main.out_v[15][6]| |main.out_v[15][7]|
                                                |main.out_v[15][8]| |main.out_v[15][9]| |main.out_v[15][10]| |main.out_v[15][11]|
                                                |main.out_v[15][12]| |main.out_v[15][13]| |main.out_v[15][14]| |main.out_v[15][15]|
                                                |main.out_v[15][16]| |main.out_v[15][17]| |main.out_v[15][18]| |main.out_v[15][19]|
                                                |main.out_v[15][20]| |main.out_v[15][21]| |main.out_v[15][22]| |main.out_v[15][23]|
                                                |main.out_v[15][24]| |main.out_v[15][25]| |main.out_v[15][26]| |main.out_v[15][27]|
                                                |main.out_v[15][28]| |main.out_v[15][29]| |main.out_v[15][30]| |main.out_v[15][31]|)
  (equal (blake::g (list (pack-blake-word |main.in_v[0][0]| |main.in_v[0][1]| |main.in_v[0][2]| |main.in_v[0][3]|
                                          |main.in_v[0][4]| |main.in_v[0][5]| |main.in_v[0][6]| |main.in_v[0][7]|
                                          |main.in_v[0][8]| |main.in_v[0][9]| |main.in_v[0][10]| |main.in_v[0][11]|
                                          |main.in_v[0][12]| |main.in_v[0][13]| |main.in_v[0][14]| |main.in_v[0][15]|
                                          |main.in_v[0][16]| |main.in_v[0][17]| |main.in_v[0][18]| |main.in_v[0][19]|
                                          |main.in_v[0][20]| |main.in_v[0][21]| |main.in_v[0][22]| |main.in_v[0][23]|
                                          |main.in_v[0][24]| |main.in_v[0][25]| |main.in_v[0][26]| |main.in_v[0][27]|
                                          |main.in_v[0][28]| |main.in_v[0][29]| |main.in_v[0][30]| |main.in_v[0][31]|)

                         (pack-blake-word |main.in_v[1][0]| |main.in_v[1][1]| |main.in_v[1][2]| |main.in_v[1][3]|
                                          |main.in_v[1][4]| |main.in_v[1][5]| |main.in_v[1][6]| |main.in_v[1][7]|
                                          |main.in_v[1][8]| |main.in_v[1][9]| |main.in_v[1][10]| |main.in_v[1][11]|
                                          |main.in_v[1][12]| |main.in_v[1][13]| |main.in_v[1][14]| |main.in_v[1][15]|
                                          |main.in_v[1][16]| |main.in_v[1][17]| |main.in_v[1][18]| |main.in_v[1][19]|
                                          |main.in_v[1][20]| |main.in_v[1][21]| |main.in_v[1][22]| |main.in_v[1][23]|
                                          |main.in_v[1][24]| |main.in_v[1][25]| |main.in_v[1][26]| |main.in_v[1][27]|
                                          |main.in_v[1][28]| |main.in_v[1][29]| |main.in_v[1][30]| |main.in_v[1][31]|)

                         (pack-blake-word |main.in_v[2][0]| |main.in_v[2][1]| |main.in_v[2][2]| |main.in_v[2][3]|
                                          |main.in_v[2][4]| |main.in_v[2][5]| |main.in_v[2][6]| |main.in_v[2][7]|
                                          |main.in_v[2][8]| |main.in_v[2][9]| |main.in_v[2][10]| |main.in_v[2][11]|
                                          |main.in_v[2][12]| |main.in_v[2][13]| |main.in_v[2][14]| |main.in_v[2][15]|
                                          |main.in_v[2][16]| |main.in_v[2][17]| |main.in_v[2][18]| |main.in_v[2][19]|
                                          |main.in_v[2][20]| |main.in_v[2][21]| |main.in_v[2][22]| |main.in_v[2][23]|
                                          |main.in_v[2][24]| |main.in_v[2][25]| |main.in_v[2][26]| |main.in_v[2][27]|
                                          |main.in_v[2][28]| |main.in_v[2][29]| |main.in_v[2][30]| |main.in_v[2][31]|)

                         (pack-blake-word |main.in_v[3][0]| |main.in_v[3][1]| |main.in_v[3][2]| |main.in_v[3][3]|
                                          |main.in_v[3][4]| |main.in_v[3][5]| |main.in_v[3][6]| |main.in_v[3][7]|
                                          |main.in_v[3][8]| |main.in_v[3][9]| |main.in_v[3][10]| |main.in_v[3][11]|
                                          |main.in_v[3][12]| |main.in_v[3][13]| |main.in_v[3][14]| |main.in_v[3][15]|
                                          |main.in_v[3][16]| |main.in_v[3][17]| |main.in_v[3][18]| |main.in_v[3][19]|
                                          |main.in_v[3][20]| |main.in_v[3][21]| |main.in_v[3][22]| |main.in_v[3][23]|
                                          |main.in_v[3][24]| |main.in_v[3][25]| |main.in_v[3][26]| |main.in_v[3][27]|
                                          |main.in_v[3][28]| |main.in_v[3][29]| |main.in_v[3][30]| |main.in_v[3][31]|)

                         (pack-blake-word |main.in_v[4][0]| |main.in_v[4][1]| |main.in_v[4][2]| |main.in_v[4][3]|
                                          |main.in_v[4][4]| |main.in_v[4][5]| |main.in_v[4][6]| |main.in_v[4][7]|
                                          |main.in_v[4][8]| |main.in_v[4][9]| |main.in_v[4][10]| |main.in_v[4][11]|
                                          |main.in_v[4][12]| |main.in_v[4][13]| |main.in_v[4][14]| |main.in_v[4][15]|
                                          |main.in_v[4][16]| |main.in_v[4][17]| |main.in_v[4][18]| |main.in_v[4][19]|
                                          |main.in_v[4][20]| |main.in_v[4][21]| |main.in_v[4][22]| |main.in_v[4][23]|
                                          |main.in_v[4][24]| |main.in_v[4][25]| |main.in_v[4][26]| |main.in_v[4][27]|
                                          |main.in_v[4][28]| |main.in_v[4][29]| |main.in_v[4][30]| |main.in_v[4][31]|)

                         (pack-blake-word |main.in_v[5][0]| |main.in_v[5][1]| |main.in_v[5][2]| |main.in_v[5][3]|
                                          |main.in_v[5][4]| |main.in_v[5][5]| |main.in_v[5][6]| |main.in_v[5][7]|
                                          |main.in_v[5][8]| |main.in_v[5][9]| |main.in_v[5][10]| |main.in_v[5][11]|
                                          |main.in_v[5][12]| |main.in_v[5][13]| |main.in_v[5][14]| |main.in_v[5][15]|
                                          |main.in_v[5][16]| |main.in_v[5][17]| |main.in_v[5][18]| |main.in_v[5][19]|
                                          |main.in_v[5][20]| |main.in_v[5][21]| |main.in_v[5][22]| |main.in_v[5][23]|
                                          |main.in_v[5][24]| |main.in_v[5][25]| |main.in_v[5][26]| |main.in_v[5][27]|
                                          |main.in_v[5][28]| |main.in_v[5][29]| |main.in_v[5][30]| |main.in_v[5][31]|)

                         (pack-blake-word |main.in_v[6][0]| |main.in_v[6][1]| |main.in_v[6][2]| |main.in_v[6][3]|
                                          |main.in_v[6][4]| |main.in_v[6][5]| |main.in_v[6][6]| |main.in_v[6][7]|
                                          |main.in_v[6][8]| |main.in_v[6][9]| |main.in_v[6][10]| |main.in_v[6][11]|
                                          |main.in_v[6][12]| |main.in_v[6][13]| |main.in_v[6][14]| |main.in_v[6][15]|
                                          |main.in_v[6][16]| |main.in_v[6][17]| |main.in_v[6][18]| |main.in_v[6][19]|
                                          |main.in_v[6][20]| |main.in_v[6][21]| |main.in_v[6][22]| |main.in_v[6][23]|
                                          |main.in_v[6][24]| |main.in_v[6][25]| |main.in_v[6][26]| |main.in_v[6][27]|
                                          |main.in_v[6][28]| |main.in_v[6][29]| |main.in_v[6][30]| |main.in_v[6][31]|)

                         (pack-blake-word |main.in_v[7][0]| |main.in_v[7][1]| |main.in_v[7][2]| |main.in_v[7][3]|
                                          |main.in_v[7][4]| |main.in_v[7][5]| |main.in_v[7][6]| |main.in_v[7][7]|
                                          |main.in_v[7][8]| |main.in_v[7][9]| |main.in_v[7][10]| |main.in_v[7][11]|
                                          |main.in_v[7][12]| |main.in_v[7][13]| |main.in_v[7][14]| |main.in_v[7][15]|
                                          |main.in_v[7][16]| |main.in_v[7][17]| |main.in_v[7][18]| |main.in_v[7][19]|
                                          |main.in_v[7][20]| |main.in_v[7][21]| |main.in_v[7][22]| |main.in_v[7][23]|
                                          |main.in_v[7][24]| |main.in_v[7][25]| |main.in_v[7][26]| |main.in_v[7][27]|
                                          |main.in_v[7][28]| |main.in_v[7][29]| |main.in_v[7][30]| |main.in_v[7][31]|)

                         (pack-blake-word |main.in_v[8][0]| |main.in_v[8][1]| |main.in_v[8][2]| |main.in_v[8][3]|
                                          |main.in_v[8][4]| |main.in_v[8][5]| |main.in_v[8][6]| |main.in_v[8][7]|
                                          |main.in_v[8][8]| |main.in_v[8][9]| |main.in_v[8][10]| |main.in_v[8][11]|
                                          |main.in_v[8][12]| |main.in_v[8][13]| |main.in_v[8][14]| |main.in_v[8][15]|
                                          |main.in_v[8][16]| |main.in_v[8][17]| |main.in_v[8][18]| |main.in_v[8][19]|
                                          |main.in_v[8][20]| |main.in_v[8][21]| |main.in_v[8][22]| |main.in_v[8][23]|
                                          |main.in_v[8][24]| |main.in_v[8][25]| |main.in_v[8][26]| |main.in_v[8][27]|
                                          |main.in_v[8][28]| |main.in_v[8][29]| |main.in_v[8][30]| |main.in_v[8][31]|)

                         (pack-blake-word |main.in_v[9][0]| |main.in_v[9][1]| |main.in_v[9][2]| |main.in_v[9][3]|
                                          |main.in_v[9][4]| |main.in_v[9][5]| |main.in_v[9][6]| |main.in_v[9][7]|
                                          |main.in_v[9][8]| |main.in_v[9][9]| |main.in_v[9][10]| |main.in_v[9][11]|
                                          |main.in_v[9][12]| |main.in_v[9][13]| |main.in_v[9][14]| |main.in_v[9][15]|
                                          |main.in_v[9][16]| |main.in_v[9][17]| |main.in_v[9][18]| |main.in_v[9][19]|
                                          |main.in_v[9][20]| |main.in_v[9][21]| |main.in_v[9][22]| |main.in_v[9][23]|
                                          |main.in_v[9][24]| |main.in_v[9][25]| |main.in_v[9][26]| |main.in_v[9][27]|
                                          |main.in_v[9][28]| |main.in_v[9][29]| |main.in_v[9][30]| |main.in_v[9][31]|)

                         (pack-blake-word |main.in_v[10][0]| |main.in_v[10][1]| |main.in_v[10][2]| |main.in_v[10][3]|
                                          |main.in_v[10][4]| |main.in_v[10][5]| |main.in_v[10][6]| |main.in_v[10][7]|
                                          |main.in_v[10][8]| |main.in_v[10][9]| |main.in_v[10][10]| |main.in_v[10][11]|
                                          |main.in_v[10][12]| |main.in_v[10][13]| |main.in_v[10][14]| |main.in_v[10][15]|
                                          |main.in_v[10][16]| |main.in_v[10][17]| |main.in_v[10][18]| |main.in_v[10][19]|
                                          |main.in_v[10][20]| |main.in_v[10][21]| |main.in_v[10][22]| |main.in_v[10][23]|
                                          |main.in_v[10][24]| |main.in_v[10][25]| |main.in_v[10][26]| |main.in_v[10][27]|
                                          |main.in_v[10][28]| |main.in_v[10][29]| |main.in_v[10][30]| |main.in_v[10][31]|)

                         (pack-blake-word |main.in_v[11][0]| |main.in_v[11][1]| |main.in_v[11][2]| |main.in_v[11][3]|
                                          |main.in_v[11][4]| |main.in_v[11][5]| |main.in_v[11][6]| |main.in_v[11][7]|
                                          |main.in_v[11][8]| |main.in_v[11][9]| |main.in_v[11][10]| |main.in_v[11][11]|
                                          |main.in_v[11][12]| |main.in_v[11][13]| |main.in_v[11][14]| |main.in_v[11][15]|
                                          |main.in_v[11][16]| |main.in_v[11][17]| |main.in_v[11][18]| |main.in_v[11][19]|
                                          |main.in_v[11][20]| |main.in_v[11][21]| |main.in_v[11][22]| |main.in_v[11][23]|
                                          |main.in_v[11][24]| |main.in_v[11][25]| |main.in_v[11][26]| |main.in_v[11][27]|
                                          |main.in_v[11][28]| |main.in_v[11][29]| |main.in_v[11][30]| |main.in_v[11][31]|)

                         (pack-blake-word |main.in_v[12][0]| |main.in_v[12][1]| |main.in_v[12][2]| |main.in_v[12][3]|
                                          |main.in_v[12][4]| |main.in_v[12][5]| |main.in_v[12][6]| |main.in_v[12][7]|
                                          |main.in_v[12][8]| |main.in_v[12][9]| |main.in_v[12][10]| |main.in_v[12][11]|
                                          |main.in_v[12][12]| |main.in_v[12][13]| |main.in_v[12][14]| |main.in_v[12][15]|
                                          |main.in_v[12][16]| |main.in_v[12][17]| |main.in_v[12][18]| |main.in_v[12][19]|
                                          |main.in_v[12][20]| |main.in_v[12][21]| |main.in_v[12][22]| |main.in_v[12][23]|
                                          |main.in_v[12][24]| |main.in_v[12][25]| |main.in_v[12][26]| |main.in_v[12][27]|
                                          |main.in_v[12][28]| |main.in_v[12][29]| |main.in_v[12][30]| |main.in_v[12][31]|)

                         (pack-blake-word |main.in_v[13][0]| |main.in_v[13][1]| |main.in_v[13][2]| |main.in_v[13][3]|
                                          |main.in_v[13][4]| |main.in_v[13][5]| |main.in_v[13][6]| |main.in_v[13][7]|
                                          |main.in_v[13][8]| |main.in_v[13][9]| |main.in_v[13][10]| |main.in_v[13][11]|
                                          |main.in_v[13][12]| |main.in_v[13][13]| |main.in_v[13][14]| |main.in_v[13][15]|
                                          |main.in_v[13][16]| |main.in_v[13][17]| |main.in_v[13][18]| |main.in_v[13][19]|
                                          |main.in_v[13][20]| |main.in_v[13][21]| |main.in_v[13][22]| |main.in_v[13][23]|
                                          |main.in_v[13][24]| |main.in_v[13][25]| |main.in_v[13][26]| |main.in_v[13][27]|
                                          |main.in_v[13][28]| |main.in_v[13][29]| |main.in_v[13][30]| |main.in_v[13][31]|)

                         (pack-blake-word |main.in_v[14][0]| |main.in_v[14][1]| |main.in_v[14][2]| |main.in_v[14][3]|
                                          |main.in_v[14][4]| |main.in_v[14][5]| |main.in_v[14][6]| |main.in_v[14][7]|
                                          |main.in_v[14][8]| |main.in_v[14][9]| |main.in_v[14][10]| |main.in_v[14][11]|
                                          |main.in_v[14][12]| |main.in_v[14][13]| |main.in_v[14][14]| |main.in_v[14][15]|
                                          |main.in_v[14][16]| |main.in_v[14][17]| |main.in_v[14][18]| |main.in_v[14][19]|
                                          |main.in_v[14][20]| |main.in_v[14][21]| |main.in_v[14][22]| |main.in_v[14][23]|
                                          |main.in_v[14][24]| |main.in_v[14][25]| |main.in_v[14][26]| |main.in_v[14][27]|
                                          |main.in_v[14][28]| |main.in_v[14][29]| |main.in_v[14][30]| |main.in_v[14][31]|)

                         (pack-blake-word |main.in_v[15][0]| |main.in_v[15][1]| |main.in_v[15][2]| |main.in_v[15][3]|
                                          |main.in_v[15][4]| |main.in_v[15][5]| |main.in_v[15][6]| |main.in_v[15][7]|
                                          |main.in_v[15][8]| |main.in_v[15][9]| |main.in_v[15][10]| |main.in_v[15][11]|
                                          |main.in_v[15][12]| |main.in_v[15][13]| |main.in_v[15][14]| |main.in_v[15][15]|
                                          |main.in_v[15][16]| |main.in_v[15][17]| |main.in_v[15][18]| |main.in_v[15][19]|
                                          |main.in_v[15][20]| |main.in_v[15][21]| |main.in_v[15][22]| |main.in_v[15][23]|
                                          |main.in_v[15][24]| |main.in_v[15][25]| |main.in_v[15][26]| |main.in_v[15][27]|
                                          |main.in_v[15][28]| |main.in_v[15][29]| |main.in_v[15][30]| |main.in_v[15][31]|)
                         ) ; end of v
                   0
                   4
                   8
                   12
                   (pack-blake-word |main.x[0]| |main.x[1]| |main.x[2]| |main.x[3]|
                                    |main.x[4]| |main.x[5]| |main.x[6]| |main.x[7]|
                                    |main.x[8]| |main.x[9]| |main.x[10]| |main.x[11]|
                                    |main.x[12]| |main.x[13]| |main.x[14]| |main.x[15]|
                                    |main.x[16]| |main.x[17]| |main.x[18]| |main.x[19]|
                                    |main.x[20]| |main.x[21]| |main.x[22]| |main.x[23]|
                                    |main.x[24]| |main.x[25]| |main.x[26]| |main.x[27]|
                                    |main.x[28]| |main.x[29]| |main.x[30]| |main.x[31]|)

                   (pack-blake-word |main.y[0]| |main.y[1]| |main.y[2]| |main.y[3]|
                                    |main.y[4]| |main.y[5]| |main.y[6]| |main.y[7]|
                                    |main.y[8]| |main.y[9]| |main.y[10]| |main.y[11]|
                                    |main.y[12]| |main.y[13]| |main.y[14]| |main.y[15]|
                                    |main.y[16]| |main.y[17]| |main.y[18]| |main.y[19]|
                                    |main.y[20]| |main.y[21]| |main.y[22]| |main.y[23]|
                                    |main.y[24]| |main.y[25]| |main.y[26]| |main.y[27]|
                                    |main.y[28]| |main.y[29]| |main.y[30]| |main.y[31]|))
         (list (pack-blake-word |main.out_v[0][0]| |main.out_v[0][1]| |main.out_v[0][2]| |main.out_v[0][3]|
                                |main.out_v[0][4]| |main.out_v[0][5]| |main.out_v[0][6]| |main.out_v[0][7]|
                                |main.out_v[0][8]| |main.out_v[0][9]| |main.out_v[0][10]| |main.out_v[0][11]|
                                |main.out_v[0][12]| |main.out_v[0][13]| |main.out_v[0][14]| |main.out_v[0][15]|
                                |main.out_v[0][16]| |main.out_v[0][17]| |main.out_v[0][18]| |main.out_v[0][19]|
                                |main.out_v[0][20]| |main.out_v[0][21]| |main.out_v[0][22]| |main.out_v[0][23]|
                                |main.out_v[0][24]| |main.out_v[0][25]| |main.out_v[0][26]| |main.out_v[0][27]|
                                |main.out_v[0][28]| |main.out_v[0][29]| |main.out_v[0][30]| |main.out_v[0][31]|)

               (pack-blake-word |main.out_v[1][0]| |main.out_v[1][1]| |main.out_v[1][2]| |main.out_v[1][3]|
                                |main.out_v[1][4]| |main.out_v[1][5]| |main.out_v[1][6]| |main.out_v[1][7]|
                                |main.out_v[1][8]| |main.out_v[1][9]| |main.out_v[1][10]| |main.out_v[1][11]|
                                |main.out_v[1][12]| |main.out_v[1][13]| |main.out_v[1][14]| |main.out_v[1][15]|
                                |main.out_v[1][16]| |main.out_v[1][17]| |main.out_v[1][18]| |main.out_v[1][19]|
                                |main.out_v[1][20]| |main.out_v[1][21]| |main.out_v[1][22]| |main.out_v[1][23]|
                                |main.out_v[1][24]| |main.out_v[1][25]| |main.out_v[1][26]| |main.out_v[1][27]|
                                |main.out_v[1][28]| |main.out_v[1][29]| |main.out_v[1][30]| |main.out_v[1][31]|)

               (pack-blake-word |main.out_v[2][0]| |main.out_v[2][1]| |main.out_v[2][2]| |main.out_v[2][3]|
                                |main.out_v[2][4]| |main.out_v[2][5]| |main.out_v[2][6]| |main.out_v[2][7]|
                                |main.out_v[2][8]| |main.out_v[2][9]| |main.out_v[2][10]| |main.out_v[2][11]|
                                |main.out_v[2][12]| |main.out_v[2][13]| |main.out_v[2][14]| |main.out_v[2][15]|
                                |main.out_v[2][16]| |main.out_v[2][17]| |main.out_v[2][18]| |main.out_v[2][19]|
                                |main.out_v[2][20]| |main.out_v[2][21]| |main.out_v[2][22]| |main.out_v[2][23]|
                                |main.out_v[2][24]| |main.out_v[2][25]| |main.out_v[2][26]| |main.out_v[2][27]|
                                |main.out_v[2][28]| |main.out_v[2][29]| |main.out_v[2][30]| |main.out_v[2][31]|)

               (pack-blake-word |main.out_v[3][0]| |main.out_v[3][1]| |main.out_v[3][2]| |main.out_v[3][3]|
                                |main.out_v[3][4]| |main.out_v[3][5]| |main.out_v[3][6]| |main.out_v[3][7]|
                                |main.out_v[3][8]| |main.out_v[3][9]| |main.out_v[3][10]| |main.out_v[3][11]|
                                |main.out_v[3][12]| |main.out_v[3][13]| |main.out_v[3][14]| |main.out_v[3][15]|
                                |main.out_v[3][16]| |main.out_v[3][17]| |main.out_v[3][18]| |main.out_v[3][19]|
                                |main.out_v[3][20]| |main.out_v[3][21]| |main.out_v[3][22]| |main.out_v[3][23]|
                                |main.out_v[3][24]| |main.out_v[3][25]| |main.out_v[3][26]| |main.out_v[3][27]|
                                |main.out_v[3][28]| |main.out_v[3][29]| |main.out_v[3][30]| |main.out_v[3][31]|)

               (pack-blake-word |main.out_v[4][0]| |main.out_v[4][1]| |main.out_v[4][2]| |main.out_v[4][3]|
                                |main.out_v[4][4]| |main.out_v[4][5]| |main.out_v[4][6]| |main.out_v[4][7]|
                                |main.out_v[4][8]| |main.out_v[4][9]| |main.out_v[4][10]| |main.out_v[4][11]|
                                |main.out_v[4][12]| |main.out_v[4][13]| |main.out_v[4][14]| |main.out_v[4][15]|
                                |main.out_v[4][16]| |main.out_v[4][17]| |main.out_v[4][18]| |main.out_v[4][19]|
                                |main.out_v[4][20]| |main.out_v[4][21]| |main.out_v[4][22]| |main.out_v[4][23]|
                                |main.out_v[4][24]| |main.out_v[4][25]| |main.out_v[4][26]| |main.out_v[4][27]|
                                |main.out_v[4][28]| |main.out_v[4][29]| |main.out_v[4][30]| |main.out_v[4][31]|)

               (pack-blake-word |main.out_v[5][0]| |main.out_v[5][1]| |main.out_v[5][2]| |main.out_v[5][3]|
                                |main.out_v[5][4]| |main.out_v[5][5]| |main.out_v[5][6]| |main.out_v[5][7]|
                                |main.out_v[5][8]| |main.out_v[5][9]| |main.out_v[5][10]| |main.out_v[5][11]|
                                |main.out_v[5][12]| |main.out_v[5][13]| |main.out_v[5][14]| |main.out_v[5][15]|
                                |main.out_v[5][16]| |main.out_v[5][17]| |main.out_v[5][18]| |main.out_v[5][19]|
                                |main.out_v[5][20]| |main.out_v[5][21]| |main.out_v[5][22]| |main.out_v[5][23]|
                                |main.out_v[5][24]| |main.out_v[5][25]| |main.out_v[5][26]| |main.out_v[5][27]|
                                |main.out_v[5][28]| |main.out_v[5][29]| |main.out_v[5][30]| |main.out_v[5][31]|)

               (pack-blake-word |main.out_v[6][0]| |main.out_v[6][1]| |main.out_v[6][2]| |main.out_v[6][3]|
                                |main.out_v[6][4]| |main.out_v[6][5]| |main.out_v[6][6]| |main.out_v[6][7]|
                                |main.out_v[6][8]| |main.out_v[6][9]| |main.out_v[6][10]| |main.out_v[6][11]|
                                |main.out_v[6][12]| |main.out_v[6][13]| |main.out_v[6][14]| |main.out_v[6][15]|
                                |main.out_v[6][16]| |main.out_v[6][17]| |main.out_v[6][18]| |main.out_v[6][19]|
                                |main.out_v[6][20]| |main.out_v[6][21]| |main.out_v[6][22]| |main.out_v[6][23]|
                                |main.out_v[6][24]| |main.out_v[6][25]| |main.out_v[6][26]| |main.out_v[6][27]|
                                |main.out_v[6][28]| |main.out_v[6][29]| |main.out_v[6][30]| |main.out_v[6][31]|)

               (pack-blake-word |main.out_v[7][0]| |main.out_v[7][1]| |main.out_v[7][2]| |main.out_v[7][3]|
                                |main.out_v[7][4]| |main.out_v[7][5]| |main.out_v[7][6]| |main.out_v[7][7]|
                                |main.out_v[7][8]| |main.out_v[7][9]| |main.out_v[7][10]| |main.out_v[7][11]|
                                |main.out_v[7][12]| |main.out_v[7][13]| |main.out_v[7][14]| |main.out_v[7][15]|
                                |main.out_v[7][16]| |main.out_v[7][17]| |main.out_v[7][18]| |main.out_v[7][19]|
                                |main.out_v[7][20]| |main.out_v[7][21]| |main.out_v[7][22]| |main.out_v[7][23]|
                                |main.out_v[7][24]| |main.out_v[7][25]| |main.out_v[7][26]| |main.out_v[7][27]|
                                |main.out_v[7][28]| |main.out_v[7][29]| |main.out_v[7][30]| |main.out_v[7][31]|)

               (pack-blake-word |main.out_v[8][0]| |main.out_v[8][1]| |main.out_v[8][2]| |main.out_v[8][3]|
                                |main.out_v[8][4]| |main.out_v[8][5]| |main.out_v[8][6]| |main.out_v[8][7]|
                                |main.out_v[8][8]| |main.out_v[8][9]| |main.out_v[8][10]| |main.out_v[8][11]|
                                |main.out_v[8][12]| |main.out_v[8][13]| |main.out_v[8][14]| |main.out_v[8][15]|
                                |main.out_v[8][16]| |main.out_v[8][17]| |main.out_v[8][18]| |main.out_v[8][19]|
                                |main.out_v[8][20]| |main.out_v[8][21]| |main.out_v[8][22]| |main.out_v[8][23]|
                                |main.out_v[8][24]| |main.out_v[8][25]| |main.out_v[8][26]| |main.out_v[8][27]|
                                |main.out_v[8][28]| |main.out_v[8][29]| |main.out_v[8][30]| |main.out_v[8][31]|)

               (pack-blake-word |main.out_v[9][0]| |main.out_v[9][1]| |main.out_v[9][2]| |main.out_v[9][3]|
                                |main.out_v[9][4]| |main.out_v[9][5]| |main.out_v[9][6]| |main.out_v[9][7]|
                                |main.out_v[9][8]| |main.out_v[9][9]| |main.out_v[9][10]| |main.out_v[9][11]|
                                |main.out_v[9][12]| |main.out_v[9][13]| |main.out_v[9][14]| |main.out_v[9][15]|
                                |main.out_v[9][16]| |main.out_v[9][17]| |main.out_v[9][18]| |main.out_v[9][19]|
                                |main.out_v[9][20]| |main.out_v[9][21]| |main.out_v[9][22]| |main.out_v[9][23]|
                                |main.out_v[9][24]| |main.out_v[9][25]| |main.out_v[9][26]| |main.out_v[9][27]|
                                |main.out_v[9][28]| |main.out_v[9][29]| |main.out_v[9][30]| |main.out_v[9][31]|)

               (pack-blake-word |main.out_v[10][0]| |main.out_v[10][1]| |main.out_v[10][2]| |main.out_v[10][3]|
                                |main.out_v[10][4]| |main.out_v[10][5]| |main.out_v[10][6]| |main.out_v[10][7]|
                                |main.out_v[10][8]| |main.out_v[10][9]| |main.out_v[10][10]| |main.out_v[10][11]|
                                |main.out_v[10][12]| |main.out_v[10][13]| |main.out_v[10][14]| |main.out_v[10][15]|
                                |main.out_v[10][16]| |main.out_v[10][17]| |main.out_v[10][18]| |main.out_v[10][19]|
                                |main.out_v[10][20]| |main.out_v[10][21]| |main.out_v[10][22]| |main.out_v[10][23]|
                                |main.out_v[10][24]| |main.out_v[10][25]| |main.out_v[10][26]| |main.out_v[10][27]|
                                |main.out_v[10][28]| |main.out_v[10][29]| |main.out_v[10][30]| |main.out_v[10][31]|)

               (pack-blake-word |main.out_v[11][0]| |main.out_v[11][1]| |main.out_v[11][2]| |main.out_v[11][3]|
                                |main.out_v[11][4]| |main.out_v[11][5]| |main.out_v[11][6]| |main.out_v[11][7]|
                                |main.out_v[11][8]| |main.out_v[11][9]| |main.out_v[11][10]| |main.out_v[11][11]|
                                |main.out_v[11][12]| |main.out_v[11][13]| |main.out_v[11][14]| |main.out_v[11][15]|
                                |main.out_v[11][16]| |main.out_v[11][17]| |main.out_v[11][18]| |main.out_v[11][19]|
                                |main.out_v[11][20]| |main.out_v[11][21]| |main.out_v[11][22]| |main.out_v[11][23]|
                                |main.out_v[11][24]| |main.out_v[11][25]| |main.out_v[11][26]| |main.out_v[11][27]|
                                |main.out_v[11][28]| |main.out_v[11][29]| |main.out_v[11][30]| |main.out_v[11][31]|)

               (pack-blake-word |main.out_v[12][0]| |main.out_v[12][1]| |main.out_v[12][2]| |main.out_v[12][3]|
                                |main.out_v[12][4]| |main.out_v[12][5]| |main.out_v[12][6]| |main.out_v[12][7]|
                                |main.out_v[12][8]| |main.out_v[12][9]| |main.out_v[12][10]| |main.out_v[12][11]|
                                |main.out_v[12][12]| |main.out_v[12][13]| |main.out_v[12][14]| |main.out_v[12][15]|
                                |main.out_v[12][16]| |main.out_v[12][17]| |main.out_v[12][18]| |main.out_v[12][19]|
                                |main.out_v[12][20]| |main.out_v[12][21]| |main.out_v[12][22]| |main.out_v[12][23]|
                                |main.out_v[12][24]| |main.out_v[12][25]| |main.out_v[12][26]| |main.out_v[12][27]|
                                |main.out_v[12][28]| |main.out_v[12][29]| |main.out_v[12][30]| |main.out_v[12][31]|)

               (pack-blake-word |main.out_v[13][0]| |main.out_v[13][1]| |main.out_v[13][2]| |main.out_v[13][3]|
                                |main.out_v[13][4]| |main.out_v[13][5]| |main.out_v[13][6]| |main.out_v[13][7]|
                                |main.out_v[13][8]| |main.out_v[13][9]| |main.out_v[13][10]| |main.out_v[13][11]|
                                |main.out_v[13][12]| |main.out_v[13][13]| |main.out_v[13][14]| |main.out_v[13][15]|
                                |main.out_v[13][16]| |main.out_v[13][17]| |main.out_v[13][18]| |main.out_v[13][19]|
                                |main.out_v[13][20]| |main.out_v[13][21]| |main.out_v[13][22]| |main.out_v[13][23]|
                                |main.out_v[13][24]| |main.out_v[13][25]| |main.out_v[13][26]| |main.out_v[13][27]|
                                |main.out_v[13][28]| |main.out_v[13][29]| |main.out_v[13][30]| |main.out_v[13][31]|)

               (pack-blake-word |main.out_v[14][0]| |main.out_v[14][1]| |main.out_v[14][2]| |main.out_v[14][3]|
                                |main.out_v[14][4]| |main.out_v[14][5]| |main.out_v[14][6]| |main.out_v[14][7]|
                                |main.out_v[14][8]| |main.out_v[14][9]| |main.out_v[14][10]| |main.out_v[14][11]|
                                |main.out_v[14][12]| |main.out_v[14][13]| |main.out_v[14][14]| |main.out_v[14][15]|
                                |main.out_v[14][16]| |main.out_v[14][17]| |main.out_v[14][18]| |main.out_v[14][19]|
                                |main.out_v[14][20]| |main.out_v[14][21]| |main.out_v[14][22]| |main.out_v[14][23]|
                                |main.out_v[14][24]| |main.out_v[14][25]| |main.out_v[14][26]| |main.out_v[14][27]|
                                |main.out_v[14][28]| |main.out_v[14][29]| |main.out_v[14][30]| |main.out_v[14][31]|)

               (pack-blake-word |main.out_v[15][0]| |main.out_v[15][1]| |main.out_v[15][2]| |main.out_v[15][3]|
                                |main.out_v[15][4]| |main.out_v[15][5]| |main.out_v[15][6]| |main.out_v[15][7]|
                                |main.out_v[15][8]| |main.out_v[15][9]| |main.out_v[15][10]| |main.out_v[15][11]|
                                |main.out_v[15][12]| |main.out_v[15][13]| |main.out_v[15][14]| |main.out_v[15][15]|
                                |main.out_v[15][16]| |main.out_v[15][17]| |main.out_v[15][18]| |main.out_v[15][19]|
                                |main.out_v[15][20]| |main.out_v[15][21]| |main.out_v[15][22]| |main.out_v[15][23]|
                                |main.out_v[15][24]| |main.out_v[15][25]| |main.out_v[15][26]| |main.out_v[15][27]|
                                |main.out_v[15][28]| |main.out_v[15][29]| |main.out_v[15][30]| |main.out_v[15][31]|))))

;; Invoke the Axe R1CS prover to do the proof:
(verify-semaphore-r1cs
 *blake2s-mixingg-0-r1cs-lifted*
 ;; The spec (this says that spec holds on the inputs and outputs):
 (blake2s-mixing-0-4-8-12 |main.in_v[0][0]| |main.in_v[0][1]| |main.in_v[0][2]| |main.in_v[0][3]|
                          |main.in_v[0][4]| |main.in_v[0][5]| |main.in_v[0][6]| |main.in_v[0][7]|
                          |main.in_v[0][8]| |main.in_v[0][9]| |main.in_v[0][10]| |main.in_v[0][11]|
                          |main.in_v[0][12]| |main.in_v[0][13]| |main.in_v[0][14]| |main.in_v[0][15]|
                          |main.in_v[0][16]| |main.in_v[0][17]| |main.in_v[0][18]| |main.in_v[0][19]|
                          |main.in_v[0][20]| |main.in_v[0][21]| |main.in_v[0][22]| |main.in_v[0][23]|
                          |main.in_v[0][24]| |main.in_v[0][25]| |main.in_v[0][26]| |main.in_v[0][27]|
                          |main.in_v[0][28]| |main.in_v[0][29]| |main.in_v[0][30]| |main.in_v[0][31]|

                          |main.in_v[1][0]| |main.in_v[1][1]| |main.in_v[1][2]| |main.in_v[1][3]|
                          |main.in_v[1][4]| |main.in_v[1][5]| |main.in_v[1][6]| |main.in_v[1][7]|
                          |main.in_v[1][8]| |main.in_v[1][9]| |main.in_v[1][10]| |main.in_v[1][11]|
                          |main.in_v[1][12]| |main.in_v[1][13]| |main.in_v[1][14]| |main.in_v[1][15]|
                          |main.in_v[1][16]| |main.in_v[1][17]| |main.in_v[1][18]| |main.in_v[1][19]|
                          |main.in_v[1][20]| |main.in_v[1][21]| |main.in_v[1][22]| |main.in_v[1][23]|
                          |main.in_v[1][24]| |main.in_v[1][25]| |main.in_v[1][26]| |main.in_v[1][27]|
                          |main.in_v[1][28]| |main.in_v[1][29]| |main.in_v[1][30]| |main.in_v[1][31]|

                          |main.in_v[2][0]| |main.in_v[2][1]| |main.in_v[2][2]| |main.in_v[2][3]|
                          |main.in_v[2][4]| |main.in_v[2][5]| |main.in_v[2][6]| |main.in_v[2][7]|
                          |main.in_v[2][8]| |main.in_v[2][9]| |main.in_v[2][10]| |main.in_v[2][11]|
                          |main.in_v[2][12]| |main.in_v[2][13]| |main.in_v[2][14]| |main.in_v[2][15]|
                          |main.in_v[2][16]| |main.in_v[2][17]| |main.in_v[2][18]| |main.in_v[2][19]|
                          |main.in_v[2][20]| |main.in_v[2][21]| |main.in_v[2][22]| |main.in_v[2][23]|
                          |main.in_v[2][24]| |main.in_v[2][25]| |main.in_v[2][26]| |main.in_v[2][27]|
                          |main.in_v[2][28]| |main.in_v[2][29]| |main.in_v[2][30]| |main.in_v[2][31]|

                          |main.in_v[3][0]| |main.in_v[3][1]| |main.in_v[3][2]| |main.in_v[3][3]|
                          |main.in_v[3][4]| |main.in_v[3][5]| |main.in_v[3][6]| |main.in_v[3][7]|
                          |main.in_v[3][8]| |main.in_v[3][9]| |main.in_v[3][10]| |main.in_v[3][11]|
                          |main.in_v[3][12]| |main.in_v[3][13]| |main.in_v[3][14]| |main.in_v[3][15]|
                          |main.in_v[3][16]| |main.in_v[3][17]| |main.in_v[3][18]| |main.in_v[3][19]|
                          |main.in_v[3][20]| |main.in_v[3][21]| |main.in_v[3][22]| |main.in_v[3][23]|
                          |main.in_v[3][24]| |main.in_v[3][25]| |main.in_v[3][26]| |main.in_v[3][27]|
                          |main.in_v[3][28]| |main.in_v[3][29]| |main.in_v[3][30]| |main.in_v[3][31]|

                          |main.in_v[4][0]| |main.in_v[4][1]| |main.in_v[4][2]| |main.in_v[4][3]|
                          |main.in_v[4][4]| |main.in_v[4][5]| |main.in_v[4][6]| |main.in_v[4][7]|
                          |main.in_v[4][8]| |main.in_v[4][9]| |main.in_v[4][10]| |main.in_v[4][11]|
                          |main.in_v[4][12]| |main.in_v[4][13]| |main.in_v[4][14]| |main.in_v[4][15]|
                          |main.in_v[4][16]| |main.in_v[4][17]| |main.in_v[4][18]| |main.in_v[4][19]|
                          |main.in_v[4][20]| |main.in_v[4][21]| |main.in_v[4][22]| |main.in_v[4][23]|
                          |main.in_v[4][24]| |main.in_v[4][25]| |main.in_v[4][26]| |main.in_v[4][27]|
                          |main.in_v[4][28]| |main.in_v[4][29]| |main.in_v[4][30]| |main.in_v[4][31]|

                          |main.in_v[5][0]| |main.in_v[5][1]| |main.in_v[5][2]| |main.in_v[5][3]|
                          |main.in_v[5][4]| |main.in_v[5][5]| |main.in_v[5][6]| |main.in_v[5][7]|
                          |main.in_v[5][8]| |main.in_v[5][9]| |main.in_v[5][10]| |main.in_v[5][11]|
                          |main.in_v[5][12]| |main.in_v[5][13]| |main.in_v[5][14]| |main.in_v[5][15]|
                          |main.in_v[5][16]| |main.in_v[5][17]| |main.in_v[5][18]| |main.in_v[5][19]|
                          |main.in_v[5][20]| |main.in_v[5][21]| |main.in_v[5][22]| |main.in_v[5][23]|
                          |main.in_v[5][24]| |main.in_v[5][25]| |main.in_v[5][26]| |main.in_v[5][27]|
                          |main.in_v[5][28]| |main.in_v[5][29]| |main.in_v[5][30]| |main.in_v[5][31]|

                          |main.in_v[6][0]| |main.in_v[6][1]| |main.in_v[6][2]| |main.in_v[6][3]|
                          |main.in_v[6][4]| |main.in_v[6][5]| |main.in_v[6][6]| |main.in_v[6][7]|
                          |main.in_v[6][8]| |main.in_v[6][9]| |main.in_v[6][10]| |main.in_v[6][11]|
                          |main.in_v[6][12]| |main.in_v[6][13]| |main.in_v[6][14]| |main.in_v[6][15]|
                          |main.in_v[6][16]| |main.in_v[6][17]| |main.in_v[6][18]| |main.in_v[6][19]|
                          |main.in_v[6][20]| |main.in_v[6][21]| |main.in_v[6][22]| |main.in_v[6][23]|
                          |main.in_v[6][24]| |main.in_v[6][25]| |main.in_v[6][26]| |main.in_v[6][27]|
                          |main.in_v[6][28]| |main.in_v[6][29]| |main.in_v[6][30]| |main.in_v[6][31]|

                          |main.in_v[7][0]| |main.in_v[7][1]| |main.in_v[7][2]| |main.in_v[7][3]|
                          |main.in_v[7][4]| |main.in_v[7][5]| |main.in_v[7][6]| |main.in_v[7][7]|
                          |main.in_v[7][8]| |main.in_v[7][9]| |main.in_v[7][10]| |main.in_v[7][11]|
                          |main.in_v[7][12]| |main.in_v[7][13]| |main.in_v[7][14]| |main.in_v[7][15]|
                          |main.in_v[7][16]| |main.in_v[7][17]| |main.in_v[7][18]| |main.in_v[7][19]|
                          |main.in_v[7][20]| |main.in_v[7][21]| |main.in_v[7][22]| |main.in_v[7][23]|
                          |main.in_v[7][24]| |main.in_v[7][25]| |main.in_v[7][26]| |main.in_v[7][27]|
                          |main.in_v[7][28]| |main.in_v[7][29]| |main.in_v[7][30]| |main.in_v[7][31]|

                          |main.in_v[8][0]| |main.in_v[8][1]| |main.in_v[8][2]| |main.in_v[8][3]|
                          |main.in_v[8][4]| |main.in_v[8][5]| |main.in_v[8][6]| |main.in_v[8][7]|
                          |main.in_v[8][8]| |main.in_v[8][9]| |main.in_v[8][10]| |main.in_v[8][11]|
                          |main.in_v[8][12]| |main.in_v[8][13]| |main.in_v[8][14]| |main.in_v[8][15]|
                          |main.in_v[8][16]| |main.in_v[8][17]| |main.in_v[8][18]| |main.in_v[8][19]|
                          |main.in_v[8][20]| |main.in_v[8][21]| |main.in_v[8][22]| |main.in_v[8][23]|
                          |main.in_v[8][24]| |main.in_v[8][25]| |main.in_v[8][26]| |main.in_v[8][27]|
                          |main.in_v[8][28]| |main.in_v[8][29]| |main.in_v[8][30]| |main.in_v[8][31]|

                          |main.in_v[9][0]| |main.in_v[9][1]| |main.in_v[9][2]| |main.in_v[9][3]|
                          |main.in_v[9][4]| |main.in_v[9][5]| |main.in_v[9][6]| |main.in_v[9][7]|
                          |main.in_v[9][8]| |main.in_v[9][9]| |main.in_v[9][10]| |main.in_v[9][11]|
                          |main.in_v[9][12]| |main.in_v[9][13]| |main.in_v[9][14]| |main.in_v[9][15]|
                          |main.in_v[9][16]| |main.in_v[9][17]| |main.in_v[9][18]| |main.in_v[9][19]|
                          |main.in_v[9][20]| |main.in_v[9][21]| |main.in_v[9][22]| |main.in_v[9][23]|
                          |main.in_v[9][24]| |main.in_v[9][25]| |main.in_v[9][26]| |main.in_v[9][27]|
                          |main.in_v[9][28]| |main.in_v[9][29]| |main.in_v[9][30]| |main.in_v[9][31]|

                          |main.in_v[10][0]| |main.in_v[10][1]| |main.in_v[10][2]| |main.in_v[10][3]|
                          |main.in_v[10][4]| |main.in_v[10][5]| |main.in_v[10][6]| |main.in_v[10][7]|
                          |main.in_v[10][8]| |main.in_v[10][9]| |main.in_v[10][10]| |main.in_v[10][11]|
                          |main.in_v[10][12]| |main.in_v[10][13]| |main.in_v[10][14]| |main.in_v[10][15]|
                          |main.in_v[10][16]| |main.in_v[10][17]| |main.in_v[10][18]| |main.in_v[10][19]|
                          |main.in_v[10][20]| |main.in_v[10][21]| |main.in_v[10][22]| |main.in_v[10][23]|
                          |main.in_v[10][24]| |main.in_v[10][25]| |main.in_v[10][26]| |main.in_v[10][27]|
                          |main.in_v[10][28]| |main.in_v[10][29]| |main.in_v[10][30]| |main.in_v[10][31]|

                          |main.in_v[11][0]| |main.in_v[11][1]| |main.in_v[11][2]| |main.in_v[11][3]|
                          |main.in_v[11][4]| |main.in_v[11][5]| |main.in_v[11][6]| |main.in_v[11][7]|
                          |main.in_v[11][8]| |main.in_v[11][9]| |main.in_v[11][10]| |main.in_v[11][11]|
                          |main.in_v[11][12]| |main.in_v[11][13]| |main.in_v[11][14]| |main.in_v[11][15]|
                          |main.in_v[11][16]| |main.in_v[11][17]| |main.in_v[11][18]| |main.in_v[11][19]|
                          |main.in_v[11][20]| |main.in_v[11][21]| |main.in_v[11][22]| |main.in_v[11][23]|
                          |main.in_v[11][24]| |main.in_v[11][25]| |main.in_v[11][26]| |main.in_v[11][27]|
                          |main.in_v[11][28]| |main.in_v[11][29]| |main.in_v[11][30]| |main.in_v[11][31]|

                          |main.in_v[12][0]| |main.in_v[12][1]| |main.in_v[12][2]| |main.in_v[12][3]|
                          |main.in_v[12][4]| |main.in_v[12][5]| |main.in_v[12][6]| |main.in_v[12][7]|
                          |main.in_v[12][8]| |main.in_v[12][9]| |main.in_v[12][10]| |main.in_v[12][11]|
                          |main.in_v[12][12]| |main.in_v[12][13]| |main.in_v[12][14]| |main.in_v[12][15]|
                          |main.in_v[12][16]| |main.in_v[12][17]| |main.in_v[12][18]| |main.in_v[12][19]|
                          |main.in_v[12][20]| |main.in_v[12][21]| |main.in_v[12][22]| |main.in_v[12][23]|
                          |main.in_v[12][24]| |main.in_v[12][25]| |main.in_v[12][26]| |main.in_v[12][27]|
                          |main.in_v[12][28]| |main.in_v[12][29]| |main.in_v[12][30]| |main.in_v[12][31]|

                          |main.in_v[13][0]| |main.in_v[13][1]| |main.in_v[13][2]| |main.in_v[13][3]|
                          |main.in_v[13][4]| |main.in_v[13][5]| |main.in_v[13][6]| |main.in_v[13][7]|
                          |main.in_v[13][8]| |main.in_v[13][9]| |main.in_v[13][10]| |main.in_v[13][11]|
                          |main.in_v[13][12]| |main.in_v[13][13]| |main.in_v[13][14]| |main.in_v[13][15]|
                          |main.in_v[13][16]| |main.in_v[13][17]| |main.in_v[13][18]| |main.in_v[13][19]|
                          |main.in_v[13][20]| |main.in_v[13][21]| |main.in_v[13][22]| |main.in_v[13][23]|
                          |main.in_v[13][24]| |main.in_v[13][25]| |main.in_v[13][26]| |main.in_v[13][27]|
                          |main.in_v[13][28]| |main.in_v[13][29]| |main.in_v[13][30]| |main.in_v[13][31]|

                          |main.in_v[14][0]| |main.in_v[14][1]| |main.in_v[14][2]| |main.in_v[14][3]|
                          |main.in_v[14][4]| |main.in_v[14][5]| |main.in_v[14][6]| |main.in_v[14][7]|
                          |main.in_v[14][8]| |main.in_v[14][9]| |main.in_v[14][10]| |main.in_v[14][11]|
                          |main.in_v[14][12]| |main.in_v[14][13]| |main.in_v[14][14]| |main.in_v[14][15]|
                          |main.in_v[14][16]| |main.in_v[14][17]| |main.in_v[14][18]| |main.in_v[14][19]|
                          |main.in_v[14][20]| |main.in_v[14][21]| |main.in_v[14][22]| |main.in_v[14][23]|
                          |main.in_v[14][24]| |main.in_v[14][25]| |main.in_v[14][26]| |main.in_v[14][27]|
                          |main.in_v[14][28]| |main.in_v[14][29]| |main.in_v[14][30]| |main.in_v[14][31]|

                          |main.in_v[15][0]| |main.in_v[15][1]| |main.in_v[15][2]| |main.in_v[15][3]|
                          |main.in_v[15][4]| |main.in_v[15][5]| |main.in_v[15][6]| |main.in_v[15][7]|
                          |main.in_v[15][8]| |main.in_v[15][9]| |main.in_v[15][10]| |main.in_v[15][11]|
                          |main.in_v[15][12]| |main.in_v[15][13]| |main.in_v[15][14]| |main.in_v[15][15]|
                          |main.in_v[15][16]| |main.in_v[15][17]| |main.in_v[15][18]| |main.in_v[15][19]|
                          |main.in_v[15][20]| |main.in_v[15][21]| |main.in_v[15][22]| |main.in_v[15][23]|
                          |main.in_v[15][24]| |main.in_v[15][25]| |main.in_v[15][26]| |main.in_v[15][27]|
                          |main.in_v[15][28]| |main.in_v[15][29]| |main.in_v[15][30]| |main.in_v[15][31]|

                          |main.x[0]| |main.x[1]| |main.x[2]| |main.x[3]|
                          |main.x[4]| |main.x[5]| |main.x[6]| |main.x[7]|
                          |main.x[8]| |main.x[9]| |main.x[10]| |main.x[11]|
                          |main.x[12]| |main.x[13]| |main.x[14]| |main.x[15]|
                          |main.x[16]| |main.x[17]| |main.x[18]| |main.x[19]|
                          |main.x[20]| |main.x[21]| |main.x[22]| |main.x[23]|
                          |main.x[24]| |main.x[25]| |main.x[26]| |main.x[27]|
                          |main.x[28]| |main.x[29]| |main.x[30]| |main.x[31]|

                          |main.y[0]| |main.y[1]| |main.y[2]| |main.y[3]|
                          |main.y[4]| |main.y[5]| |main.y[6]| |main.y[7]|
                          |main.y[8]| |main.y[9]| |main.y[10]| |main.y[11]|
                          |main.y[12]| |main.y[13]| |main.y[14]| |main.y[15]|
                          |main.y[16]| |main.y[17]| |main.y[18]| |main.y[19]|
                          |main.y[20]| |main.y[21]| |main.y[22]| |main.y[23]|
                          |main.y[24]| |main.y[25]| |main.y[26]| |main.y[27]|
                          |main.y[28]| |main.y[29]| |main.y[30]| |main.y[31]|

                          |main.out_v[0][0]| |main.out_v[0][1]| |main.out_v[0][2]| |main.out_v[0][3]|
                          |main.out_v[0][4]| |main.out_v[0][5]| |main.out_v[0][6]| |main.out_v[0][7]|
                          |main.out_v[0][8]| |main.out_v[0][9]| |main.out_v[0][10]| |main.out_v[0][11]|
                          |main.out_v[0][12]| |main.out_v[0][13]| |main.out_v[0][14]| |main.out_v[0][15]|
                          |main.out_v[0][16]| |main.out_v[0][17]| |main.out_v[0][18]| |main.out_v[0][19]|
                          |main.out_v[0][20]| |main.out_v[0][21]| |main.out_v[0][22]| |main.out_v[0][23]|
                          |main.out_v[0][24]| |main.out_v[0][25]| |main.out_v[0][26]| |main.out_v[0][27]|
                          |main.out_v[0][28]| |main.out_v[0][29]| |main.out_v[0][30]| |main.out_v[0][31]|

                          |main.out_v[1][0]| |main.out_v[1][1]| |main.out_v[1][2]| |main.out_v[1][3]|
                          |main.out_v[1][4]| |main.out_v[1][5]| |main.out_v[1][6]| |main.out_v[1][7]|
                          |main.out_v[1][8]| |main.out_v[1][9]| |main.out_v[1][10]| |main.out_v[1][11]|
                          |main.out_v[1][12]| |main.out_v[1][13]| |main.out_v[1][14]| |main.out_v[1][15]|
                          |main.out_v[1][16]| |main.out_v[1][17]| |main.out_v[1][18]| |main.out_v[1][19]|
                          |main.out_v[1][20]| |main.out_v[1][21]| |main.out_v[1][22]| |main.out_v[1][23]|
                          |main.out_v[1][24]| |main.out_v[1][25]| |main.out_v[1][26]| |main.out_v[1][27]|
                          |main.out_v[1][28]| |main.out_v[1][29]| |main.out_v[1][30]| |main.out_v[1][31]|

                          |main.out_v[2][0]| |main.out_v[2][1]| |main.out_v[2][2]| |main.out_v[2][3]|
                          |main.out_v[2][4]| |main.out_v[2][5]| |main.out_v[2][6]| |main.out_v[2][7]|
                          |main.out_v[2][8]| |main.out_v[2][9]| |main.out_v[2][10]| |main.out_v[2][11]|
                          |main.out_v[2][12]| |main.out_v[2][13]| |main.out_v[2][14]| |main.out_v[2][15]|
                          |main.out_v[2][16]| |main.out_v[2][17]| |main.out_v[2][18]| |main.out_v[2][19]|
                          |main.out_v[2][20]| |main.out_v[2][21]| |main.out_v[2][22]| |main.out_v[2][23]|
                          |main.out_v[2][24]| |main.out_v[2][25]| |main.out_v[2][26]| |main.out_v[2][27]|
                          |main.out_v[2][28]| |main.out_v[2][29]| |main.out_v[2][30]| |main.out_v[2][31]|

                          |main.out_v[3][0]| |main.out_v[3][1]| |main.out_v[3][2]| |main.out_v[3][3]|
                          |main.out_v[3][4]| |main.out_v[3][5]| |main.out_v[3][6]| |main.out_v[3][7]|
                          |main.out_v[3][8]| |main.out_v[3][9]| |main.out_v[3][10]| |main.out_v[3][11]|
                          |main.out_v[3][12]| |main.out_v[3][13]| |main.out_v[3][14]| |main.out_v[3][15]|
                          |main.out_v[3][16]| |main.out_v[3][17]| |main.out_v[3][18]| |main.out_v[3][19]|
                          |main.out_v[3][20]| |main.out_v[3][21]| |main.out_v[3][22]| |main.out_v[3][23]|
                          |main.out_v[3][24]| |main.out_v[3][25]| |main.out_v[3][26]| |main.out_v[3][27]|
                          |main.out_v[3][28]| |main.out_v[3][29]| |main.out_v[3][30]| |main.out_v[3][31]|

                          |main.out_v[4][0]| |main.out_v[4][1]| |main.out_v[4][2]| |main.out_v[4][3]|
                          |main.out_v[4][4]| |main.out_v[4][5]| |main.out_v[4][6]| |main.out_v[4][7]|
                          |main.out_v[4][8]| |main.out_v[4][9]| |main.out_v[4][10]| |main.out_v[4][11]|
                          |main.out_v[4][12]| |main.out_v[4][13]| |main.out_v[4][14]| |main.out_v[4][15]|
                          |main.out_v[4][16]| |main.out_v[4][17]| |main.out_v[4][18]| |main.out_v[4][19]|
                          |main.out_v[4][20]| |main.out_v[4][21]| |main.out_v[4][22]| |main.out_v[4][23]|
                          |main.out_v[4][24]| |main.out_v[4][25]| |main.out_v[4][26]| |main.out_v[4][27]|
                          |main.out_v[4][28]| |main.out_v[4][29]| |main.out_v[4][30]| |main.out_v[4][31]|

                          |main.out_v[5][0]| |main.out_v[5][1]| |main.out_v[5][2]| |main.out_v[5][3]|
                          |main.out_v[5][4]| |main.out_v[5][5]| |main.out_v[5][6]| |main.out_v[5][7]|
                          |main.out_v[5][8]| |main.out_v[5][9]| |main.out_v[5][10]| |main.out_v[5][11]|
                          |main.out_v[5][12]| |main.out_v[5][13]| |main.out_v[5][14]| |main.out_v[5][15]|
                          |main.out_v[5][16]| |main.out_v[5][17]| |main.out_v[5][18]| |main.out_v[5][19]|
                          |main.out_v[5][20]| |main.out_v[5][21]| |main.out_v[5][22]| |main.out_v[5][23]|
                          |main.out_v[5][24]| |main.out_v[5][25]| |main.out_v[5][26]| |main.out_v[5][27]|
                          |main.out_v[5][28]| |main.out_v[5][29]| |main.out_v[5][30]| |main.out_v[5][31]|

                          |main.out_v[6][0]| |main.out_v[6][1]| |main.out_v[6][2]| |main.out_v[6][3]|
                          |main.out_v[6][4]| |main.out_v[6][5]| |main.out_v[6][6]| |main.out_v[6][7]|
                          |main.out_v[6][8]| |main.out_v[6][9]| |main.out_v[6][10]| |main.out_v[6][11]|
                          |main.out_v[6][12]| |main.out_v[6][13]| |main.out_v[6][14]| |main.out_v[6][15]|
                          |main.out_v[6][16]| |main.out_v[6][17]| |main.out_v[6][18]| |main.out_v[6][19]|
                          |main.out_v[6][20]| |main.out_v[6][21]| |main.out_v[6][22]| |main.out_v[6][23]|
                          |main.out_v[6][24]| |main.out_v[6][25]| |main.out_v[6][26]| |main.out_v[6][27]|
                          |main.out_v[6][28]| |main.out_v[6][29]| |main.out_v[6][30]| |main.out_v[6][31]|

                          |main.out_v[7][0]| |main.out_v[7][1]| |main.out_v[7][2]| |main.out_v[7][3]|
                          |main.out_v[7][4]| |main.out_v[7][5]| |main.out_v[7][6]| |main.out_v[7][7]|
                          |main.out_v[7][8]| |main.out_v[7][9]| |main.out_v[7][10]| |main.out_v[7][11]|
                          |main.out_v[7][12]| |main.out_v[7][13]| |main.out_v[7][14]| |main.out_v[7][15]|
                          |main.out_v[7][16]| |main.out_v[7][17]| |main.out_v[7][18]| |main.out_v[7][19]|
                          |main.out_v[7][20]| |main.out_v[7][21]| |main.out_v[7][22]| |main.out_v[7][23]|
                          |main.out_v[7][24]| |main.out_v[7][25]| |main.out_v[7][26]| |main.out_v[7][27]|
                          |main.out_v[7][28]| |main.out_v[7][29]| |main.out_v[7][30]| |main.out_v[7][31]|

                          |main.out_v[8][0]| |main.out_v[8][1]| |main.out_v[8][2]| |main.out_v[8][3]|
                          |main.out_v[8][4]| |main.out_v[8][5]| |main.out_v[8][6]| |main.out_v[8][7]|
                          |main.out_v[8][8]| |main.out_v[8][9]| |main.out_v[8][10]| |main.out_v[8][11]|
                          |main.out_v[8][12]| |main.out_v[8][13]| |main.out_v[8][14]| |main.out_v[8][15]|
                          |main.out_v[8][16]| |main.out_v[8][17]| |main.out_v[8][18]| |main.out_v[8][19]|
                          |main.out_v[8][20]| |main.out_v[8][21]| |main.out_v[8][22]| |main.out_v[8][23]|
                          |main.out_v[8][24]| |main.out_v[8][25]| |main.out_v[8][26]| |main.out_v[8][27]|
                          |main.out_v[8][28]| |main.out_v[8][29]| |main.out_v[8][30]| |main.out_v[8][31]|

                          |main.out_v[9][0]| |main.out_v[9][1]| |main.out_v[9][2]| |main.out_v[9][3]|
                          |main.out_v[9][4]| |main.out_v[9][5]| |main.out_v[9][6]| |main.out_v[9][7]|
                          |main.out_v[9][8]| |main.out_v[9][9]| |main.out_v[9][10]| |main.out_v[9][11]|
                          |main.out_v[9][12]| |main.out_v[9][13]| |main.out_v[9][14]| |main.out_v[9][15]|
                          |main.out_v[9][16]| |main.out_v[9][17]| |main.out_v[9][18]| |main.out_v[9][19]|
                          |main.out_v[9][20]| |main.out_v[9][21]| |main.out_v[9][22]| |main.out_v[9][23]|
                          |main.out_v[9][24]| |main.out_v[9][25]| |main.out_v[9][26]| |main.out_v[9][27]|
                          |main.out_v[9][28]| |main.out_v[9][29]| |main.out_v[9][30]| |main.out_v[9][31]|

                          |main.out_v[10][0]| |main.out_v[10][1]| |main.out_v[10][2]| |main.out_v[10][3]|
                          |main.out_v[10][4]| |main.out_v[10][5]| |main.out_v[10][6]| |main.out_v[10][7]|
                          |main.out_v[10][8]| |main.out_v[10][9]| |main.out_v[10][10]| |main.out_v[10][11]|
                          |main.out_v[10][12]| |main.out_v[10][13]| |main.out_v[10][14]| |main.out_v[10][15]|
                          |main.out_v[10][16]| |main.out_v[10][17]| |main.out_v[10][18]| |main.out_v[10][19]|
                          |main.out_v[10][20]| |main.out_v[10][21]| |main.out_v[10][22]| |main.out_v[10][23]|
                          |main.out_v[10][24]| |main.out_v[10][25]| |main.out_v[10][26]| |main.out_v[10][27]|
                          |main.out_v[10][28]| |main.out_v[10][29]| |main.out_v[10][30]| |main.out_v[10][31]|

                          |main.out_v[11][0]| |main.out_v[11][1]| |main.out_v[11][2]| |main.out_v[11][3]|
                          |main.out_v[11][4]| |main.out_v[11][5]| |main.out_v[11][6]| |main.out_v[11][7]|
                          |main.out_v[11][8]| |main.out_v[11][9]| |main.out_v[11][10]| |main.out_v[11][11]|
                          |main.out_v[11][12]| |main.out_v[11][13]| |main.out_v[11][14]| |main.out_v[11][15]|
                          |main.out_v[11][16]| |main.out_v[11][17]| |main.out_v[11][18]| |main.out_v[11][19]|
                          |main.out_v[11][20]| |main.out_v[11][21]| |main.out_v[11][22]| |main.out_v[11][23]|
                          |main.out_v[11][24]| |main.out_v[11][25]| |main.out_v[11][26]| |main.out_v[11][27]|
                          |main.out_v[11][28]| |main.out_v[11][29]| |main.out_v[11][30]| |main.out_v[11][31]|

                          |main.out_v[12][0]| |main.out_v[12][1]| |main.out_v[12][2]| |main.out_v[12][3]|
                          |main.out_v[12][4]| |main.out_v[12][5]| |main.out_v[12][6]| |main.out_v[12][7]|
                          |main.out_v[12][8]| |main.out_v[12][9]| |main.out_v[12][10]| |main.out_v[12][11]|
                          |main.out_v[12][12]| |main.out_v[12][13]| |main.out_v[12][14]| |main.out_v[12][15]|
                          |main.out_v[12][16]| |main.out_v[12][17]| |main.out_v[12][18]| |main.out_v[12][19]|
                          |main.out_v[12][20]| |main.out_v[12][21]| |main.out_v[12][22]| |main.out_v[12][23]|
                          |main.out_v[12][24]| |main.out_v[12][25]| |main.out_v[12][26]| |main.out_v[12][27]|
                          |main.out_v[12][28]| |main.out_v[12][29]| |main.out_v[12][30]| |main.out_v[12][31]|

                          |main.out_v[13][0]| |main.out_v[13][1]| |main.out_v[13][2]| |main.out_v[13][3]|
                          |main.out_v[13][4]| |main.out_v[13][5]| |main.out_v[13][6]| |main.out_v[13][7]|
                          |main.out_v[13][8]| |main.out_v[13][9]| |main.out_v[13][10]| |main.out_v[13][11]|
                          |main.out_v[13][12]| |main.out_v[13][13]| |main.out_v[13][14]| |main.out_v[13][15]|
                          |main.out_v[13][16]| |main.out_v[13][17]| |main.out_v[13][18]| |main.out_v[13][19]|
                          |main.out_v[13][20]| |main.out_v[13][21]| |main.out_v[13][22]| |main.out_v[13][23]|
                          |main.out_v[13][24]| |main.out_v[13][25]| |main.out_v[13][26]| |main.out_v[13][27]|
                          |main.out_v[13][28]| |main.out_v[13][29]| |main.out_v[13][30]| |main.out_v[13][31]|

                          |main.out_v[14][0]| |main.out_v[14][1]| |main.out_v[14][2]| |main.out_v[14][3]|
                          |main.out_v[14][4]| |main.out_v[14][5]| |main.out_v[14][6]| |main.out_v[14][7]|
                          |main.out_v[14][8]| |main.out_v[14][9]| |main.out_v[14][10]| |main.out_v[14][11]|
                          |main.out_v[14][12]| |main.out_v[14][13]| |main.out_v[14][14]| |main.out_v[14][15]|
                          |main.out_v[14][16]| |main.out_v[14][17]| |main.out_v[14][18]| |main.out_v[14][19]|
                          |main.out_v[14][20]| |main.out_v[14][21]| |main.out_v[14][22]| |main.out_v[14][23]|
                          |main.out_v[14][24]| |main.out_v[14][25]| |main.out_v[14][26]| |main.out_v[14][27]|
                          |main.out_v[14][28]| |main.out_v[14][29]| |main.out_v[14][30]| |main.out_v[14][31]|

                          |main.out_v[15][0]| |main.out_v[15][1]| |main.out_v[15][2]| |main.out_v[15][3]|
                          |main.out_v[15][4]| |main.out_v[15][5]| |main.out_v[15][6]| |main.out_v[15][7]|
                          |main.out_v[15][8]| |main.out_v[15][9]| |main.out_v[15][10]| |main.out_v[15][11]|
                          |main.out_v[15][12]| |main.out_v[15][13]| |main.out_v[15][14]| |main.out_v[15][15]|
                          |main.out_v[15][16]| |main.out_v[15][17]| |main.out_v[15][18]| |main.out_v[15][19]|
                          |main.out_v[15][20]| |main.out_v[15][21]| |main.out_v[15][22]| |main.out_v[15][23]|
                          |main.out_v[15][24]| |main.out_v[15][25]| |main.out_v[15][26]| |main.out_v[15][27]|
                          |main.out_v[15][28]| |main.out_v[15][29]| |main.out_v[15][30]| |main.out_v[15][31]|)
 :bit-inputs '(|main.in_v[0][0]| |main.in_v[0][1]| |main.in_v[0][2]| |main.in_v[0][3]|
               |main.in_v[0][4]| |main.in_v[0][5]| |main.in_v[0][6]| |main.in_v[0][7]|
               |main.in_v[0][8]| |main.in_v[0][9]| |main.in_v[0][10]| |main.in_v[0][11]|
               |main.in_v[0][12]| |main.in_v[0][13]| |main.in_v[0][14]| |main.in_v[0][15]|
               |main.in_v[0][16]| |main.in_v[0][17]| |main.in_v[0][18]| |main.in_v[0][19]|
               |main.in_v[0][20]| |main.in_v[0][21]| |main.in_v[0][22]| |main.in_v[0][23]|
               |main.in_v[0][24]| |main.in_v[0][25]| |main.in_v[0][26]| |main.in_v[0][27]|
               |main.in_v[0][28]| |main.in_v[0][29]| |main.in_v[0][30]| |main.in_v[0][31]|

               |main.in_v[1][0]| |main.in_v[1][1]| |main.in_v[1][2]| |main.in_v[1][3]|
               |main.in_v[1][4]| |main.in_v[1][5]| |main.in_v[1][6]| |main.in_v[1][7]|
               |main.in_v[1][8]| |main.in_v[1][9]| |main.in_v[1][10]| |main.in_v[1][11]|
               |main.in_v[1][12]| |main.in_v[1][13]| |main.in_v[1][14]| |main.in_v[1][15]|
               |main.in_v[1][16]| |main.in_v[1][17]| |main.in_v[1][18]| |main.in_v[1][19]|
               |main.in_v[1][20]| |main.in_v[1][21]| |main.in_v[1][22]| |main.in_v[1][23]|
               |main.in_v[1][24]| |main.in_v[1][25]| |main.in_v[1][26]| |main.in_v[1][27]|
               |main.in_v[1][28]| |main.in_v[1][29]| |main.in_v[1][30]| |main.in_v[1][31]|

               |main.in_v[2][0]| |main.in_v[2][1]| |main.in_v[2][2]| |main.in_v[2][3]|
               |main.in_v[2][4]| |main.in_v[2][5]| |main.in_v[2][6]| |main.in_v[2][7]|
               |main.in_v[2][8]| |main.in_v[2][9]| |main.in_v[2][10]| |main.in_v[2][11]|
               |main.in_v[2][12]| |main.in_v[2][13]| |main.in_v[2][14]| |main.in_v[2][15]|
               |main.in_v[2][16]| |main.in_v[2][17]| |main.in_v[2][18]| |main.in_v[2][19]|
               |main.in_v[2][20]| |main.in_v[2][21]| |main.in_v[2][22]| |main.in_v[2][23]|
               |main.in_v[2][24]| |main.in_v[2][25]| |main.in_v[2][26]| |main.in_v[2][27]|
               |main.in_v[2][28]| |main.in_v[2][29]| |main.in_v[2][30]| |main.in_v[2][31]|

               |main.in_v[3][0]| |main.in_v[3][1]| |main.in_v[3][2]| |main.in_v[3][3]|
               |main.in_v[3][4]| |main.in_v[3][5]| |main.in_v[3][6]| |main.in_v[3][7]|
               |main.in_v[3][8]| |main.in_v[3][9]| |main.in_v[3][10]| |main.in_v[3][11]|
               |main.in_v[3][12]| |main.in_v[3][13]| |main.in_v[3][14]| |main.in_v[3][15]|
               |main.in_v[3][16]| |main.in_v[3][17]| |main.in_v[3][18]| |main.in_v[3][19]|
               |main.in_v[3][20]| |main.in_v[3][21]| |main.in_v[3][22]| |main.in_v[3][23]|
               |main.in_v[3][24]| |main.in_v[3][25]| |main.in_v[3][26]| |main.in_v[3][27]|
               |main.in_v[3][28]| |main.in_v[3][29]| |main.in_v[3][30]| |main.in_v[3][31]|

               |main.in_v[4][0]| |main.in_v[4][1]| |main.in_v[4][2]| |main.in_v[4][3]|
               |main.in_v[4][4]| |main.in_v[4][5]| |main.in_v[4][6]| |main.in_v[4][7]|
               |main.in_v[4][8]| |main.in_v[4][9]| |main.in_v[4][10]| |main.in_v[4][11]|
               |main.in_v[4][12]| |main.in_v[4][13]| |main.in_v[4][14]| |main.in_v[4][15]|
               |main.in_v[4][16]| |main.in_v[4][17]| |main.in_v[4][18]| |main.in_v[4][19]|
               |main.in_v[4][20]| |main.in_v[4][21]| |main.in_v[4][22]| |main.in_v[4][23]|
               |main.in_v[4][24]| |main.in_v[4][25]| |main.in_v[4][26]| |main.in_v[4][27]|
               |main.in_v[4][28]| |main.in_v[4][29]| |main.in_v[4][30]| |main.in_v[4][31]|

               |main.in_v[5][0]| |main.in_v[5][1]| |main.in_v[5][2]| |main.in_v[5][3]|
               |main.in_v[5][4]| |main.in_v[5][5]| |main.in_v[5][6]| |main.in_v[5][7]|
               |main.in_v[5][8]| |main.in_v[5][9]| |main.in_v[5][10]| |main.in_v[5][11]|
               |main.in_v[5][12]| |main.in_v[5][13]| |main.in_v[5][14]| |main.in_v[5][15]|
               |main.in_v[5][16]| |main.in_v[5][17]| |main.in_v[5][18]| |main.in_v[5][19]|
               |main.in_v[5][20]| |main.in_v[5][21]| |main.in_v[5][22]| |main.in_v[5][23]|
               |main.in_v[5][24]| |main.in_v[5][25]| |main.in_v[5][26]| |main.in_v[5][27]|
               |main.in_v[5][28]| |main.in_v[5][29]| |main.in_v[5][30]| |main.in_v[5][31]|

               |main.in_v[6][0]| |main.in_v[6][1]| |main.in_v[6][2]| |main.in_v[6][3]|
               |main.in_v[6][4]| |main.in_v[6][5]| |main.in_v[6][6]| |main.in_v[6][7]|
               |main.in_v[6][8]| |main.in_v[6][9]| |main.in_v[6][10]| |main.in_v[6][11]|
               |main.in_v[6][12]| |main.in_v[6][13]| |main.in_v[6][14]| |main.in_v[6][15]|
               |main.in_v[6][16]| |main.in_v[6][17]| |main.in_v[6][18]| |main.in_v[6][19]|
               |main.in_v[6][20]| |main.in_v[6][21]| |main.in_v[6][22]| |main.in_v[6][23]|
               |main.in_v[6][24]| |main.in_v[6][25]| |main.in_v[6][26]| |main.in_v[6][27]|
               |main.in_v[6][28]| |main.in_v[6][29]| |main.in_v[6][30]| |main.in_v[6][31]|

               |main.in_v[7][0]| |main.in_v[7][1]| |main.in_v[7][2]| |main.in_v[7][3]|
               |main.in_v[7][4]| |main.in_v[7][5]| |main.in_v[7][6]| |main.in_v[7][7]|
               |main.in_v[7][8]| |main.in_v[7][9]| |main.in_v[7][10]| |main.in_v[7][11]|
               |main.in_v[7][12]| |main.in_v[7][13]| |main.in_v[7][14]| |main.in_v[7][15]|
               |main.in_v[7][16]| |main.in_v[7][17]| |main.in_v[7][18]| |main.in_v[7][19]|
               |main.in_v[7][20]| |main.in_v[7][21]| |main.in_v[7][22]| |main.in_v[7][23]|
               |main.in_v[7][24]| |main.in_v[7][25]| |main.in_v[7][26]| |main.in_v[7][27]|
               |main.in_v[7][28]| |main.in_v[7][29]| |main.in_v[7][30]| |main.in_v[7][31]|

               |main.in_v[8][0]| |main.in_v[8][1]| |main.in_v[8][2]| |main.in_v[8][3]|
               |main.in_v[8][4]| |main.in_v[8][5]| |main.in_v[8][6]| |main.in_v[8][7]|
               |main.in_v[8][8]| |main.in_v[8][9]| |main.in_v[8][10]| |main.in_v[8][11]|
               |main.in_v[8][12]| |main.in_v[8][13]| |main.in_v[8][14]| |main.in_v[8][15]|
               |main.in_v[8][16]| |main.in_v[8][17]| |main.in_v[8][18]| |main.in_v[8][19]|
               |main.in_v[8][20]| |main.in_v[8][21]| |main.in_v[8][22]| |main.in_v[8][23]|
               |main.in_v[8][24]| |main.in_v[8][25]| |main.in_v[8][26]| |main.in_v[8][27]|
               |main.in_v[8][28]| |main.in_v[8][29]| |main.in_v[8][30]| |main.in_v[8][31]|

               |main.in_v[9][0]| |main.in_v[9][1]| |main.in_v[9][2]| |main.in_v[9][3]|
               |main.in_v[9][4]| |main.in_v[9][5]| |main.in_v[9][6]| |main.in_v[9][7]|
               |main.in_v[9][8]| |main.in_v[9][9]| |main.in_v[9][10]| |main.in_v[9][11]|
               |main.in_v[9][12]| |main.in_v[9][13]| |main.in_v[9][14]| |main.in_v[9][15]|
               |main.in_v[9][16]| |main.in_v[9][17]| |main.in_v[9][18]| |main.in_v[9][19]|
               |main.in_v[9][20]| |main.in_v[9][21]| |main.in_v[9][22]| |main.in_v[9][23]|
               |main.in_v[9][24]| |main.in_v[9][25]| |main.in_v[9][26]| |main.in_v[9][27]|
               |main.in_v[9][28]| |main.in_v[9][29]| |main.in_v[9][30]| |main.in_v[9][31]|

               |main.in_v[10][0]| |main.in_v[10][1]| |main.in_v[10][2]| |main.in_v[10][3]|
               |main.in_v[10][4]| |main.in_v[10][5]| |main.in_v[10][6]| |main.in_v[10][7]|
               |main.in_v[10][8]| |main.in_v[10][9]| |main.in_v[10][10]| |main.in_v[10][11]|
               |main.in_v[10][12]| |main.in_v[10][13]| |main.in_v[10][14]| |main.in_v[10][15]|
               |main.in_v[10][16]| |main.in_v[10][17]| |main.in_v[10][18]| |main.in_v[10][19]|
               |main.in_v[10][20]| |main.in_v[10][21]| |main.in_v[10][22]| |main.in_v[10][23]|
               |main.in_v[10][24]| |main.in_v[10][25]| |main.in_v[10][26]| |main.in_v[10][27]|
               |main.in_v[10][28]| |main.in_v[10][29]| |main.in_v[10][30]| |main.in_v[10][31]|

               |main.in_v[11][0]| |main.in_v[11][1]| |main.in_v[11][2]| |main.in_v[11][3]|
               |main.in_v[11][4]| |main.in_v[11][5]| |main.in_v[11][6]| |main.in_v[11][7]|
               |main.in_v[11][8]| |main.in_v[11][9]| |main.in_v[11][10]| |main.in_v[11][11]|
               |main.in_v[11][12]| |main.in_v[11][13]| |main.in_v[11][14]| |main.in_v[11][15]|
               |main.in_v[11][16]| |main.in_v[11][17]| |main.in_v[11][18]| |main.in_v[11][19]|
               |main.in_v[11][20]| |main.in_v[11][21]| |main.in_v[11][22]| |main.in_v[11][23]|
               |main.in_v[11][24]| |main.in_v[11][25]| |main.in_v[11][26]| |main.in_v[11][27]|
               |main.in_v[11][28]| |main.in_v[11][29]| |main.in_v[11][30]| |main.in_v[11][31]|

               |main.in_v[12][0]| |main.in_v[12][1]| |main.in_v[12][2]| |main.in_v[12][3]|
               |main.in_v[12][4]| |main.in_v[12][5]| |main.in_v[12][6]| |main.in_v[12][7]|
               |main.in_v[12][8]| |main.in_v[12][9]| |main.in_v[12][10]| |main.in_v[12][11]|
               |main.in_v[12][12]| |main.in_v[12][13]| |main.in_v[12][14]| |main.in_v[12][15]|
               |main.in_v[12][16]| |main.in_v[12][17]| |main.in_v[12][18]| |main.in_v[12][19]|
               |main.in_v[12][20]| |main.in_v[12][21]| |main.in_v[12][22]| |main.in_v[12][23]|
               |main.in_v[12][24]| |main.in_v[12][25]| |main.in_v[12][26]| |main.in_v[12][27]|
               |main.in_v[12][28]| |main.in_v[12][29]| |main.in_v[12][30]| |main.in_v[12][31]|

               |main.in_v[13][0]| |main.in_v[13][1]| |main.in_v[13][2]| |main.in_v[13][3]|
               |main.in_v[13][4]| |main.in_v[13][5]| |main.in_v[13][6]| |main.in_v[13][7]|
               |main.in_v[13][8]| |main.in_v[13][9]| |main.in_v[13][10]| |main.in_v[13][11]|
               |main.in_v[13][12]| |main.in_v[13][13]| |main.in_v[13][14]| |main.in_v[13][15]|
               |main.in_v[13][16]| |main.in_v[13][17]| |main.in_v[13][18]| |main.in_v[13][19]|
               |main.in_v[13][20]| |main.in_v[13][21]| |main.in_v[13][22]| |main.in_v[13][23]|
               |main.in_v[13][24]| |main.in_v[13][25]| |main.in_v[13][26]| |main.in_v[13][27]|
               |main.in_v[13][28]| |main.in_v[13][29]| |main.in_v[13][30]| |main.in_v[13][31]|

               |main.in_v[14][0]| |main.in_v[14][1]| |main.in_v[14][2]| |main.in_v[14][3]|
               |main.in_v[14][4]| |main.in_v[14][5]| |main.in_v[14][6]| |main.in_v[14][7]|
               |main.in_v[14][8]| |main.in_v[14][9]| |main.in_v[14][10]| |main.in_v[14][11]|
               |main.in_v[14][12]| |main.in_v[14][13]| |main.in_v[14][14]| |main.in_v[14][15]|
               |main.in_v[14][16]| |main.in_v[14][17]| |main.in_v[14][18]| |main.in_v[14][19]|
               |main.in_v[14][20]| |main.in_v[14][21]| |main.in_v[14][22]| |main.in_v[14][23]|
               |main.in_v[14][24]| |main.in_v[14][25]| |main.in_v[14][26]| |main.in_v[14][27]|
               |main.in_v[14][28]| |main.in_v[14][29]| |main.in_v[14][30]| |main.in_v[14][31]|

               |main.in_v[15][0]| |main.in_v[15][1]| |main.in_v[15][2]| |main.in_v[15][3]|
               |main.in_v[15][4]| |main.in_v[15][5]| |main.in_v[15][6]| |main.in_v[15][7]|
               |main.in_v[15][8]| |main.in_v[15][9]| |main.in_v[15][10]| |main.in_v[15][11]|
               |main.in_v[15][12]| |main.in_v[15][13]| |main.in_v[15][14]| |main.in_v[15][15]|
               |main.in_v[15][16]| |main.in_v[15][17]| |main.in_v[15][18]| |main.in_v[15][19]|
               |main.in_v[15][20]| |main.in_v[15][21]| |main.in_v[15][22]| |main.in_v[15][23]|
               |main.in_v[15][24]| |main.in_v[15][25]| |main.in_v[15][26]| |main.in_v[15][27]|
               |main.in_v[15][28]| |main.in_v[15][29]| |main.in_v[15][30]| |main.in_v[15][31]|

               |main.x[0]| |main.x[1]| |main.x[2]| |main.x[3]|
               |main.x[4]| |main.x[5]| |main.x[6]| |main.x[7]|
               |main.x[8]| |main.x[9]| |main.x[10]| |main.x[11]|
               |main.x[12]| |main.x[13]| |main.x[14]| |main.x[15]|
               |main.x[16]| |main.x[17]| |main.x[18]| |main.x[19]|
               |main.x[20]| |main.x[21]| |main.x[22]| |main.x[23]|
               |main.x[24]| |main.x[25]| |main.x[26]| |main.x[27]|
               |main.x[28]| |main.x[29]| |main.x[30]| |main.x[31]|

               |main.y[0]| |main.y[1]| |main.y[2]| |main.y[3]|
               |main.y[4]| |main.y[5]| |main.y[6]| |main.y[7]|
               |main.y[8]| |main.y[9]| |main.y[10]| |main.y[11]|
               |main.y[12]| |main.y[13]| |main.y[14]| |main.y[15]|
               |main.y[16]| |main.y[17]| |main.y[18]| |main.y[19]|
               |main.y[20]| |main.y[21]| |main.y[22]| |main.y[23]|
               |main.y[24]| |main.y[25]| |main.y[26]| |main.y[27]|
               |main.y[28]| |main.y[29]| |main.y[30]| |main.y[31]|
               )
 :interpreted-function-alist (acl2::make-interpreted-function-alist '( ;mul
                                                                      ;;pfield::pow INV ;bad: can overflow the stack!
                                                                      pfield::minus1
                                                                      acl2::power-of-2p add PFIELD::POS-FIX) (w state))
 ;; Everything below this point consists of lists of rewrite rules to apply.  All of have been proved as theorems by ACL2.
 :global-rules '( ;; integerp rules:
                 acl2::integerp-of-bvcat
                 acl2::integerp-of-bitxor
                 acl2::integerp-of-bvnot
                 acl2::integerp-of-bvchop
                 acl2::integerp-of-bvplus
                 acl2::integerp-of-bvxor
                 acl2::integerp-of-rightrotate
                 acl2::integerp-of-+
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
                 ;;pfield::add-combine-constants
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
                 pfield::mul-combine-constants
                 pfield::mul-combine-constants-alt
                 pfield::mul-of-constant-normalize-to-fep
                 pfield::mul-of-1-arg1
                 pfield::mul-becomes-neg
                 acl2::bvchop-of-bvchop
                 acl2::getbit-of-bvchop
                 acl2::bvchop-of-bvplus-same
                 acl2::getbit-of-0-when-bitp
                 acl2::slice-becomes-getbit
                 acl2::bvchop-of-bvcat-cases-gen
                 acl2::bvcat-of-bvchop-low
                 acl2::bvcat-of-bvchop-high
                 pfield::mod-of-add
                 ;; always introduce xors:
                 pfield::xor-idiom-1
                 pfield::xor-idiom-2
                 pfield::xor-idiom-3
                 pfield::xor-idiom-3-alt
                 pfield::xor-idiom-4
                 pfield::xor-idiom-4-alt
                 pfield::xor-idiom-4-big-constant
                 r1cs::equal-of-xor-idiom
                 r1cs::equal-of-xor-idiom-alt
                 r1cs::equal-of-xor-idiom-b
                 r1cs::equal-of-xor-idiom-b-alt
                 ;; solve equalities:
                 PFIELD::EQUAL-OF-0-AND-ADD-OF-NEG-ARG1
                 ;; introduce slice:
                 bitp-of-add-of-mul-of--2-becomes-equal-of-slice
                 bitp-of-add-of-mul-of--2-becomes-equal-of-slice-extra
                 bitp-of-add-of-mul-of--2-becomes-equal-of-slice-extra-2
                 ACL2::GETBIT-OF-BVCAT-ALL
                 ACL2::BVCHOP-CHOP-LEADING-CONSTANT
                 UNICITY-OF-0
                 fix-when-integerp
                 add-of-neg-of-bvplus-lemma
                 add-of-neg-of-bvplus-lemma2
                 add-of-neg-of-bvplus-lemma3
                 add-of-neg-of-bvplus-lemma4
                 mod-of-bitxor
                 bvchop-of-if
                 ACL2::BVCHOP-OF-BVPLUS-TIGHTEN-TO-32
                 ACL2::GETBIT-OF-BVXOR
                 ACL2::IF-SAME-BRANCHES
                 ACL2::BVPLUS-OF-BVPLUS-TRIM-TO-32-ARG1
                 ACL2::BVPLUS-OF-BVPLUS-TRIM-TO-32-ARG2
                 ACL2::TRIM-OF-BVCAT ACL2::TRIM-OF-SLICE ;(acl2::trim-helper-rules) ;caused problems with bvplus?
                 combine-special
                 xor-idiom-special
                 xor-idiom-special-2
                 xor-idiom-special-3
                 unsigned-byte-p-32-of-slice-33-1
                 ACL2::GETBIT-TOO-HIGH
                 add-of-mul-of-256-becomes-bvcat
                 )
 :rule-lists '( ;; recognize bitp idioms before we start changing things:
               (r1cs::bitp-idiom-1
                r1cs::bitp-idiom-2)
               ;; introduce bvcats:
               ( ;; These get the process started, by combining 2 bits:
                add-of-mul-and-mul-when-bitps-and-adjacent-coeffs
                add-of-mul-and-mul-when-bitps-and-adjacent-coeffs-alt
                ;; We may need these, even to get the process started, if there are extra addends not involved in this cat:
                add-of-mul-and-mul-when-bitps-and-adjacent-coeffs-extra
                add-of-mul-and-mul-when-bitps-and-adjacent-coeffs-extra-alt
                ;; These 4 add a bit to the top of a bvcat:
                ;; add-of-mul-and-mul-when-bitp-and-bvcat
                ;; add-of-mul-and-mul-when-bitp-and-bvcat-extra
                ;; add-of-mul-and-mul-when-bitp-and-bvcat-alt
                ;; add-of-mul-and-mul-when-bitp-and-bvcat-extra-alt
                ;; These 8 add a bit to the bottom of a bvcat:
                add-of-mul-and-mul-when-bvcat-and-bitp ; may cause a bit to be put into the wrong bvcat?
                add-of-mul-and-mul-when-bvcat-and-bitp-alt
                add-of-mul-and-mul-when-bvcat-and-bitp-extra ; may cause a bit to be put into the wrong bvcat?
                add-of-mul-and-mul-when-bvcat-and-bitp-extra-alt
                ;; add-of-mul-of-2-and-bvcat-and-bit ; may cause a bit to be put into the wrong bvcat?
                add-of-mul-of-2-and-bvcat-and-bit-alt
                ;; add-of-mul-of-2-and-bvcat-and-bit-extra ; may cause a bit to be put into the wrong bvcat?
                add-of-mul-of-2-and-bvcat-and-bit-extra-alt
                ;; These combine 2 bvcats:
                ;; add-of-mul-and-mul-when-bvs-bvcat-version
                ;; add-of-mul-and-mul-when-bvs-bvcat-version-alt
                ;; add-of-mul-and-mul-when-bvs-bvcat-version-extra
                ;; add-of-mul-and-mul-when-bvs-bvcat-version-extra-alt
                acl2::bvcat-associative
                ;; more rules (why are these needed?)
                add-of-mul-of-65536-and-add-extra-special
                add-of-mul-of-1048576-special
                ;;add-of-mul-of-65536 ;causes problems?
                ;;add-of-mul-of-65536-and-add-extra
                ;;add-of-mul-of-1048576-and-add-extra
                )
               ;; combine xors (would like to always do this, but it interferes with bvcat reconstruction):
               ( ;; hope we get lucky and can lift the xors out of the cats and have things pair up right:
                acl2::bvcat-of-bitxor-and-bitxor
                acl2::bvcat-of-bitxor-and-bvxor
                acl2::bvcat-of-bvxor-and-bitxor
                acl2::bvcat-of-bvxor-and-bvxor)
               ;; ;; commute negs forward (needed for xor pattern and also carry bit?)
               (pfield::add-of-neg-commute   ;careful
                pfield::add-of-neg-commute-2 ;careful
                )
               ;; Get rid of more xor patterns:
;(xor-idiom-special)
               ;; introduce bvplus:  todo: do this later?
               ( ;;pfield::add-becomes-bvplus-33-extra
                ;;pfield::add-becomes-bvplus-34-extra
                ;;pfield::add-becomes-bvplus-34-special
                ;;pfield::add-becomes-bvplus-34
                ;;pfield::add-becomes-bvplus-35
                )
               ;; pull out the coeffs:
               ( ;add-of-mul-normalize-based-on-second-coeff
                pull-out-inverse-coeff-32
                pull-out-inverse-coeff-32-alt
                pull-out-inverse-coeff-32-extra
                ;;add-of-mul-of-1048576-and-add-extra ;why here too?
                )
               ;; commute negs forward and deal with carry bit:
               ( ;pfield::add-of-neg-commute   ;careful
                ;;pfield::add-of-neg-commute-2 ;careful
                bitp-of-mul-of-1/2^32-and-add-of-neg-32
                bitp-of-mul-of-1/2^32-and-add-of-neg-32-two-addends
                bvchop-32-of-add-when-unsigned-byte-p-33
                ;;this helps deal with a bitxor of add:
                mul-of--2-when-equal-of-slice
                ;; add-of-bvplus-helper-when-equal-slice-34
                ;; add-of-bvplus-helper-when-equal-slice-34-gen
                ;; add-of-bvplus-helper-when-equal-slice-33
                acl2::getbit-0-of-bvplus
                add-of-mul-of-65536-and-add-extra-special ;why needed here again?
                add-of-mul-of-65536-special
                add-of-mul-of-1048576-and-add-extra-special
                bitp-of-mul-of-1/2^32-and-add-of-neg-32-5-addends ;try
                add-helper-bv35-for-use
                add-helper-bv35-for-use-special-1
                add-helper-bv35-for-use-new
                add-helper-bv33-for-use
                add-helper-bv33-for-use-bv-version
                bitp-of-mul-of-1/2^32-and-add-of-neg-32-two-addends-with-bvplus
                bitp-of-mul-of-1/2^32-and-add-of-neg-32-two-addends
                )
               ;;todo: do we want to get rid of all adds (into bvplus) first or not?
               ;; introduce bvplus again:
               (pfield::add-becomes-bvplus-33
                pfield::add-becomes-bvplus-33-extra
                pfield::add-becomes-bvplus-34-extra
                pfield::add-becomes-bvplus-34-special
                pfield::add-becomes-bvplus-34
                pfield::add-becomes-bvplus-35
                pfield::add-becomes-bvplus-36
                bvplus-34-tighten-to-33 ;drop?
                )

               ;; ;; handle carry:
               ;; (add-of-mul-of-neg-shifted-carry-and-bvplus-34
               ;;  acl2::bvchop-of-bvplus-tighten-to-32
               ;;  r1cs::bvplus-of-bvplus-trim-to-32-arg1
               ;;  r1cs::bvplus-of-bvplus-trim-to-32-arg2)

               ;; blast the equality of the bvcat:
               (acl2::bvcat-equal-rewrite
                acl2::bvcat-equal-rewrite-alt
                )

               ;; Open the spec and finish the proof:
               (blake2s-mixing-0-4-8-12
                BLAKE::G
                pack-blake-word
                BLAKE::WORDXOR
                BLAKE::ROT-WORD
                acl2::PACKBV-LITTLE

                acl2::car-cons
                acl2::cdr-cons
                acl2::equal-of-cons
                acl2::equal-of-cons-alt
                ACL2::CDR-OF-UPDATE-NTH
                zp
                acl2::car-becomes-nth-of-0
                acl2::nth-of-cdr
                nfix
                acl2::nth-of-reverse-list
                acl2::len-of-reverse-list
                acl2::consp-of-update-nth
                acl2::consp-of-cons
                acl2::len-of-cons
                acl2::nth-of-cons
                acl2::nth-update-nth-safe

                acl2::equal-same
                acl2::packbv-opener
                acl2::bvchop-of-bvcat-cases
                acl2::slice-becomes-getbit
                acl2::getbit-of-bvxor
                acl2::bvchop-of-bvxor
                acl2::getbit-of-slice-gen

                acl2::mod-of-+-of-4294967296 ;introduce bvplus

                acl2::getbit-of-bitxor-all-cases
                acl2::getbit-of-bvcat-all
                acl2::getbit-of-0-when-bitp
                acl2::bvxor-1-becomes-bitxor
                acl2::bitxor-of-bvcat-irrel-arg1
                acl2::bitxor-of-bvcat-irrel-arg2
                acl2::bitxor-commutative-increasing-dag
                acl2::bvplus-of-plus-arg2
                acl2::bvplus-of-plus-arg3
                acl2::getbit-of-bvplus-tighten-to-32
                acl2::slice-of-bvplus-tighten-to-32
                acl2::getbit-of-0-when-bitp

                acl2::bvxor-blast
                acl2::rightrotate-open-when-constant-shift-amount
                acl2::bvcat-blast-high
                acl2::bvcat-blast-low
                acl2::bvplus-associative
                acl2::bvplus-commutative-increasing-dag
                acl2::bvplus-commutative-2-increasing-dag

                ;; now that we have substituted for the bits, recreate the bvcats:
                acl2::bvcat-of-slice-and-slice-adjacent
                acl2::bvcat-of-slice-and-getbit-adjacent
                acl2::bvcat-of-getbit-and-slice-adjacent
                acl2::bvcat-of-getbit-and-getbit-adjacent
                acl2::bvcat-of-getbit-and-x-adjacent
                acl2::bvcat-of-slice-and-x-adjacent
                acl2::bvcat-of-getbit-and-x-adjacent-2
                acl2::bvcat-of-slice-and-x-adjacent-2
                )
               ;; ;; doing this earlier may interfere with bvcat reconstruction:
               (
                ;;  ;; would be better to use these:
                acl2::bvcat-trim-arg1-dag ;does not trim bvplus, etc
                acl2::bvcat-trim-arg2-dag ;does not trim bvplus, etc
                ;;  acl2::bvcat-trim-arg1-dag-all
                ;;  acl2::bvcat-trim-arg2-dag-all
                ;;  acl2::getbit-trim-dag-all-gen
                acl2::bvcat-equal-bvcat
                acl2::bitxor-commutative-2-increasing-dag
                acl2::bitxor-commutative-increasing-dag
                acl2::bitxor-associative ;needed?
                acl2::bitxor-of-slice-arg1
                acl2::bitxor-of-slice-arg2
                ;;acl2::bitxor-trim-arg1-dag-all ;make a non-all version?
                ;;acl2::bitxor-trim-arg2-dag-all ;make a non-all version?
                bitxor-of-bvplus-tighten-arg1
                bitxor-of-bvplus-tighten-arg2
                acl2::bvplus-1-becomes-bitxor
                ;; these 2 are just for proof debugging:
                acl2::equal-of-bitxor-and-bitxor-same
                acl2::equal-of-bitxor-and-bitxor-same-alt
                acl2::bitxor-of-bvcat-irrel-arg1 ; todo make non-arith trim rules for bitxor
                acl2::bitxor-of-bvcat-irrel-arg2
                acl2::bitxor-of-getbit-arg1
                acl2::bitxor-of-getbit-arg2
                acl2::bvplus-commutative-2-increasing-dag
                acl2::bvplus-commutative-increasing-dag
                acl2::booland-of-t
                acl2::bool-fix-when-booleanp ;todo add bool-fix (and booland) to the evaluator
                )
               ))
