#|
  Book:      proof-AES
  Copyright: (c) 2005 Galois Connections, Inc.
  Author:    Lee Pike, Galois Connections, Inc. <leepike@galois.com>
|#

(in-package "ACL2")

; Edited by Matt K.:
; (include-book "make-theorems" :dir :books)
(include-book "../books/make-theorems")

;; --------------------------------------------------------
;; COMPILER OUTPUT

(include-book "AES-source-shallow-canon")
(include-book "AES-source-shallow-flatten")
;; --------------------------------------------------------


(make-thm :name |type-0-0-1-thm|
          :thm-type type
          :itr-term (and (|$itr_0_typep| x)
                         (|$itr_1_typep| y))
          :ind-term (|$ind_0_typep| (list x y))
          :enables (|$itr_0_typep| |$itr_1_typep| |$ind_0_typep|))

 (make-thm :name |comp-1-thm|
          :thm-type comp
          :itr-term (|$itr_comp_1| x y i)
          :ind-term (|$ind_comp_1| (list y x) x i))

 (make-thm :name |bitMmult-thm|
          :thm-type fn
          :itr-term (|itr_bitMmult_1| x y)
          :ind-term (|ind_bitMmult_1| (list x y)))

 (make-thm :name |type-1-1-thm|
          :thm-type type
          :itr-term (and (|$itr_1_typep| x)
                         (|$itr_1_typep| y))
          :ind-term (|$ind_1_typep| (list x y))
          :enables (|$itr_1_typep| |$ind_1_typep|))

 (make-thm :name |gtimes-thm|
          :thm-type fn
          :itr-term (|itr_gtimes_1| x y)
          :ind-term (|ind_gtimes_1| (list x y)))

 (make-thm :name |type-1-2-thm|
          :thm-type type
          :itr-term (|$itr_1_typep| x)
          :ind-term (|$ind_2_typep| x)
          :enables (|$itr_1_typep| |$ind_2_typep|))

(make-thm :name |inv-ps-thm|
          :thm-type invariant
          :itr-name |iter_ps_3|
          :ind-name |ps_2|
          :arg-types ((|$itr_1_typep| x))
          :branches (|ps_2|)
          :arg-list (x)
          :init-hist (0)
          :hist-widths (0))

 (make-thm :name |gpower-thm|
          :thm-type fn
          :itr-term (|itr_gpower_1| x y)
          :ind-term (|ind_gpower_1| (list x y)))

 (make-thm :name |ginverse-thm|
          :thm-type fn
          :itr-term (|itr_ginverse_1| x)
          :ind-term (|ind_ginverse_1| x))

 (make-thm :name |type-2-3-thm|
          :thm-type type
          :itr-term (|$itr_2_typep| x)
          :ind-term (|$ind_3_typep| x)
          :enables (|$itr_2_typep| |$ind_3_typep|))

 (make-thm :name |inv-sums-thm|
          :thm-type invariant
          :itr-name |iter_sums_3|
          :ind-name |sums_2|
          :arg-list (x)
          :arg-types ((|$itr_2_typep| x))
          :branches (|sums_2|)
          :init-hist (0)
          :hist-widths (0))

 (make-thm :name |byteSum-thm|
          :thm-type fn
          :itr-term (|itr_byteSum_1| x)
          :ind-term (|ind_byteSum_1| x))


 (make-thm :name |type-2-2-4-thm|
          :thm-type type
          :itr-term (and (|$itr_2_typep| x)
                         (|$itr_2_typep| y))
          :ind-term (|$ind_4_typep| (list x y))
          :enables (|$itr_2_typep| |$ind_4_typep|))

 (make-thm :name |comp-2-thm|
          :thm-type comp
          :itr-term (|$itr_comp_2| x y i)
          :ind-term (|$ind_comp_2| (list y x) i))

 (make-thm :name |byteDot-thm|
          :thm-type fn
          :itr-term (|itr_byteDot_1| x y)
          :ind-term (|ind_byteDot_1| (list x y)))

 (make-thm :name |type-2-3-5-thm|
          :thm-type type
          :itr-term (and (|$itr_3_typep| x)
                         (|$itr_2_typep| y))
          :ind-term (|$ind_5_typep| (list x y))
          :enables (|$itr_2_typep| |$itr_3_typep| |$ind_5_typep|))

 (make-thm :name |comp-3-thm|
          :thm-type comp
          :itr-term (|$itr_comp_3| x y i)
          :ind-term (|$ind_comp_3| (list y x) x i))

 (make-thm :name |byteMmult-thm|
          :thm-type fn
          :itr-term (|itr_byteMmult_1| x y)
          :ind-term (|ind_byteMmult_1| (list x y)))

 (make-thm :name |comp-4-thm|
          :thm-type comp
          :itr-term (|$itr_comp_4| i)
          :ind-term (|$ind_comp_4| i))

 (make-thm :name |affMat-thm|
          :thm-type fn
          :itr-term (|itr_affMat_1|)
          :ind-term (|ind_affMat_1|))

 (make-thm :name |invAffMat-thm|
          :thm-type fn
          :itr-term (|itr_invAffMat_1|)
          :ind-term (|ind_invAffMat_1|))

 (make-thm :name |affine-thm|
          :thm-type fn
          :itr-term (|itr_affine_1| x)
          :ind-term (|ind_affine_1| x))

 (make-thm :name |invAfine-thm|
          :thm-type fn
          :itr-term (|itr_invAffine_1| x)
          :ind-term (|ind_invAffine_1| x))

 (make-thm :name |sbox-thm|
          :thm-type fn
          :itr-term (|itr_sbox_1|)
          :ind-term (|ind_sbox_1|))

 (make-thm :name |invSbox-thm|
          :thm-type fn
          :itr-term (|itr_invSbox_1|)
          :ind-term (|ind_invSbox_1|))

 (make-thm :name |type3-6-thm|
          :thm-type type
          :itr-term (|$itr_3_typep| x)
          :ind-term (|$ind_6_typep| x)
          :enables (|$itr_3_typep| |$ind_6_typep|))

 (make-thm :name |comp-9-thm|
          :thm-type comp
          :itr-term (|$itr_comp_9| x i)
          :ind-term (|$ind_comp_9| x i))

 (make-thm :name |comp-8-thm|
          :thm-type comp
          :itr-term (|$itr_comp_8| x i)
          :ind-term (|$ind_comp_8| x i))

 (make-thm :name |byteSub-thm|
          :thm-type fn
          :itr-term (|itr_byteSub_1| x)
          :ind-term (|ind_byteSub_1| x))

 (make-thm :name |comp-11-thm|
          :thm-type comp
          :itr-term (|$itr_comp_11| x i)
          :ind-term (|$ind_comp_11| x i))

 (make-thm :name |comp-10-thm|
          :thm-type comp
          :itr-term (|$itr_comp_10| x i)
          :ind-term (|$ind_comp_10| x i))

 (make-thm :name |invByteSub-thm|
          :thm-type fn
          :itr-term (|itr_invByteSub_1| x)
          :ind-term (|ind_invByteSub_1| x))

 (make-thm :name |comp-13-12-thm|
          :thm-type comp
          :itr-term (|$itr_comp_13| x i)
          :ind-term (|$ind_comp_12| x i))

 (make-thm :name |shiftRow-thm|
          :thm-type fn
          :itr-term (|itr_shiftRow_1| x)
        :ind-term (|ind_shiftRow_1| x))

 (make-thm :name |comp-15-13-thm|
          :thm-type comp
          :itr-term (|$itr_comp_15| x i)
          :ind-term (|$ind_comp_13| x i))

 (make-thm :name |invShiftRow-thm|
          :thm-type fn
          :itr-term (|itr_invShiftRow_1| x)
          :ind-term (|ind_invShiftRow_1| x))

 (make-thm :name |comp-20-thm|
          :thm-type comp
          :itr-term (|$itr_comp_20| ind st i)
          :ind-term (make-rows ind 4 st i))

 (make-thm :name |comp-16-14-thm|
          :thm-type comp
          :itr-term (|$itr_comp_16| x i)
         :ind-term (|$ind_comp_14| x i))

 (make-thm :name |comp-18-thm|
          :thm-type comp
          :itr-term (|$itr_comp_18| ind st i)
          :ind-term (make-rows ind 4 st i))

 (make-thm :name |comp-17-thm|
          :thm-type comp
          :itr-term (|$itr_comp_17| vec i)
          :ind-term (c-vec-transpose-hlp 4 4 vec i))

 (make-thm :name |polyMat-thm|
          :thm-type fn
          :itr-term (|itr_polyMat_1| x)
          :ind-term (|ind_polyMat_1| x))

 (make-thm :name |comp-19-thm|
          :thm-type comp
          :itr-term (|$itr_comp_19| vec i)
          :ind-term (c-vec-transpose-hlp 4 4 vec i))

 (make-thm :name |comp-23-thm|
          :thm-type comp
          :itr-term (|$itr_comp_23| ind st i)
          :ind-term (make-rows ind 4 st i))

 (make-thm :name |comp-22-thm|
          :thm-type comp
          :itr-term (|$itr_comp_22| vec i)
          :ind-term (c-vec-transpose-hlp 4 4 vec i))

 (make-thm :name |comp-21-15-thm|
          :thm-type comp
          :itr-term (|$itr_comp_21| (c-vec-transpose-hlp 4 4 x 0) i)
          :ind-term (|$ind_comp_15| x i))

 (make-thm :name |mixColumn-thm|
          :thm-type fn
          :itr-term (|itr_mixColumn_1| x)
          :ind-term (|ind_mixColumn_1| x))

 (make-thm :name |comp_25-thm|
          :thm-type comp
          :itr-term (|$itr_comp_25| ind vec i)
          :ind-term (make-rows ind 4 vec i))

 (make-thm :name |comp-24-thm|
          :thm-type comp
          :itr-term (|$itr_comp_24| vec i)
          :ind-term (c-vec-transpose-hlp 4 4 vec i))

 (make-thm :name |comp_28-thm|
          :thm-type comp
          :itr-term (|$itr_comp_28| ind vec i)
          :ind-term (make-rows ind 4 vec i))

 (make-thm :name |comp-27-thm|
          :thm-type comp
          :itr-term (|$itr_comp_27| vec i)
          :ind-term (c-vec-transpose-hlp 4 4 vec i))

 (make-thm :name |comp_26-16-thm|
          :thm-type comp
          :itr-term (|$itr_comp_26| (c-vec-transpose-hlp 4 4 vec 0) i)
          :ind-term (|$ind_comp_16| vec i))

 (make-thm :name |invMixColumn-thm|
          :thm-type fn
          :itr-term (|itr_invMixColumn_1| x)
          :ind-term (|ind_invMixColumn_1| x))

 (make-thm :name |type3-3-7-thm|
          :thm-type type
          :itr-term (and (|$itr_3_typep| x)
                         (|$itr_3_typep| y))
          :ind-term (|$ind_7_typep| (list x y))
          :enables (|$itr_3_typep| |$ind_7_typep|))

 (make-thm :name |xorS-thm|
          :thm-type fn
          :itr-term (|itr_xorS_1| x y)
          :ind-term (|ind_xorS_1| (list x y)))

 (make-thm :name |round-thm|
          :thm-type fn
          :itr-term (|itr_round_1| x y)
          :ind-term (|ind_round_1| (list x y)))

 (make-thm :name |finalRound-thm|
          :itr-term (|itr_finalRound_1| x y)
          :ind-term (|ind_finalRound_1| (list x y)))

 (make-thm :name |invRound-thm|
          :thm-type fn
          :itr-term (|itr_invRound_1| x y)
          :ind-term (|ind_invRound_1| (list x y)))

 (make-thm :name |invFinalRound-thm|
          :thm-type fn
          :itr-term (|itr_invFinalRound_1| x y)
          :ind-term (|ind_invFinalRound_1| (list x y)))

 (make-thm :name |type-4-8-thm|
          :thm-type type
          :ind-term (|$ind_8_typep| x)
          :itr-term (|$itr_4_typep| x)
          :enables (|$itr_4_typep| |$ind_8_typep|))

 (make-thm :name |inv-rnds-6-4-thm|
          :thm-type invariant
          :itr-name |iter_rnds_6|
          :ind-name |rnds_4|
          :arg-list (|tmp_290| |rndKeys_3| |initialKey_2|)
          :arg-types ((|$itr_3_typep| |initialKey_2|)
                      (|$itr_4_typep| |rndKeys_3|)
                      (|$itr_3_typep| |tmp_290|))
          :branches (|rnds_4|)
          :init-hist ( ( ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)))
          :hist-widths (0))

 (make-thm :name |type-5-3-9-type|
          :thm-type type
          :itr-term (and (|$itr_3_typep| x)
                         (|$itr_5_typep| y))
          :ind-term (|$ind_9_typep| (list x y))
          :enables (|$ind_9_typep| |$itr_5_typep| |$itr_3_typep|))

 (make-thm :name |rounds-thm|
          :thm-type fn
          :itr-term (|itr_rounds_1| x y)
          :ind-term (|ind_rounds_1| (list x y)))

 (make-thm :name |inv-rnds-5-3-thm|
          :thm-type invariant
          :itr-name |iter_rnds_5|
          :ind-name |rnds_3|
          :arg-list (|tmp_283| |invRndKeys_2| |finalKey_2|)
          :arg-types ((|$itr_3_typep| |finalKey_2|)
                      (|$itr_4_typep| |invRndKeys_2|)
                      (|$itr_3_typep| |tmp_283|))
          :branches (|rnds_3|)
          :init-hist ( ( ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)))
          :hist-widths (0))

 (make-thm :name |comp-29-thm|
          :thm-type comp
          :itr-term (|$itr_comp_29| vec i)
          :ind-term (c-vec-reverse-hlp 9 vec i))

 (make-thm :name |comp-30-17-thm|
          :thm-type comp
          :itr-term (|$itr_comp_30| (c-vec-reverse-hlp 9 (nth 1 y) 0) i)
          :ind-term (|$ind_comp_17| y i))

 (make-thm :name |invRounds-thm|
           :thm-type fn
           :itr-term (|itr_invRounds_1| x y)
           :ind-term (|ind_invRounds_1| (list x y)))

  (make-thm :name |xorB4-thm|
           :thm-type fn
           :itr-term (|itr_xorB4_1| x y)
           :ind-term (|ind_xorB4_1| (list x y)))

 (make-thm :name |comp-31-18|
          :thm-type comp
          :itr-term (|$itr_comp_31| x i)
          :ind-term (|$ind_comp_18| x i))

 (make-thm :name |subByte-thm|
          :thm-type fn
          :itr-term (|itr_subByte_1| x)
          :ind-term (|ind_subByte_1| x))

 (make-thm :name |rcon-thm|
          :thm-type fn
          :itr-term (|itr_rcon_1| x)
          :ind-term (|ind_rcon_1| x))

 (make-thm :name |type-1-2-2-10-thm|
          :thm-type type
          :itr-term (and (|$itr_2_typep| z)
                         (|$itr_2_typep| y)
                         (|$itr_1_typep| x))
          :ind-term (|$ind_10_typep| (list x y z))
          :enables (|$ind_10_typep| |$itr_2_typep| |$itr_1_typep|))

 (make-thm :name |nextWord-thm|
          :thm-type fn
          :itr-term (|itr_nextWord_1| x y z)
          :ind-term (|ind_nextWord_1| (list x y z)))

(make-thm :name |inv-3-2-thm|
          :thm-type invariant
          :itr-name |iter_w_3|
          :ind-name |w_2|
          :arg-list  (k)
          :arg-types ((|$itr_3_typep| k))
          :branches (|w_2|)
          :init-hist ( ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0))
          :hist-widths (6))

(make-thm :name |type-6-11-thm|
          :thm-type type
          :itr-term (|$itr_6_typep| x)
          :ind-term (|$ind_11_typep| x)
          :enables (|$itr_6_typep| |$ind_11_typep|))


 (make-thm :name |comp_35-thm|
          :thm-type comp
          :itr-term (|$itr_comp_35| ind vec i)
          :ind-term (make-rows ind 4 vec i))

 (make-thm :name |comp_34-thm|
          :thm-type comp
          :itr-term (|$itr_comp_34| vec i)
          :ind-term (c-vec-transpose-hlp 4 4 vec i))

(make-thm :name |takes-w_2|
          :thm-type takes
          :take-depth 44
          :hist-width 64
          :invar-thm |inv-3-2-thm|
          :itr-name |iter_w_3|
          :arg-list (k)
          :branches (|w_2|)
          :arg-types ((|$itr_3_typep| k))
          :ind-name |$ind_takes_1|
          :ind-loop |w_2|
          :init-hist ( ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)
      ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0) ( 0 0 0 0)))

(make-thm :name |key-exp-type|
          :thm-type vector-split
          :type1 |$itr_6_typep|
          :type2 |$itr_3_typep|
          :vector-size 4
          :vector-length 16)

(make-thm :name |keyExpansion-thm|
          :thm-type fn
          :itr-term (|itr_keyExpansion_1| x)
          :ind-term (|ind_keyExpansion_1| x))

(make-thm :name |comp_33-19-thm|
          :thm-type comp
          :itr-term (|$itr_comp_33| (c-vec-split 4 (|itr_keyExpansion_1| x)) i)
          :ind-term (|$ind_comp_19| x i))

(make-thm :name |keySchedule-thm|
          :itr-term (|itr_keySchedule_1| x)
          :ind-term (|ind_keySchedule_1| x))

(make-thm :name |comp_37-thm|
          :thm-type comp
          :itr-term (|$itr_comp_37| ind vec i)
          :ind-term (make-rows ind 4 vec i))

(make-thm :name |comp_36-thm|
          :thm-type comp
          :itr-term (|$itr_comp_36| vec i)
          :ind-term (c-vec-transpose-hlp 4 4 vec i))

(make-thm :name |stripe-thm|
          :thm-type fn
          :itr-term (|itr_stripe_1| x)
          :ind-term (|ind_stripe_1| x))

(make-thm :name |comp_39-thm|
          :thm-type comp
          :itr-term (|$itr_comp_39| ind vec i)
          :ind-term (make-rows ind 4 vec i))

(make-thm :name |comp_38-thm|
          :thm-type comp
          :itr-term (|$itr_comp_38| vec i)
          :ind-term (c-vec-transpose-hlp 4 4 vec i))

(make-thm :name |unstripe-thm|
          :thm-type fn
          :itr-term (|itr_unstripe_1| x)
          :ind-term (|ind_unstripe_1| x))

(make-thm :name |type-6-5-12-thm|
          :thm-type type
          :itr-term (and (|$itr_6_typep| x)
                         (|$itr_5_typep| y))
          :ind-term (|$ind_12_typep| (list x y))
          :enables (|$ind_12_typep| |$itr_5_typep| |$itr_6_typep|))

(make-thm :name |encrypt-thm|
          :itr-term (|itr_encrypt_1| x y)
          :ind-term (|ind_encrypt_1| (list x y)))

(make-thm :name |decrypt-thm|
          :thm-type fn
          :itr-term (|itr_decrypt_1| x y)
          :ind-term (|ind_decrypt_1| (list x y)))

(make-thm :name |type-6-6-thm|
          :thm-type type
          :itr-term (and (|$itr_6_typep| x)
                         (|$itr_6_typep| y))
          :ind-term (|$ind_13_typep| (list x y))
          :enables (|$itr_6_typep| |$ind_13_typep|))

(make-thm :name |aes-thm|
          :thm-type fn
          :itr-term (|itr_aes| x y)
          :ind-term (|ind_aes| (list x y)))

(make-thm :name |sea-thm|
          :thm-type fn
          :itr-term (|itr_sea| x y)
          :ind-term (|ind_sea| (list x y)))
