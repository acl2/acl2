; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

;; STATUS: COMPLETE

(include-book "support-blake2s")
(include-book "kestrel/axe/r1cs/lift-r1cs" :dir :system)
(include-book "kestrel/axe/r1cs/axe-prover-r1cs" :dir :system)
(include-book "kestrel/crypto/r1cs/gadgets/boolean-alt-rules" :dir :system)
(include-book "projects/bls12-377-curves/primes/bls12-377-prime" :dir :system)

;;NOTE: Manually replaced R1CS::|Input0| by 1
(defconst *add-plus-3-constraints*
  '(((R1CS::A (1 1)
              (-1 R1CS::|Aux0|))
     (R1CS::B (1 R1CS::|Aux0|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux1|))
     (R1CS::B (1 R1CS::|Aux1|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux2|))
     (R1CS::B (1 R1CS::|Aux2|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux3|))
     (R1CS::B (1 R1CS::|Aux3|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux4|))
     (R1CS::B (1 R1CS::|Aux4|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux5|))
     (R1CS::B (1 R1CS::|Aux5|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux6|))
     (R1CS::B (1 R1CS::|Aux6|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux7|))
     (R1CS::B (1 R1CS::|Aux7|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux8|))
     (R1CS::B (1 R1CS::|Aux8|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux9|))
     (R1CS::B (1 R1CS::|Aux9|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux10|))
     (R1CS::B (1 R1CS::|Aux10|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux11|))
     (R1CS::B (1 R1CS::|Aux11|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux12|))
     (R1CS::B (1 R1CS::|Aux12|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux13|))
     (R1CS::B (1 R1CS::|Aux13|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux14|))
     (R1CS::B (1 R1CS::|Aux14|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux15|))
     (R1CS::B (1 R1CS::|Aux15|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux16|))
     (R1CS::B (1 R1CS::|Aux16|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux17|))
     (R1CS::B (1 R1CS::|Aux17|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux18|))
     (R1CS::B (1 R1CS::|Aux18|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux19|))
     (R1CS::B (1 R1CS::|Aux19|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux20|))
     (R1CS::B (1 R1CS::|Aux20|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux21|))
     (R1CS::B (1 R1CS::|Aux21|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux22|))
     (R1CS::B (1 R1CS::|Aux22|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux23|))
     (R1CS::B (1 R1CS::|Aux23|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux24|))
     (R1CS::B (1 R1CS::|Aux24|))
     (R1CS::C))
    ((R1CS::A)
     (R1CS::B)
     (R1CS::C (1 R1CS::|Aux0|)
              (2 R1CS::|Aux1|)
              (4 R1CS::|Aux2|)
              (8 R1CS::|Aux3|)
              (16 R1CS::|Aux4|)
              (32 R1CS::|Aux5|)
              (64 R1CS::|Aux6|)
              (128 R1CS::|Aux7|)
              (1 R1CS::|Aux8|)
              (2 R1CS::|Aux9|)
              (4 R1CS::|Aux10|)
              (8 R1CS::|Aux11|)
              (16 R1CS::|Aux12|)
              (32 R1CS::|Aux13|)
              (64 R1CS::|Aux14|)
              (128 R1CS::|Aux15|)
              (-1 R1CS::|Aux16|)
              (8444461749428370424248824938781546531375899335154063827935233455917409239039
               R1CS::|Aux17|)
              (8444461749428370424248824938781546531375899335154063827935233455917409239037
               R1CS::|Aux18|)
              (8444461749428370424248824938781546531375899335154063827935233455917409239033
               R1CS::|Aux19|)
              (8444461749428370424248824938781546531375899335154063827935233455917409239025
               R1CS::|Aux20|)
              (8444461749428370424248824938781546531375899335154063827935233455917409239009
               R1CS::|Aux21|)
              (8444461749428370424248824938781546531375899335154063827935233455917409238977
               R1CS::|Aux22|)
              (8444461749428370424248824938781546531375899335154063827935233455917409238913
               R1CS::|Aux23|)
              (8444461749428370424248824938781546531375899335154063827935233455917409238785
               R1CS::|Aux24|)))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux25|))
     (R1CS::B (1 R1CS::|Aux25|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux26|))
     (R1CS::B (1 R1CS::|Aux26|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux27|))
     (R1CS::B (1 R1CS::|Aux27|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux28|))
     (R1CS::B (1 R1CS::|Aux28|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux29|))
     (R1CS::B (1 R1CS::|Aux29|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux30|))
     (R1CS::B (1 R1CS::|Aux30|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux31|))
     (R1CS::B (1 R1CS::|Aux31|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux32|))
     (R1CS::B (1 R1CS::|Aux32|))
     (R1CS::C))
    ((R1CS::A (1 1)
              (-1 R1CS::|Aux33|))
     (R1CS::B (1 R1CS::|Aux33|))
     (R1CS::C))
    ((R1CS::A)
     (R1CS::B)
     (R1CS::C (3 1)
              (1 R1CS::|Aux16|)
              (2 R1CS::|Aux17|)
              (4 R1CS::|Aux18|)
              (8 R1CS::|Aux19|)
              (16 R1CS::|Aux20|)
              (32 R1CS::|Aux21|)
              (64 R1CS::|Aux22|)
              (128 R1CS::|Aux23|)
              (-1 R1CS::|Aux25|)
              (8444461749428370424248824938781546531375899335154063827935233455917409239039
               R1CS::|Aux26|)
              (8444461749428370424248824938781546531375899335154063827935233455917409239037
               R1CS::|Aux27|)
              (8444461749428370424248824938781546531375899335154063827935233455917409239033
               R1CS::|Aux28|)
              (8444461749428370424248824938781546531375899335154063827935233455917409239025
               R1CS::|Aux29|)
              (8444461749428370424248824938781546531375899335154063827935233455917409239009
               R1CS::|Aux30|)
              (8444461749428370424248824938781546531375899335154063827935233455917409238977
               R1CS::|Aux31|)
              (8444461749428370424248824938781546531375899335154063827935233455917409238913
               R1CS::|Aux32|)
              (8444461749428370424248824938781546531375899335154063827935233455917409238785
               R1CS::|Aux33|)))))

;todo: use vars in the r1cs package.  also, some functions expect keyword vars!
(defconst *add-plus-3-vars*
  (acl2::make-var-names '|Aux| 34))

(local
 (r1cs::lift-r1cs *add-plus-3-r1cs*
                      *add-plus-3-vars*
                      *add-plus-3-constraints*
                      8444461749428370424248824938781546531375899335154063827935233455917409239041
                      :monitor '(;equal-of-0-and-mul-of-add-of-1-and-neg-same
                                 )
                      :remove-rules '(pfield::neg-of-mul-when-constant ;makes it harder to move terms to the other side?
                                      pfield::equal-of-add-of-add-of-neg-arg2-arg2 ;for now, to try to combine more stuff
                                      PFIELD::ADD-COMMUTATIVE-2-AXE
                                      PFIELD::ADD-COMMUTATIVE-axe
                                     )
                      :extra-rules '(pfield::introduce-bitp-alt-2-alt
                                     pfield::introduce-bitp-alt-2
                                     primes::primep-of-bls12-377-scalar-field-prime-constant)
                      :print t
                      :count-hits t))


;; Essentially says that c = 3+a+b
(defund add-plus-3-spec (a7 a6 a5 a4 a3 a2 a1 a0
                           b7 b6 b5 b4 b3 b2 b1 b0
                           c7 c6 c5 c4 c3 c2 c1 c0)
  (declare (xargs :guard (and (bitp a7) (bitp a6) (bitp a5) (bitp a4) (bitp a3) (bitp a2) (bitp a1) (bitp a0)
                              (bitp b7) (bitp b6) (bitp b5) (bitp b4) (bitp b3) (bitp b2) (bitp b1) (bitp b0)
                              (bitp c7) (bitp c6) (bitp c5) (bitp c4) (bitp c3) (bitp c2) (bitp c1) (bitp c0))))

  (equal (acl2::bvcat2 1 c7
                       1 c6
                       1 c5
                       1 c4
                       1 c3
                       1 c2
                       1 c1
                       1 c0)
         ;; todo: pull out into a function:
         (acl2::bvplus 8
                       3
                       (acl2::bvplus 8 (acl2::bvcat2 1 b7
                                                     1 b6
                                                     1 b5
                                                     1 b4
                                                     1 b3
                                                     1 b2
                                                     1 b1
                                                     1 b0)
                                     (acl2::bvcat2 1 a7
                                                   1 a6
                                                   1 a5
                                                   1 a4
                                                   1 a3
                                                   1 a2
                                                   1 a1
                                                   1 a0)))))

;; tricky issues:
;; - 8-bit vs 9-bit sums (carrry)
;; - no single variable actually contains the sum, so can't subst for vars.  have to bit-blast (see below).
;; - whether to turn bvplus into add or add into bvplus

;; Proves that the R1CS implies the spec:
;; TODO: Characterize Aux33?
(acl2::prove-implication-with-r1cs-prover *add-plus-3-r1cs*
                                           ;; TODO: Why the ACL2 package?
                                           '(add-plus-3-spec |Aux7| |Aux6| |Aux5| |Aux4| |Aux3| |Aux2| |Aux1| |Aux0|
                                                             |Aux15| |Aux14| |Aux13| |Aux12| |Aux11| |Aux10| |Aux9| |Aux8|
                                                             |Aux32| |Aux31| |Aux30| |Aux29| |Aux28| |Aux27| |Aux26| |Aux25|)
                                           :interpreted-function-alist (acl2::make-interpreted-function-alist '(neg pfield::add pfield::pos-fix ACL2::BVCAT acl2::logapp ACL2::EXPT2$INLINE ACL2::LOGHEAD$INLINE acl2::imod$inline ACL2::POWER-OF-2P)
                                                                                                              (w state))
                                           :monitor '(acl2::bvcat-equal-rewrite
                                                      acl2::bvcat-equal-rewrite-alt)
                                           :no-splitp t
                                           :rule-lists '( ;; first open the r1cs and substitute, keeping the spec closed to keep the dag small:
                                                         ( ;acl2::mimcsponge-1-1-0k-holdsp
                                                          (acl2::lookup-rules)
                                                          acl2::implies-opener
                                                          ;;bvcat-intro-4-2-simple
                                                          ;;bvcat-intro-4-2
                                                          pfield::add-of-mod-arg1
                                                          pfield::add-of-mod-arg2
                                                          pfield::mul-of-mod-arg1
                                                          pfield::mul-of-mod-arg1
                                                          acl2::integerp-of-bvcat
                                                          add-of-bvcat-of-add-of-mul-combine
                                                          add-of-bvcat-of-add-of-mul-combine-simp-alt
                                                          add-of-bvcat-of-add-of-mul-combine-simp
                                                          mul-of---arg1
                                                          pfield::mul-when-constant-becomes-neg-of-mul
                                                          ;;pfield::neg-when-constant-arg1
                                                          ;;move-negation-1
                                                          add-of-mul-of-2-becomes-bvcat
                                                          add-of-add-of-mul-of-2-becomes-add-of-bvcat
                                                          pfield::add-of-neg-and-neg
                                                          pfield::neg-of-mod
                                                          )
                                                         ;; next, move the negated addends
                                                         ((pfield::prime-field-proof-rules)
                                                          pfield::equal-of-add-of-add-of-neg-arg2-arg2
                                                          acl2::ifix-when-integerp
                                                          pfield::integerp-of-add
                                                          pfield::neg-of-0
                                                          pfield::mod-of-add
                                                          acl2::if-of-t-and-nil-when-booleanp
                                                          (acl2::booleanp-rules)
                                                          acl2::integerp-of-bvcat
                                                          acl2::mod-when-<
                                                          acl2::bvcat-numeric-bound
                                                          ;acl2::not-<-of-bvcat-and-0
                                                          acl2::rationalp-when-integerp
                                                          pfield::equal-of-0-and-add-of-neg-arg1
                                                          pfield::equal-of-0-and-add-of-neg-arg2
                                                          pfield::fep-of-bvcat
                                                          pfield::equal-of-0-and-add-of-add-of-neg-lemma)
                                                         ;; now, turn additions into bvplus
                                                         (acl2::adding-8-idiom ;split out the carry
                                                          acl2::adding-8-idiom-alt ;split out the carry
                                                          acl2::bitp-of-getbit
                                                          (acl2::unsigned-byte-p-rules))
                                                         ;; now blast the equalities of bvcats, since the prover only substitutes for variables:
                                                         (acl2::bvcat-equal-rewrite ; restrict to a cat nest of vars?
                                                          acl2::bvcat-equal-rewrite-alt ; restrict to a cat nest of vars?
                                                          acl2::bvchop-of-bvcat-cases
                                                          (acl2::unsigned-byte-p-rules)
                                                          acl2::if-of-nil-becomes-booland ;shouldn't be needed to avoid splits?
                                                          (acl2::booleanp-rules)
                                                          acl2::bitp-of-getbit
                                                          acl2::bitp-of-bvchop-of-1
                                                          bvchop-of-1-when-bitp
                                                          acl2::slice-becomes-getbit
                                                          acl2::bvchop-1-becomes-getbit
                                                          ;reassemble larger bvs:
                                                          acl2::bvcat-of-getbit-and-getbit-adjacent
                                                          acl2::bvcat-of-slice-and-slice-adjacent
                                                          acl2::bvcat-of-getbit-and-slice-adjacent
                                                          acl2::bvcat-of-slice-and-getbit-adjacent
                                                          acl2::getbit-of-bvchop
                                                          )
                                                         ;; ;; now open the spec:
                                                         (add-plus-3-spec
                                                          acl2::bvcat-of-getbit-and-getbit-adjacent
                                                          acl2::bvcat-of-slice-and-slice-adjacent
                                                          acl2::bvcat-of-getbit-and-slice-adjacent
                                                          acl2::bvcat-of-slice-and-getbit-adjacent
                                                          acl2::slice-becomes-bvchop
                                                          acl2::bvchop-of-bvplus-same
                                                          acl2::bvcat-of-bvchop-low
                                                          acl2::bvcat-of-bvchop-high
                                                          acl2::bvcat-of-getbit-and-x-adjacent-2
                                                          acl2::bvcat-of-getbit-and-x-adjacent
                                                          acl2::bvcat-of-slice-and-x-adjacent-2
                                                          acl2::bvcat-of-slice-and-x-adjacent
                                                          acl2::equal-same)
                                                         ))

;; TODO: Add proof going in the other (less important?) direction.
