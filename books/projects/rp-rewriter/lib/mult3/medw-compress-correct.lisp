
; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2020 Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Mertcan Temel         <mert@utexas.edu>

(in-package "RP")

(include-book "fnc-defs")

(include-book "medw-compress")
(include-book "summation-tree-meta-fncs-correct")

(include-book "lemmas")
(include-book "lemmas-2")

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

(local
 (fetch-new-theory
  (include-book "arithmetic-5/top" :dir :system)
  use-arith-5
  :disabled t))

(local
 (in-theory (enable ex-from-rp-loose-is-ex-from-rp)))

(local
 (in-theory (enable rp-trans trans-list)))

(create-regular-eval-lemma c 4 mult-formula-checks)
(create-regular-eval-lemma s 3 mult-formula-checks)
(create-regular-eval-lemma s-c-res 3 mult-formula-checks)
(create-regular-eval-lemma and-list 2 mult-formula-checks)
(create-regular-eval-lemma -- 1 mult-formula-checks)

(local
 (in-theory (disable (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                     (:DEFINITION ACL2::APPLY$-BADGEP)
                     (:DEFINITION SUBSETP-EQUAL)
                     (:DEFINITION MEMBER-EQUAL)
                     (:REWRITE DEFAULT-CDR)
                     (:REWRITE ACL2::SUBSETP-REFLEXIVE-LEMMA)
                     (:REWRITE
                      ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1))))

(defret create-c-instance-medwc-filtered-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms s-lst a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a))
           (and (equal (sum-list-eval res-c-lst a)
                       (f2 (sum (sum-list-eval s-lst a)
                                (sum-list-eval pp-lst a)
                                (sum-list-eval c-lst a))))
                (valid-sc-subterms res-c-lst a)))
  :fn create-c-instance-medwc-filtered
  :hints (("Goal"
           :do-not-induct t
           :expand ((:free (x) (sum-list-eval (list x) a)))
           :in-theory (e/d* (create-c-instance-medwc-filtered
                             regular-eval-lemmas

                             regular-eval-lemmas-with-ex-from-rp
                             )
                            (NOT-INCLUDE-RP-MEANS-VALID-SC
                             NOT-INCLUDE-RP-MEANS-VALID-SC-LST
                             INCLUDE-FNC-SUBTERMS
                             SUM-LIST-EVAL
                             valid-sc-subterms
                             )))))

(local
 (defthmd rp-evlt-of-ex-from-rp-reverse-atom
   (implies (syntaxp (atom term))
            (equal (rp-evl (rp-trans term) a)
                   (rp-evl (rp-trans (ex-from-rp term))
                           a)))))

(defret medw-compress-safe-cons-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (equal (sum-list-eval res a)
                       (sum (rp-evlt e a)
                            (sum-list-eval lst a)))
                (implies (and (valid-sc e a)
                              (valid-sc-subterms lst a))
                         (valid-sc-subterms res a))))
  :fn medw-compress-safe-cons
  :hints (("Goal"
           :do-not-induct t
           :expand ((SUM-LIST-EVAL (CONS E LST) A)
                    (SUM-LIST-EVAL LST A))
           :in-theory (e/d* (medw-compress-safe-cons
                             regular-eval-lemmas
                             rp-evlt-of-ex-from-rp-reverse-atom
                             regular-eval-lemmas-with-ex-from-rp
                             )
                            (NOT-INCLUDE-RP-MEANS-VALID-SC
                             rp-evlt-of-ex-from-rp
                             rp-trans
                             rp-equal
                             rp-equal-cnt
                             (:REWRITE IFIX-OPENER)
                             (:REWRITE LIGHT-PP-TERM-P-INTEGERP)
                             (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                             (:REWRITE MINUS-OF-MINUS)
                             (:DEFINITION VALID-SC)
                             (:DEFINITION EX-FROM-RP)
                             (:DEFINITION EVAL-AND-ALL)
                             (:REWRITE NOT-INCLUDE-RP)
                             (:REWRITE VALID-SC-EX-FROM-RP)
                             (:REWRITE MINUS-OF-SUM)
                             (:DEFINITION INCLUDE-FNC)
                             (:REWRITE VALID-SC-CADR)
                             NOT-INCLUDE-RP-MEANS-VALID-SC-LST
                             INCLUDE-FNC-SUBTERMS
                             SUM-LIST-EVAL
                             VALID-SC-SUBTERMS-CONS
                             valid-sc-subterms
                             )))))

(local
 (encapsulate
   nil
   (local
    (use-arith-5 t))

   (defthm m2-of-repeated-dummy-0
     (EQUAL (M2 (SUM Y Y)) 0)
     :hints (("Goal"
              :in-theory (e/d (m2 sum f2)
                              (mod2-is-m2
                               +-IS-SUM
                               floor2-if-f2)))))
   (defthm m2-of-repeated-dummy-1
     (equal (m2 (sum y y x z))
            (m2 (sum x z)))
     :hints (("Goal"
              :in-theory (e/d () ()))))))

(local
 (encapsulate
   nil
   (local
    (use-arith-5 t))

   (defthm ifix-of-sum
     (equal (ifix (sum x y))
            (sum x y))
     :hints (("Goal"
              :in-theory (e/d (sum) (+-IS-SUM)))))

   (defthm f2-of-repeated
     (equal (f2 (sum x x y))
            (sum x (f2 y)))
     :hints (("Goal"
              :in-theory (e/d (f2 m2 sum)
                              (+-IS-SUM mod2-is-m2
                                        floor2-if-f2)))))

   (defthm ifix-of---
     (equal (ifix (-- x))
            (-- x)))

   (defthm --of-sum
     (equal (-- (sum x y))
            (sum (-- x) (-- y))))

   (defthm --of---
     (equal (-- (-- x))
            (ifix x)))

   (defthm equal-of-m2-dummy1
     (equal (equal (m2 (sum x a))
                   (m2 (sum y z a)))
            (equal (m2 (sum x))
                   (m2 (sum y z)))))

   (defthm m2-of-negated-dummy1
     (equal (m2 (sum x y (-- a)))
            (m2 (sum x y a))))

   ;; (local
   ;;  (defthmd m2-of-f2-of-the-same-lemma
   ;;    (implies (case-split (evenp a))
   ;;             (equal (f2 (sum x a))
   ;;                    (sum (f2 (ifix x))))
   ;;    :hints (("Goal"
   ;;             :in-theory (e/d (f2 sum ifix)
   ;;                             (floor2-if-f2 mod2-is-m2
   ;;                                           +-IS-SUM))))))

   ;; (defthm m2-of-f2-of-the-same
   ;;   (equal (equal (m2 (f2 (sum x a)))
   ;;                 (m2 (f2 (sum y a))))
   ;;          (equal (m2 (f2 x))
   ;;                 (m2 (f2 y))))
   ;;   :hints (("Goal"
   ;;            :cases ((evenp a) (oddp a))
   ;;            :in-theory (e/d (m2 f2 sum ifix)
   ;;                            (+-IS-SUM
   ;;                             floor2-if-f2
   ;;                             mod2-is-m2)))))

   (defthm dummy-lemma1
     (implies (equal (sum x x) (sum (-- x) (-- x)))
              (equal (ifix x) 0))

     :rule-classes :forward-chaining
     :hints (("Goal"
              :in-theory (e/d (sum --)
                              (+-IS-SUM ifix)))))

   (defthm dummy-lemma2
     (implies (equal (sum (-- x) (-- x)) 0)
              (equal (ifix x) 0))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :in-theory (e/d (sum --)
                              (+-IS-SUM ifix)))))

   (defthm dummy-lemma3
     (implies (equal (ifix x) 0)
              (equal (-- x) 0))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :in-theory (e/d (sum --)
                              (+-IS-SUM ifix)))))

   (defthmd dummy-lemma4
     (implies (equal (ifix x) 0)
              (equal (sum x other) (ifix other)))
     :hints (("Goal"
              :in-theory (e/d (sum --)
                              (+-IS-SUM ifix)))))

   (defthm dummy-lemma5
     (implies (equal (ifix x) 0)
              (equal (m2 x) 0))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :in-theory (e/d (m2 sum --)
                              (mod2-is-m2 +-IS-SUM ifix)))))

   ))

(defret medw-compress-c-arg-lst-aux-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (booleanp c-is-signed)
                (booleanp sign-matters)
                (valid-sc c a)
                (valid-sc-subterms cur-c-c-lst a)
                compressed)
           (and (implies sign-matters
                         (equal (sum-list-eval new-cur-c-c-lst a)
                                (sum (if c-is-signed
                                         (-- (rp-evlt c a))
                                       (rp-evlt c a))
                                     (if c-is-signed
                                         (-- (rp-evlt c a))
                                       (rp-evlt c a))
                                     (sum-list-eval cur-c-c-lst a))))
                (implies (not sign-matters)
                         (equal (m2 (sum-list-eval new-cur-c-c-lst a))
                                (m2 (sum-list-eval cur-c-c-lst a))))
                (implies (not sign-matters)
                         (or (equal (sum-list-eval new-cur-c-c-lst a)
                                    (sum (-- (rp-evlt c a))
                                         (-- (rp-evlt c a))
                                         (sum-list-eval cur-c-c-lst a)))
                             (equal (sum-list-eval new-cur-c-c-lst a)
                                    (sum (rp-evlt c a)
                                         (rp-evlt c a)
                                         (sum-list-eval cur-c-c-lst a)))))

                #|(equal (m2 (f2 ))
                (m2 (sum (rp-evlt c a)
                (f2 (sum-list-eval cur-c-c-lst a)))))||#
                (implies t
                         (valid-sc-subterms NEW-CUR-C-C-LST a))))
  :fn medw-compress-c-arg-lst-aux-aux
  :hints (("Goal"
           :do-not-induct t
           :induct (medw-compress-c-arg-lst-aux-aux c c-is-signed cur-c-c-lst sign-matters)
           :in-theory (e/d* (medw-compress-c-arg-lst-aux-aux
                             (:REWRITE
                              REGULAR-RP-EVL-OF_--_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE RP-EVL-OF----WHEN-MULT-FORMULA-CHECKS)
                             rp-evlt-of-ex-from-rp-reverse)
                            (RP-EVL-OF-EX-FROM-RP
                             ex-from-rp
                             rp-equal
                             rp-trans
                             rp-equal-cnt
                             (:REWRITE MINUS-OF-MINUS)
                             (:REWRITE IFIX-OPENER)
                             (:REWRITE LIGHT-PP-TERM-P-INTEGERP)
                             (:DEFINITION VALID-SC)
                             (:DEFINITION INCLUDE-FNC)
                             (:REWRITE CAR-OF-EX-FROM-RP-IS-NOT-RP)
                             (:DEFINITION RP-TERMP)
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                             (:REWRITE VALID-SC-EX-FROM-RP)
                             (:REWRITE MINUS-OF-SUM)
                             (:REWRITE EX-FROM-SYNP-LEMMA1)
                             (:DEFINITION IS-SYNP$INLINE)
                             (:REWRITE
                              CREATE-LIST-INSTANCE-EQUALS-NIL-IMPLIES)
                             (:REWRITE DEFAULT-CAR)
                             RP-EVLT-OF-EX-FROM-RP)))))

(defret medw-compress-c-arg-lst-aux-aux-correct-corol
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (booleanp c-is-signed)
                (booleanp sign-matters)
                (valid-sc c a)
                (valid-sc-subterms cur-c-c-lst a)
                compressed
                (not sign-matters))
           (and (implies
                 (case-split (not (equal (sum-list-eval new-cur-c-c-lst a)
                                         (sum (-- (rp-evlt c a))
                                              (-- (rp-evlt c a))
                                              (sum-list-eval cur-c-c-lst a)))))
                 (equal (sum-list-eval new-cur-c-c-lst a)
                        (sum (rp-evlt c a)
                             (rp-evlt c a)
                             (sum-list-eval cur-c-c-lst a))))
                (implies (equal (ifix (rp-evlt c a)) 0)
                         (equal (sum-list-eval new-cur-c-c-lst a)
                                (sum-list-eval cur-c-c-lst a)))
                ))

  :fn medw-compress-c-arg-lst-aux-aux
  :hints (("Goal"
           :use ((:instance medw-compress-c-arg-lst-aux-aux-correct))
           :in-theory (e/d (dummy-lemma4)
                           (medw-compress-c-arg-lst-aux-aux-correct)))))

(defret medw-compress-c-arg-lst-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (booleanp c-is-signed)
                (booleanp sign-matters)
                compressed
                (valid-sc c a)
                (valid-sc-subterms c-lst a))
           (and
            (valid-sc-subterms new-c-lst a)
            (implies sign-matters
                     (equal (sum-list-eval new-c-lst a)
                            (sum (if c-is-signed (-- (rp-evlt c a)) (rp-evlt c a))
                                 (sum-list-eval c-lst a))))
            (implies (not sign-matters)
                     (equal (m2 (sum-list-eval new-c-lst a))
                            (m2 (sum (rp-evlt c a)
                                     (sum-list-eval c-lst a)))))))
  :fn medw-compress-c-arg-lst-aux
  :hints (("Goal"
           :do-not-induct t
           :induct (medw-compress-c-arg-lst-aux c c-is-signed c-lst sign-matters)
           :in-theory (e/d* (medw-compress-c-arg-lst-aux
                             (:REWRITE
                              REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_--_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE RP-EVL-OF----WHEN-MULT-FORMULA-CHECKS)
                             rp-evlt-of-ex-from-rp-reverse)
                            (RP-EVL-OF-EX-FROM-RP
                             (:REWRITE VALID-SC-SUBTERMS-CDR)

                             (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                             (:DEFINITION RP-TERM-LISTP)
                             (:TYPE-PRESCRIPTION MEMBER-EQUAL)
                             ex-from-rp
                             rp-equal
                             rp-trans
                             rp-equal-cnt
                             (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                             (:REWRITE MINUS-OF-MINUS)
                             (:REWRITE IFIX-OPENER)
                             (:REWRITE LIGHT-PP-TERM-P-INTEGERP)
                             (:DEFINITION VALID-SC)
                             (:DEFINITION INCLUDE-FNC)
                             (:REWRITE CAR-OF-EX-FROM-RP-IS-NOT-RP)
                             (:DEFINITION RP-TERMP)
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                             (:REWRITE VALID-SC-EX-FROM-RP)
                             (:REWRITE MINUS-OF-SUM)
                             (:REWRITE EX-FROM-SYNP-LEMMA1)
                             (:DEFINITION IS-SYNP$INLINE)
                             (:REWRITE
                              CREATE-LIST-INSTANCE-EQUALS-NIL-IMPLIES)
                             (:REWRITE DEFAULT-CAR)
                             RP-EVLT-OF-EX-FROM-RP)))))

(defret medw-compress-c-arg-lst-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (booleanp sign-matters)

                (force (valid-sc-subterms c-lst a)))
           (and (implies sign-matters
                         (equal (sum-list-eval res-c-lst a)
                                (sum-list-eval c-lst a)))
                (implies (not sign-matters)
                         (equal (m2 (sum-list-eval res-c-lst a))
                                (m2 (sum-list-eval c-lst a))))
                (valid-sc-subterms res-c-lst a)))
  :fn  medw-compress-c-arg-lst
  :hints (("Goal"
           :do-not-induct t
           :induct ( medw-compress-c-arg-lst c-lst sign-matters limit)
           :in-theory (e/d ( medw-compress-c-arg-lst
                             (:REWRITE
                              REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_--_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE RP-EVL-OF----WHEN-MULT-FORMULA-CHECKS)
                             rp-evlt-of-ex-from-rp-reverse)
                           (RP-EVL-OF-EX-FROM-RP
                            (:REWRITE VALID-SC-SUBTERMS-CDR)

                            (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                            (:DEFINITION RP-TERM-LISTP)
                            (:TYPE-PRESCRIPTION MEMBER-EQUAL)
                            ex-from-rp
                            rp-equal
                            rp-trans
                            rp-equal-cnt
                            (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                            (:REWRITE MINUS-OF-MINUS)
                            (:REWRITE IFIX-OPENER)
                            (:REWRITE LIGHT-PP-TERM-P-INTEGERP)
                            (:DEFINITION VALID-SC)
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE CAR-OF-EX-FROM-RP-IS-NOT-RP)
                            (:DEFINITION RP-TERMP)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE VALID-SC-EX-FROM-RP)
                            (:REWRITE MINUS-OF-SUM)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:DEFINITION IS-SYNP$INLINE)
                            (:REWRITE
                             CREATE-LIST-INSTANCE-EQUALS-NIL-IMPLIES)
                            (:REWRITE DEFAULT-CAR)
                            RP-EVLT-OF-EX-FROM-RP)
                           ))))

;;;;;

(defret medw-compress-pp-arg-lst-aux-valid-sc
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (booleanp sign-matters)
                (booleanp c-is-signed)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-pp-arg-lst a))
           (and
            (valid-sc-subterms res-pp-lst a)
            (valid-sc-subterms res-c-pp-arg-lst a)))
  :fn  medw-compress-pp-arg-lst-aux
  :hints (("Goal"
           :do-not-induct t
           :induct ( medw-compress-pp-arg-lst-aux pp-lst c-pp-arg-lst
                                                  c-is-signed sign-matters)
           :in-theory (e/d ( medw-compress-pp-arg-lst-aux
                             (:REWRITE
                              REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_--_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE RP-EVL-OF----WHEN-MULT-FORMULA-CHECKS)
                             rp-evlt-of-ex-from-rp-reverse)
                           (RP-EVL-OF-EX-FROM-RP
                            (:REWRITE VALID-SC-SUBTERMS-CDR)

                            (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                            (:DEFINITION RP-TERM-LISTP)
                            (:TYPE-PRESCRIPTION MEMBER-EQUAL)
                            ex-from-rp
                            rp-equal
                            rp-trans
                            rp-equal-cnt
                            (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                            (:REWRITE MINUS-OF-MINUS)
                            (:REWRITE IFIX-OPENER)
                            (:REWRITE LIGHT-PP-TERM-P-INTEGERP)
                            (:DEFINITION VALID-SC)
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE CAR-OF-EX-FROM-RP-IS-NOT-RP)
                            (:DEFINITION RP-TERMP)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE VALID-SC-EX-FROM-RP)
                            (:REWRITE MINUS-OF-SUM)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:DEFINITION IS-SYNP$INLINE)
                            (:REWRITE
                             CREATE-LIST-INSTANCE-EQUALS-NIL-IMPLIES)
                            (:REWRITE DEFAULT-CAR)
                            RP-EVLT-OF-EX-FROM-RP)
                           ))))

(local
 (encapsulate
   nil

   (local
    (use-arith-5 t))

   (defthm m2-of-dummy
     (equal (equal (m2 (sum x a y))
                   (m2 (sum a b c)))
            (equal (m2 (sum x y))
                   (m2 (sum b c))))
     :otf-flg t
     :hints (("Goal"
              )))

   (defthm f2-of-negated-1
     (equal (f2 (sum b (-- a)))
            (sum (-- a) (f2 (sum a b)))))

   (defthm f2-of-repeated-dummy-1
     (equal (f2 (sum x y z a a))
            (sum a (f2 (sum x y z )))))

   (defthm m2-of-teh-same-dummy-2
     (equal (equal (m2 (sum x a))
                   (m2 (sum k l m a)))
            (equal (m2 (sum x))
                   (m2 (sum k l m)))))

   (defthm m2-of-negated-dummy-2
     (equal (m2 (sum k l m (-- a)))
            (m2 (sum k l m a))))

   (defthmd m2-equivalence-move-args
     (equal (equal (m2 (sum a b))
                   (m2 x))
            (equal (m2 a)
                   (m2 (sum b x))))
     :hints (("Goal"
              :in-theory (e/d (m2 sum f2)
                              (+-IS-SUM mod2-is-m2 floor2-if-f2)))))

   (defthmd m2-dummy-lemma2
     (equal (equal (m2 (sum a b (f2 c)))
                   (m2 x))
            (equal (m2 (sum a b))
                   (m2 (sum (f2 c) x))))
     :hints (("Goal"
              :use ((:instance m2-equivalence-move-args
                               (a (sum a b))
                               (b (f2 c))
                               (x x)))
              :in-theory (e/d ()
                              ()))))

   (defthmd equal-of-m2-to-the-same-side
     (equal (equal (m2 x) (m2 y))
            (equal (m2 (sum x y)) 0))
     :hints (("Goal"
              :in-theory (e/d (m2 f2 sum)
                              (M2-SUMS-EQUIVALENCE
                               mod2-is-m2
                               floor2-if-f2
                               +-IS-SUM)))))

   (defthm d2-of-repeated
     (and (equal (d2 (sum a a b))
                 (sum a (d2 b)))
          (equal (d2 (sum a a))
                 (sum a))
          (equal (d2 (sum x y z a a b))
                 (sum a (d2 (sum x y z b))))
          (equal (d2 (sum x y z a a))
                 (sum a (d2 (sum x y z)))))
     :hints (("Goal"
              :in-theory (e/d (d2 f2 sum m2)
                              (floor2-if-f2
                               mod2-is-m2
                               +-IS-SUM)))))

   (defthm d2-of-repeated-2
     (and (equal (d2 (sum x y a a b))
                 (sum a (d2 (sum x y b)))
                 ))
     :hints (("Goal"
              :in-theory (e/d (d2 f2 sum m2)
                              (floor2-if-f2
                               mod2-is-m2
                               +-IS-SUM)))))

   (defthm d2-of-negated
     (and (equal (d2 (sum x (-- a) y))
                 (sum (-- a) (d2 (sum a x y))))))

   (defthm evenp-and-m2
     (and (implies (evenp (ifix a))
                   (equal (m2 (sum a x))
                          (m2 x)))
          (implies (not (evenp (ifix a)))
                   (equal (m2 (sum a x))
                          (sum 1 (-- (m2 x))))))
     :hints (("Goal"
              :in-theory (e/d (sum m2 f2)
                              (+-IS-SUM
                               floor2-if-f2
                               mod2-is-m2)))))

   (defthm dummy-m2-of-repeated
     (equal (m2 (sum x y a a))
            (m2 (sum x y))))

   (defthm dummy-m2-of-repeated-2
     (equal (m2 (sum x a a y))
            (m2 (sum x y))))

   ))

(local
 (encapsulate
   nil

   (local
    (defthm dummy-d-2-of-repeated-2
      (and (equal (d2 (sum x y a a))
                  (sum a (d2 (sum x y)))))))

   (local
    (defthm dummy-m2-of-repeated-3
      (and (equal (m2 (sum x y z a a k))
                  (m2 (sum x y z k))))))

   (defthm m2-of-f2-of-the-same
     (implies (equal (m2 c) (m2 d))
              (equal (equal (m2 (sum a (f2 (sum c x))))
                            (m2 (sum b (f2 (sum d x)))))
                     (equal (m2 (sum a (f2 c)))
                            (m2 (sum b (f2 d))))))
     ;;:otf-flg t
     :hints (("Goal"
              :in-theory (e/d (
                               equal-of-m2-to-the-same-side
                               floor mod
                               rw-dir2)
                              (+-IS-SUM
                               rw-dir1
                               ;;(:REWRITE ACL2::|(mod x 2)| . 1)
                               floor2-if-f2
                               mod2-is-m2)))))

   (defthm m2-of-f2-of-the-same-2
     (implies (equal (m2 c) (m2 d))
              (equal (equal (m2 (sum a (f2 (sum c x))))
                            (m2 (sum b b1 (f2 (sum d x)))))
                     (equal (m2 (sum a (f2 c)))
                            (m2 (sum b b1 (f2 d))))))
     :otf-flg t
     :hints (("Goal"
              :use ((:instance m2-of-f2-of-the-same
                               (b (sum b b1))))
              :in-theory (e/d ()
                              (m2-of-f2-of-the-same)))))

   (defthm m2-of-f2-of-the-same-3
     (implies (equal (m2 c) (m2 d))
              (equal (equal (m2 (sum a a1 (f2 (sum c x1 x2))))
                            (m2 (sum b b1 (f2 (sum x1 d x2)))))
                     (equal (m2 (sum a a1 (f2 c)))
                            (m2 (sum b b1 (f2 d))))))
     :otf-flg t
     :hints (("Goal"
              :use ((:instance m2-of-f2-of-the-same
                               (b (sum b b1))
                               (x (sum x1 x2))
                               (a (sum a a1))))
              :in-theory (e/d ()
                              (m2-of-f2-of-the-same)))))))

;;:i-am-here

(defret medw-compress-pp-arg-lst-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (booleanp sign-matters)
                (booleanp c-is-signed))
           (and
            (implies (not compressed)
                     (and (equal res-c-pp-arg-lst c-pp-arg-lst)
                          (equal res-pp-lst pp-lst)))
            (implies (and sign-matters
                          compressed)
                     (equal (sum-list-eval res-c-pp-arg-lst a)
                            (if c-is-signed
                                (sum (sum-list-eval res-pp-lst a)
                                     (sum-list-eval res-pp-lst a)
                                     (-- (sum-list-eval pp-lst a))
                                     (-- (sum-list-eval pp-lst a))
                                     (sum-list-eval c-pp-arg-lst a))
                              (sum
                               (-- (sum-list-eval res-pp-lst a))
                               (-- (sum-list-eval res-pp-lst a))
                               (sum-list-eval pp-lst a)
                               (sum-list-eval pp-lst a)
                               (sum-list-eval c-pp-arg-lst a))))
                     )
            (equal (m2 (sum-list-eval res-c-pp-arg-lst a))
                   (m2 (sum-list-eval c-pp-arg-lst a)))
            (implies (and (not sign-matters)
                          compressed)
                     (and (equal (m2 (sum (sum-list-eval res-pp-lst a)
                                          (f2 (sum-list-eval res-c-pp-arg-lst a))))
                                 (m2 (sum (sum-list-eval pp-lst a)
                                          (f2 (sum-list-eval c-pp-arg-lst a)))))
                          (equal (m2 (sum (sum-list-eval res-pp-lst a)
                                          (f2 (sum (sum-list-eval res-c-pp-arg-lst a) other))))
                                 (m2 (sum (sum-list-eval pp-lst a)
                                          (f2 (sum (sum-list-eval c-pp-arg-lst a) other)))))))

            ))
  :fn  medw-compress-pp-arg-lst-aux
  :hints (("Goal"
           :do-not-induct t
           :induct ( medw-compress-pp-arg-lst-aux pp-lst c-pp-arg-lst
                                                  c-is-signed sign-matters)
           :in-theory (e/d ( medw-compress-pp-arg-lst-aux

                             (:REWRITE
                              REGULAR-RP-EVL-OF_--_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE RP-EVL-OF----WHEN-MULT-FORMULA-CHECKS)
                             rp-evlt-of-ex-from-rp-reverse
                             pp-order-equals-implies)
                           (RP-EVL-OF-EX-FROM-RP
                            (:REWRITE RP-EVL-OF-VARIABLE)
                            (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                            (:REWRITE RP-EVL-OF-ZP-CALL)
                            (:REWRITE SUM-OF-NEGATED-TERMS)
                            (:TYPE-PRESCRIPTION --)
                            (:TYPE-PRESCRIPTION MULT-FORMULA-CHECKS)
                            ;;(:DEFINITION RP-TRANS-LST)
                            (:REWRITE DUMMY-SUM-CANCEL-LEMMA1)
                            (:REWRITE VALID-SC-SUBTERMS-CDR)
                            (:REWRITE
                             RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC)
                            (:REWRITE WHEN-EX-FROM-RP-IS-1)
                            (:DEFINITION INCLUDE-FNC-SUBTERMS)
                            (:REWRITE VALID-SC-SUBTERMS-CONS)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC-LST)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                            (:TYPE-PRESCRIPTION VALID-SC-SUBTERMS)
                            (:TYPE-PRESCRIPTION VALID-SC)
                            (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                            (:DEFINITION RP-TERM-LISTP)
                            (:TYPE-PRESCRIPTION MEMBER-EQUAL)
                            ex-from-rp
                            rp-equal
                            rp-trans
                            rp-equal-cnt
                            (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                            (:REWRITE MINUS-OF-MINUS)
                            (:REWRITE IFIX-OPENER)
                            (:REWRITE LIGHT-PP-TERM-P-INTEGERP)
                            (:DEFINITION VALID-SC)
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE CAR-OF-EX-FROM-RP-IS-NOT-RP)
                            (:DEFINITION RP-TERMP)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE VALID-SC-EX-FROM-RP)
                            (:REWRITE MINUS-OF-SUM)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:DEFINITION IS-SYNP$INLINE)
                            (:REWRITE
                             CREATE-LIST-INSTANCE-EQUALS-NIL-IMPLIES)
                            (:REWRITE DEFAULT-CAR)
                            RP-EVLT-OF-EX-FROM-RP)
                           ))))

(defret medw-compress-pp-arg-lst-aux-correct-3
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (booleanp sign-matters)
                (booleanp c-is-signed))
           (implies (and (not sign-matters)
                         compressed)
                    (and (equal (m2 (f2 (sum (sum-list-eval res-c-pp-arg-lst a)
                                             other)))
                                (m2 (sum (sum-list-eval pp-lst a)
                                         (sum-list-eval res-pp-lst a)
                                         (f2 (sum (sum-list-eval c-pp-arg-lst a) other)))))
                         (equal (m2 (sum b c (f2 (sum (sum-list-eval
                                                       res-c-pp-arg-lst a)
                                                      other))
                                         d))
                                (m2 (sum b c d (sum-list-eval pp-lst a)
                                         (sum-list-eval res-pp-lst a)
                                         (f2 (sum (sum-list-eval c-pp-arg-lst
                                                                 a)
                                                  other))))))
                    ))
  :fn  medw-compress-pp-arg-lst-aux
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance medw-compress-pp-arg-lst-aux-correct))
           :in-theory (e/d (equal-of-m2-to-the-same-side)
                           (medw-compress-pp-arg-lst-aux-correct
                            sum-of-f2s)))))

(local
 (defthm m2-dummy-lemma3
   (implies (equal (m2 (sum k l m n)) 0)
            (equal (m2 (sum k l m n a )) (m2 a)))))

;; (local
;;  (defthmd medw-compress-pp-arg-lst-correct-dummy-lemma0
;;    (equal (equal (m2 (sum (f2 (sum a y))
;;                           (f2 (sum x a))))
;;                  (m2 (sum (f2 y)
;;                           (f2 x))))
;;           t)
;;    :hints (("Goal"
;;             :cases ((evenp (ifix a)))
;;             :in-theory (e/d (equal-of-m2-to-the-same-side)
;;                             (evenp))))))

;; (local
;;  (defthmd medw-compress-pp-arg-lst-correct-dummy-lemma1
;;    (equal (equal (m2 (sum (f2 (sum a y b))
;;                           (f2 (sum x a b))))
;;                  (m2 (sum (f2 y)
;;                           (f2 x))))
;;           t)
;;    :hints (("Goal"
;;             :cases ((evenp (sum a b)))
;;             :in-theory (e/d (equal-of-m2-to-the-same-side)
;;                             (evenp))))))

(defret medw-compress-pp-arg-lst-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (booleanp sign-matters)
                )
           (and
            (implies (not compressed)
                     (and (equal res-pp-lst pp-lst)
                          (equal res-c-lst c-lst)))
            (implies (and sign-matters
                          (force (valid-sc-subterms pp-lst a))
                          (force (valid-sc-subterms c-lst a))
                          (case-split compressed))
                     (equal (sum-list-eval res-c-lst a)
                            (sum (-- (sum-list-eval res-pp-lst a))
                                 (sum-list-eval pp-lst a)
                                 (sum-list-eval c-lst a)))
                     )

            (implies (and (not sign-matters)
                          (force (valid-sc-subterms pp-lst a))
                          (force (valid-sc-subterms c-lst a))
                          (case-split compressed))
                     (equal (m2 (sum (sum-list-eval res-pp-lst a)
                                     (sum-list-eval res-c-lst  a)))
                            (m2 (sum
                                 (sum-list-eval pp-lst a)
                                 (sum-list-eval c-lst a))))
                     )
            (implies (and (force (valid-sc-subterms pp-lst a))
                          (force (valid-sc-subterms c-lst a)))
                     (and (valid-sc-subterms res-pp-lst a)
                          (valid-sc-subterms res-c-lst a))))
           #|(implies (and (not sign-matters)
           compressed) ;
           (equal (m2 (sum (sum-list-eval res-pp-lst a) ;
           (f2 (sum-list-eval res-c-pp-arg-lst a)))) ;
           (m2 (sum (sum-list-eval pp-lst a) ;
           (f2 (sum-list-eval c-pp-arg-lst a))))))||#

           )
  :fn  medw-compress-pp-arg-lst
  :hints (("Goal"
           :do-not-induct t
           :induct (medw-compress-pp-arg-lst pp-lst c-lst
                                             sign-matters)
           :in-theory (e/d ( medw-compress-pp-arg-lst
                             ;;equal-of-m2-to-the-same-side
                             m2-dummy-lemma2
                             (:REWRITE
                              REGULAR-RP-EVL-OF_c_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_--_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE RP-EVL-OF----WHEN-MULT-FORMULA-CHECKS)
                             rp-evlt-of-ex-from-rp-reverse
                             pp-order-equals-implies)
                           (RP-EVL-OF-EX-FROM-RP

                            (:REWRITE RP-EVL-OF-VARIABLE)
                            (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                            (:REWRITE RP-EVL-OF-ZP-CALL)
                            (:REWRITE SUM-OF-NEGATED-TERMS)
                            (:TYPE-PRESCRIPTION --)
                            (:TYPE-PRESCRIPTION MULT-FORMULA-CHECKS)
                            ;;(:DEFINITION RP-TRANS-LST)
                            (:REWRITE DUMMY-SUM-CANCEL-LEMMA1)
                            (:REWRITE VALID-SC-SUBTERMS-CDR)
                            (:REWRITE
                             RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC)
                            (:REWRITE WHEN-EX-FROM-RP-IS-1)
                            (:DEFINITION INCLUDE-FNC-SUBTERMS)
                            (:REWRITE VALID-SC-SUBTERMS-CONS)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC-LST)

                            (:TYPE-PRESCRIPTION VALID-SC-SUBTERMS)
                            (:TYPE-PRESCRIPTION VALID-SC)
                            (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                            (:DEFINITION RP-TERM-LISTP)
                            (:TYPE-PRESCRIPTION MEMBER-EQUAL)
                            ex-from-rp
                            rp-equal
                            rp-trans
                            rp-equal-cnt
                            (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                            (:REWRITE MINUS-OF-MINUS)
                            (:REWRITE IFIX-OPENER)
                            (:REWRITE LIGHT-PP-TERM-P-INTEGERP)
                            (:DEFINITION VALID-SC)
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE CAR-OF-EX-FROM-RP-IS-NOT-RP)
                            (:DEFINITION RP-TERMP)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE VALID-SC-EX-FROM-RP)
                            (:REWRITE MINUS-OF-SUM)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:DEFINITION IS-SYNP$INLINE)
                            (:REWRITE
                             CREATE-LIST-INSTANCE-EQUALS-NIL-IMPLIES)
                            (:REWRITE DEFAULT-CAR)
                            RP-EVLT-OF-EX-FROM-RP
                            SUM-OF-F2S
                            )

                           ))))

(defret-mutual
  medw-compress-c-correct
  (defret medw-compress-c-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc c a))
             (and

              (implies compressed
                       (equal (sum-list-eval res-c-lst a)
                              (ifix (rp-evlt c a))))
              (valid-sc-subterms res-c-lst a)))
    :fn medw-compress-c)
  (defret medw-compress-c-lst-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  )
             (and (implies (not compressed)
                           (equal res-c-lst
                                  c-lst))
                  (implies (and (case-split compressed)
                                (valid-sc-subterms c-lst a))
                           (equal (sum-list-eval res-c-lst a)
                                  (sum-list-eval c-lst a)))
                  (implies (valid-sc-subterms c-lst a)
                           (valid-sc-subterms res-c-lst a))))
    :fn medw-compress-c-lst)
  :mutual-recursion medw-compress-c
  :hints (("Goal"
           :do-not-induct t
           :expand ((MEDW-COMPRESS-C C LIMIT))
           :in-theory (e/d* (medw-compress-c-lst
                             medw-compress-c
                             ;;regular-eval-lemmas-with-ex-from-rp
                             ;;regular-eval-lemmas
                             (:REWRITE REGULAR-RP-EVL-OF_--_WHEN_MULT-FORMULA-CHECKS)
                             (:REWRITE REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             rp-evlt-of-ex-from-rp-reverse
                             pp-order-equals-implies)
                            (RP-EVLT-OF-EX-FROM-RP
                             EX-FROM-RP
                             (:DEFINITION INCLUDE-FNC)
                             valid-sc
                             (:DEFINITION EVAL-AND-ALL)
                             (:REWRITE NOT-INCLUDE-RP)
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                             (:REWRITE WHEN-EX-FROM-RP-IS-1)
                             (:REWRITE DEFAULT-CAR)
                             (:REWRITE VALID-SC-SUBTERMS-CONS)
                             (:REWRITE --OF-SUM)
                             (:REWRITE --OF---)
                             (:DEFINITION RP-TRANS)

                             ;;(:REWRITE VALID-SC-SUBTERMS-CDR)
                             )))))

(defret medw-compress-s-is-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc s a)
                (rp-termp s))
           (and (equal (rp-evlt res-term a)
                       (rp-evlt s a))
                (valid-sc res-term a)))
  :fn medw-compress-s
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (medw-compress-s
                             regular-eval-lemmas-with-ex-from-rp
                             regular-eval-lemmas

                             rp-evlt-of-ex-from-rp-reverse-atom
                             pp-order-equals-implies)
                            (RP-EVLT-OF-EX-FROM-RP
                             EX-FROM-RP
                             (:DEFINITION INCLUDE-FNC)
                             valid-sc
                             (:DEFINITION EVAL-AND-ALL)
                             (:REWRITE NOT-INCLUDE-RP)
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                             (:REWRITE WHEN-EX-FROM-RP-IS-1)
                             (:REWRITE DEFAULT-CAR)
                             (:REWRITE VALID-SC-SUBTERMS-CONS)
                             (:REWRITE --OF-SUM)
                             (:REWRITE --OF---)
                             (:DEFINITION RP-TRANS)

                             ;;(:REWRITE VALID-SC-SUBTERMS-CDR)
                             )))))

(defret medw-compress-s-c-res-is-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc s-c-res a)
                (rp-termp s-c-res))
           (and (equal (rp-evlt res-term a)
                       (rp-evlt s-c-res a))
                (valid-sc res-term a)))
  :fn medw-compress-s-c-res
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (medw-compress-s-c-res
                             regular-eval-lemmas-with-ex-from-rp
                             regular-eval-lemmas
                             S-C-RES
                             rp-evlt-of-ex-from-rp-reverse-atom
                             pp-order-equals-implies)
                            (RP-EVLT-OF-EX-FROM-RP
                             EX-FROM-RP
                             (:DEFINITION INCLUDE-FNC)
                             valid-sc
                             (:DEFINITION EVAL-AND-ALL)
                             (:REWRITE NOT-INCLUDE-RP)
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                             (:REWRITE WHEN-EX-FROM-RP-IS-1)
                             (:REWRITE DEFAULT-CAR)
                             (:REWRITE VALID-SC-SUBTERMS-CONS)
                             (:REWRITE --OF-SUM)
                             (:REWRITE --OF---)
                             (:DEFINITION RP-TRANS)

                             ;;(:REWRITE VALID-SC-SUBTERMS-CDR)
                             )))))

;;:i-am-here

(defthmd RP-EVLt-OF-FNCALL-ARGS
  (implies (and (Not (equal fn 'quote))
                (Not (equal fn 'list))
                (Not (equal fn 'falist)))
           (equal (rp-evlt (cons fn args) a)
                  (RP-EVL (CONS FN (KWOTE-LST (RP-EVLT-LST ARGS A)))
                          NIL)))
  :hints (("Goal"
           :expand ((:free (args)
                           (rp-trans (cons fn args))))
           :in-theory (e/d (RP-EVL-OF-FNCALL-ARGS
                            rp-trans)
                           ()))))

(defthmd RP-EVLt-OF-FNCALL-ARGS2
  (implies (and (NOT (EQUAL (CAR term) 'S))
                (NOT (EQUAL (CAR term)
                            'S-C-RES))
                (NOT (EQUAL (CAR term) 'C))
                (NOT (EQUAL (CAR term) 'QUOTE))
                (NOT (EQUAL (CAR term) 'FALIST))
                (NOT (EQUAL (CAR term) 'LIST))
                (NOT (EQUAL (CAR term) 'IF))
                (consp term))
           (equal (rp-evlt term a)
                  (RP-EVL (CONS (car term)
                                (KWOTE-LST (RP-EVLT-LST (cdr term) A)))
                          NIL)))
  :hints (("Goal"
           :expand ((:free (args)
                           (rp-trans (cons fn args))))
           :in-theory (e/d (RP-EVL-OF-FNCALL-ARGS
                            rp-trans)
                           ()))))

(defthmd RP-EVL-OF-FNCALL-ARGS2
  (implies (and (Not (equal fn 'quote))
                )
           (equal (rp-evl (cons fn args) a)
                  (RP-EVL (CONS FN (KWOTE-LST (RP-EVL-LST ARGS A)))
                          NIL)))
  :hints (("Goal"
           :expand ((:free (args)
                           (rp-trans (cons fn args))))
           :in-theory (e/d (RP-EVL-OF-FNCALL-ARGS
                            rp-trans)
                           ()))))

(defthmd valid-sc-of-ex-from-rp-reverse
  (implies (syntaxp (atom term))
           (equal (valid-sc term a)
                  (and (EVAL-AND-ALL (CONTEXT-FROM-RP TERM NIL)
                                     A)
                       (valid-sc (ex-from-rp term) a))))
  :hints (("Goal"
           :expand ((VALID-SC TERM A)
                    (CONTEXT-FROM-RP TERM NIL))
           :do-not-induct t
           :in-theory (e/d (valid-sc
                            is-if
                            is-rp)
                           (;;EVAL-AND-ALL
                            ;;context-from-rp
                            )))))


(DEFTHMd
  RP-EVLT-OF-EX-FROM-RP-with-syntaxp
  (IMPLIES (SYNTAXP (consp term))
           (EQUAL (RP-EVL (RP-TRANS (EX-FROM-RP TERM))
                          A)
                  (RP-EVL (RP-TRANS TERM) A)
                  )))

(DEFTHMd
  RP-EVLT-OF-EX-FROM-RP-REVERSE-2
  (IMPLIES (SYNTAXP (atom term))
           (EQUAL (RP-EVL (RP-TRANS TERM) A)
                  (RP-EVL (RP-TRANS (EX-FROM-RP TERM))
                          A))))

(defthm is-rp-dummy-lemma
  (implies (rp-termp term)
           (not (is-rp (cons (car (ex-from-rp term)) rest))))
  :hints (("Goal"
           :induct (ex-from-rp term)
           :do-not-induct t
           :in-theory (e/d (is-rp
                            ex-from-rp)
                           ()))))

(defthm open-valid-sc-when-is-if
  (implies (is-if term)
           (equal (valid-sc term a)
                  (and 
                       (VALID-SC (CADR TERM) A)
                       (IF (RP-EVLT (CADR TERM) A)
                           (VALID-SC (CADDR TERM) A)
                           (VALID-SC (CADDDR TERM) A)))))
  :hints (("Goal"
           :expand (valid-sc term a)
           :in-theory (e/d () (valid-sc)))))

(defthm open-valid-sc-when-is-if-2
  (implies (is-if (EX-FROM-RP TERM))
           (equal (valid-sc term a)
                  (and (EVAL-AND-ALL (CONTEXT-FROM-RP TERM NIL)
                                     A)
                       (VALID-SC (CADR (EX-FROM-RP TERM)) A)
                       (IF (RP-EVLT (CADR (EX-FROM-RP TERM)) A)
                           (VALID-SC (CADDR (EX-FROM-RP TERM)) A)
                           (VALID-SC (CADDDR (EX-FROM-RP TERM)) A)))))
  :hints (("Goal"
           :expand (valid-sc (ex-from-rp term) a)
           :in-theory (e/d (valid-sc-of-ex-from-rp-reverse) (valid-sc))
           )))

(create-regular-eval-lemma if 3 MULT-FORMULA-CHECKS)

(defthm is-if-lemma
  (is-if `(if ,x ,y ,z))
  :hints (("Goal"
           :in-theory (e/d (is-if) ()))))

(defthm rp-evlt-when-list
  (implies (and (consp term)
                (equal (car term) 'list))
           (equal (rp-evlt term a)
                  (RP-EVLT-LST (CDR term) A))))


(defthm valid-sc-single-step-lemma
  (implies (and (rp-termp term)
                (equal (car term) 'rp)
                (valid-sc term a))
           (valid-sc (caddr term) a))
  :hints (("Goal"
           :in-theory (e/d (valid-sc-single-step) ()))))

(defret-mutual
  medw-compress-any-correct
  (defret medw-compress-any-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (rp-termp term)
                  (valid-sc term a))
             (and (equal (rp-evlt res a)
                         (rp-evlt term a))
                  (valid-sc res a)))
    :fn medw-compress-any)
  (defret medw-compress-any-lst-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc-subterms lst a)
                  (rp-term-listp lst)
                  )
             (and (equal (rp-evlt-lst res-lst a)
                         (rp-evlt-lst lst a))
                  (valid-sc-subterms res-lst a)
                  ))
    :fn medw-compress-any-lst)
  :mutual-recursion medw-compress-any
  :hints (("Goal"
           :do-not-induct t
           :expand (;;(rp-trans (ex-from-rp term))
                    ;;(VALID-SC (EX-FROM-RP TERM) A)
                    (:free (x y) (valid-sc (cons x y) a))
                    
                    )
           :in-theory (e/d* (medw-compress-any
                             ;;valid-sc-of-ex-from-rp-reverse
                             medw-compress-any-lst
                             regular-eval-lemmas
                             ;;RP-EVLT-OF-EX-FROM-RP-with-syntaxp
                             RP-EVLt-OF-FNCALL-ARGS
                             ;;RP-EVL-OF-FNCALL-ARGS
                             ;;RP-EVL-OF-FNCALL-ARGS2
                             RP-EVLt-OF-FNCALL-ARGS2
                             ;;RP-EVLT-OF-EX-FROM-RP-REVERSE-2
                             ;;is-if is-rp
                             valid-sc-subterms
                             valid-sc-single-step
                             regular-eval-lemmas-with-ex-from-rp)
                            ((:DEFINITION EX-FROM-RP)
                             valid-sc
                             VALID-SC-EX-FROM-RP-2
                             ;;VALID-SC-EX-FROM-RP-2
                             ;;valid-sc-subterms
                             (:REWRITE IS-IF-RP-TERMP)
                             ;;rp-evlt-of-ex-from-rp
                             rp-termp
                             rp-term-listp
                             cons-equal
                             (:REWRITE NOT-INCLUDE-RP)
                             (:DEFINITION INCLUDE-FNC)
                             (:REWRITE DEFAULT-CDR)
                             (:DEFINITION INCLUDE-FNC-SUBTERMS)
                             (:REWRITE RP-EVL-OF-RP-EQUAL2)
                             rp-trans-is-term-when-list-is-absent
                             rp-trans
                             RP-TRANS-LST
                             RP-TRANS-OPENER
                             )))))

;;(create-regular-eval-lemma medw-compress 1 MULT-FORMULA-CHECKS)

(defret medw-compress-meta-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp term)
                (valid-sc term a))
           (and (valid-sc res a)
                (equal (rp-evlt res a)
                       (rp-evlt term a))
                (dont-rw-syntaxp dont-rw)))
  :fn medw-compress-meta
  :hints (("Goal"
           :expand ((:free (x)
                           (valid-sc (cons 'equal x) a)))
           :in-theory (e/d (medw-compress-meta
                            
                            )
                           (valid-sc
                            rp-termp
                            rp-trans)))))
