
; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2020 Regents of the University of Texas
; All rights reserved.
; Copyright (C) 2022 Intel Corporation

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

(include-book "unpack-booth")
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
 (fetch-new-events
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
(create-regular-eval-lemma unpack-booth 1 mult-formula-checks)

(local
 (set-induction-depth-limit 1))

(local
 (in-theory (disable (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                     (:DEFINITION ACL2::APPLY$-BADGEP)
                     (:DEFINITION SUBSETP-EQUAL)
                     (:DEFINITION MEMBER-EQUAL)
                     (:REWRITE DEFAULT-CDR)
                     ;;                     (:REWRITE ACL2::SUBSETP-REFLEXIVE-LEMMA)
                     (:REWRITE
                      ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1))))

(defret unpack-booth-for-pp-lst-correct
  (implies (and
            (rp-evl-meta-extract-global-facts :state state)
            (mult-formula-checks state)
            (valid-sc-subterms pp-lst a))
           (and (equal (sum-list-eval res-pp-lst a)
                       (sum-list-eval pp-lst a))
                (valid-sc-subterms res-pp-lst a)))
  :fn unpack-booth-for-pp-lst
  :hints (("Goal"
           :do-not-induct t
           :induct (unpack-booth-for-pp-lst pp-lst)
           :in-theory (e/d (unpack-booth-for-pp-lst) ()))))

#|(defthmd rp-evlt-of-ex-from-rp-reverse
  (implies (syntaxp (or (atom term)
                        (not (include-fnc term 'ex-from-rp))))
           (equal (rp-evlt term a)
                  (rp-evlt (ex-from-rp term) a))))||#

(local
 (defthmd ex-from-rp-when---
   (implies (and (EQUAL (CAR C-TERM) '--)
                 (CONSP C-TERM)
                 (CONSP (CDR C-TERM))
                 (NOT (CDDR C-TERM))
                 (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state))
            (equal (rp-evlt (ex-from-rp c-term) a)
                   (-- (rp-evlt (cadr c-term) a))))

   :hints (("Goal"
            :in-theory (e/d* (regular-eval-lemmas
                              regular-eval-lemmas-with-ex-from-rp)
                             (rp-trans))))))

(defthmd f2-reverse-cough
  (implies (syntaxp (include-fnc term1 'C-FIX-ARG-AUX))
           (equal (sum term1 (f2 term2))
                  (f2 (sum term1 term1 term2))))
  :hints (("Goal"
           :use ((:instance f2-of-times2
                            (a term1)
                            (b term2)))
           :in-theory (e/d (times2) ()))))

(local
 (defthm ex-from-rp-of-binary-fnc
   (implies (binary-fnc-p x)
            (equal (rp-evlt (ex-from-rp x) a)
                   (rp-evlt x a)))))

(local
 (defthm dummy-lemma-1
   (equal (equal (sum (-- x) other)
                 (-- y))
          (equal (sum x (-- other))
                 (ifix y)))
   :hints (("Goal"
            :in-theory (e/d (sum
                             --)
                            (+-is-SUM))))))

(local
 (defthmd
   rp-evlt-of-ex-from-rp-reverse-2
   (implies (syntaxp (or (atom term)
                         (and (not (include-fnc term 'ex-from-rp))
                              (not (binary-fnc-p term)))))
            (equal (rp-evl (rp-trans term) a)
                   (rp-evl (rp-trans (ex-from-rp term))
                           a)))))

(defthm c-fix-arg-aux-correct-one-side
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (b* (((mv coughed result)
                 (c-fix-arg-aux pp-lst neg-flag)))
             (equal
              (sum-list-eval result a)
              (sum (sum-list-eval pp-lst a)
                   (-- (sum-list-eval coughed a))
                   (-- (sum-list-eval coughed a))))))
  :hints (("Goal"
           :use ((:instance c-fix-arg-aux-correct))
           :in-theory (e/d () (c-fix-arg-aux-correct)))))

(defret create-c-instance-is-correct-one-side
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms s-lst a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a))
           (and (equal (sum-list-eval res-c-lst a)
                       (sum (-- (sum-list-eval res-s-lst a))
                            (-- (sum-list-eval res-pp-lst a))
                            (f2 (sum (sum-list-eval s-lst a)
                                     (sum-list-eval pp-lst a)
                                     (sum-list-eval c-lst a)))))))
  :fn create-c-instance)

(local
 (defthm f2-of-repeated
   (equal (f2 (sum a a b))
          (sum a (f2 b)))
   :hints (("Goal"
            :use ((:instance
                   f2-of-times2-reverse (term a)
                   (term2 b)))
            :in-theory (e/d (times2)
                            (F2-OF-TIMES2
                             f2-of-times2-reverse))))))

(local
 (defthm --of-ifix
   (equal (-- (ifix x))
          (-- x))
   :hints (("Goal"
            :in-theory (e/d (--) ())))))

(progn
  (define sum-chain-smart-fn-aux (cl x)
    (if (atom cl)
        (mv nil nil)
      (b* ((cur (car cl)))
        (case-match cur
          (('not ('equal a ('binary-sum y z)))
           (if (equal a x)
               (mv y z)
             (sum-chain-smart-fn-aux (cdr cl) x)))
          (&
           (sum-chain-smart-fn-aux (cdr cl) x))))))

  (define sum-chain-smart-fn (x mfc state)
    :verify-guards nil
    (declare (ignorable state))
    (b* ( ;(ancestors  (mfc-ancestors mfc))
         (rcnst (access acl2::metafunction-context mfc :rcnst))
         (cl (access acl2::rewrite-constant rcnst :current-clause))
         (?top-cl (access acl2::rewrite-constant rcnst :top-clause))
         (cl (beta-search-reduce-subterms cl (expt 2 30)))
         ((mv y z)
          (sum-chain-smart-fn-aux cl x))
         ;;(- (cw "x: ~p0 ~%" x))
         ;;(- (cw "cl : ~p0 ~%" cl))
         ;;(- (hard-error 'nil "" 'nil))
         )
      (if (and y z)
          (progn$
           #|(cw "Success ~%")|#
           `((y . ,y)
             (z . ,z)))
        nil)))

  (defthmd expand-sum-from-the-hyps
    (implies (and (bind-free (sum-chain-smart-fn x mfc state)
                             (y z))
                  (equal x (sum y z)))
             (and (equal (sum x other)
                         (sum y other z))
                  (equal (sum other x)
                         (sum y other z))))))

(defthm valid-sc-of-binary-fnc-p
  (and (equal (valid-sc (cons 'binary-? x) a)
              (valid-sc-subterms x a))
       (equal (valid-sc (cons 'binary-xor x) a)
              (valid-sc-subterms x a))
       (equal (valid-sc (cons 'binary-and x) a)
              (valid-sc-subterms x a))
       (equal (valid-sc (cons 'binary-or x) a)
              (valid-sc-subterms x a))
       (equal (valid-sc (cons 'binary-not x) a)
              (valid-sc-subterms x a)))
  :hints (("Goal"
           :in-theory (e/d (is-rp is-if) ()))))

(local
 (defthm rp-evlt-of-ex-from-rp-of-create-s-c-res-instance
   (equal (rp-evlt (ex-from-rp (create-s-c-res-instance x1 x2 x3 x4)) a)
          (rp-evlt (create-s-c-res-instance x1 x2 x3 x4) a))))

(local
 (defthmd has-bitp-rp-force-insert
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state)
                 (valid-sc term a))
            (equal (has-bitp-rp term)
                   (and (hide (has-bitp-rp term))
                        (bitp (rp-evlt term a)))))
   :hints (("Goal"
            :expand (HIDE (HAS-BITP-RP TERM))
            :in-theory (e/d () ())))))

(defthm s-fix-pp-args-aux-correct-with-m2-chain
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
;(rp-term-listp pp-lst)
                )
           (and (equal (m2-chain (sum-list-eval (s-fix-pp-args-aux pp-lst) a)
                                 other)
                       (m2 (sum (sum-list-eval pp-lst a) other)))
                (equal (m2-chain other (sum-list-eval (s-fix-pp-args-aux pp-lst) a))
                       (m2 (sum (sum-list-eval pp-lst a) other)))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance s-fix-pp-args-aux-correct))
           :in-theory (e/d* (m2-chain)
                            ()))))

(local
 (defthm dummy-sum-cancel-lemma
   (and (equal (sum (-- x) y x)
               (sum y))
        (equal (sum x y (-- x))
               (sum y)))))

(defret-mutual
  unpack-booth-for-s-correct

  (defret unpack-booth-buried-in-pp-correct
    (implies (and
              (rp-evl-meta-extract-global-facts :state state)
              (mult-formula-checks state)
              (valid-sc term a)
              (rp-termp term))
             (and (equal (rp-evlt res-term a)
                         (rp-evlt term a))
                  (valid-sc res-term a)))
    :fn unpack-booth-buried-in-pp)

  (defret unpack-booth-process-pp-arg-correct
    (implies (and
              (rp-evl-meta-extract-global-facts :state state)
              (mult-formula-checks state)
              (valid-sc  pp-arg a)
              (rp-termp pp-arg))
             (and (equal (sum-list-eval s-res-lst a)
                         (sum
                          (-- (sum-list-eval pp-res-lst a))
                          (-- (sum-list-eval c-res-lst a))
                          (sum-list-eval (list-to-lst pp-arg) a)))
                  (valid-sc-subterms c-res-lst a)
                  (valid-sc-subterms pp-res-lst a)
                  (valid-sc-subterms s-res-lst a)))
    :fn unpack-booth-process-pp-arg)

  (defret unpack-booth-buried-in-pp-lst-correct
    (implies (and
              (rp-evl-meta-extract-global-facts :state state)
              (mult-formula-checks state)
              (valid-sc-subterms  lst a)
              (rp-term-listp lst))
             (and (equal (sum-list-eval res-lst a)
                         (sum-list-eval lst a))
                  (valid-sc-subterms res-lst a)))
    :fn unpack-booth-buried-in-pp-lst)

  (defret unpack-booth-for-s-correct
    (implies (and
              (rp-evl-meta-extract-global-facts :state state)
              (mult-formula-checks state)
              (valid-sc  s-term a)
              (rp-termp s-term))
             (and (equal (sum-list-eval s-res-lst a)
                         (sum (rp-evlt s-term a)
                              (-- (sum-list-eval pp-res-lst a))
                              (-- (sum-list-eval c-res-lst a))))
                  (valid-sc-subterms c-res-lst a)
                  (valid-sc-subterms pp-res-lst a)
                  (valid-sc-subterms s-res-lst a)))
    :fn unpack-booth-for-s)

  (defret unpack-booth-for-s-lst-correct
    (implies (and
              (rp-evl-meta-extract-global-facts :state state)
              (mult-formula-checks state)
              (valid-sc-subterms  s-lst a)
              (rp-term-listp s-lst))
             (and (equal (sum-list-eval s-res-lst a)
                         (sum (-- (sum-list-eval pp-res-lst a))
                              (-- (sum-list-eval c-res-lst a))
                              (sum-list-eval s-lst a)))
                  (valid-sc-subterms c-res-lst a)
                  (valid-sc-subterms pp-res-lst a)
                  (valid-sc-subterms s-res-lst a)))
    :fn unpack-booth-for-s-lst)

  (defret unpack-booth-for-c-correct
    (implies (and
              (rp-evl-meta-extract-global-facts :state state)
              (mult-formula-checks state)
              (valid-sc  c-term a)
              (rp-termp c-term))
             (and (equal (sum-list-eval s-res-lst a)
                         (sum (-- (sum-list-eval pp-res-lst a))
                              (-- (sum-list-eval c-res-lst a))
                              (rp-evlt c-term a)))
                  (valid-sc-subterms c-res-lst a)
                  (valid-sc-subterms pp-res-lst a)
                  (valid-sc-subterms s-res-lst a)))
    :fn unpack-booth-for-c)

  (defret unpack-booth-for-c-lst-correct
    (implies (and
              (rp-evl-meta-extract-global-facts :state state)
              (mult-formula-checks state)
              (valid-sc-subterms  c-lst a)
              (rp-term-listp c-lst))
             (and (equal (sum-list-eval s-res-lst a)
                         (sum
                          (-- (sum-list-eval pp-res-lst a))
                          (-- (sum-list-eval c-res-lst a))
                          (sum-list-eval c-lst a)))
                  (valid-sc-subterms c-res-lst a)
                  (valid-sc-subterms pp-res-lst a)
                  (valid-sc-subterms s-res-lst a)))
    :fn unpack-booth-for-c-lst)

  :mutual-recursion unpack-booth-for-s

  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (m2-to-m2-chain
                             expand-sum-from-the-hyps
                             binary-fnc-p
                             has-bitp-rp-force-insert
                             create-s-instance-correct-singled-out
                             unpack-booth-for-c-lst
                             unpack-booth-for-s-lst
                             unpack-booth-for-c
                             unpack-booth-for-s
                             UNPACK-BOOTH-BURIED-IN-PP-LST
                             unpack-booth-process-pp-arg
                             unpack-booth-buried-in-pp
                             rp-evlt-of-ex-from-rp-reverse-2
                             ex-from-rp-when---
                             REGULAR-RP-EVL-OF_binary-?_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP
                             REGULAR-RP-EVL-OF_binary-xor_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP
                             REGULAR-RP-EVL-OF_binary-and_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP
                             REGULAR-RP-EVL-OF_binary-or_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP
                             REGULAR-RP-EVL-OF_binary-not_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP
                             REGULAR-RP-EVL-OF_binary-?_WHEN_MULT-FORMULA-CHECKS
                             REGULAR-RP-EVL-OF_binary-xor_WHEN_MULT-FORMULA-CHECKS
                             REGULAR-RP-EVL-OF_binary-and_WHEN_MULT-FORMULA-CHECKS
                             REGULAR-RP-EVL-OF_binary-or_WHEN_MULT-FORMULA-CHECKS
                             REGULAR-RP-EVL-OF_binary-not_WHEN_MULT-FORMULA-CHECKS
                             ;;f2-reverse-cough
                             (:REWRITE
                              REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_s_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             )
                            (rp-evlt-of-ex-from-rp
                             ex-from-rp
                             rp-termp
                             (:REWRITE DEFAULT-CAR)
                             valid-sc-subterms
                             rp-term-listp
                             bitp
                             (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                             ;;(:REWRITE MINUS-OF-SUM)
                             F2-OF-MINUS-2
                             F2-OF-MINUS
                             valid-sc
                             (:REWRITE RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT)
                             ;;(:REWRITE RP-TRANS-OPENER-WHEN-LIST)
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC-LST)
                             eval-and-all
                             rp-trans)))))

#|(defret unpack-booth-for-c-lst-correct-with-other
    (implies (and
              (rp-evl-meta-extract-global-facts :state state)
              (mult-formula-checks state)
              (valid-sc-subterms  c-lst a)
              (rp-term-listp c-lst))
             (and (equal (sum (sum-list-eval s-res-lst a)
                              (sum-list-eval pp-res-lst a)
                              (sum-list-eval c-res-lst a)
                              other)
                         (sum (sum-list-eval c-lst a)
                              other))
                  ))
    :fn unpack-booth-for-c-lst)

(defret unpack-booth-for-s-lst-correct-with-other
    (implies (and
              (rp-evl-meta-extract-global-facts :state state)
              (mult-formula-checks state)
              (valid-sc-subterms  s-lst a)
              (rp-term-listp s-lst))
             (and (equal (sum (sum-list-eval s-res-lst a)
                              (sum-list-eval pp-res-lst a)
                              (sum-list-eval c-res-lst a)
                              other)
                         (sum (sum-list-eval s-lst a)
                              other)
                  )))
    :fn unpack-booth-for-s-lst)|#

(local
 (defthm single-c-p-implies-integerp
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state)
                 (or (single-c-p (ex-from-rp term))
                     (single-c-p term)))
            (and (integerp (rp-evlt term a))
                 (integerp (rp-evlt (ex-from-rp term) a))))
   :hints (("goal"
            :do-not-induct t
            :in-theory (e/d* (single-c-p
                              regular-rp-evl-of_c_when_mult-formula-checks_with-ex-from-rp)
                             ())))))

(local
 (defthm single-s-p-implies-integerp
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state)
                 (or (single-s-p (ex-from-rp term))
                     (single-s-p term)))
            (and (integerp (rp-evlt term a))
                 (integerp (rp-evlt (ex-from-rp term) a))))
   :hints (("goal"
            :do-not-induct t
            :in-theory (e/d* (single-s-p
                              regular-rp-evl-of_s_when_mult-formula-checks_with-ex-from-rp)
                             ())))))

(local
 (defthm single-s-c-res-p-implies-integerp
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state)
                 (or (single-s-c-res-p (ex-from-rp term))
                     (single-s-c-res-p term)))
            (and (integerp (rp-evlt term a))
                 (integerp (rp-evlt (ex-from-rp term) a))))
   :hints (("goal"
            :do-not-induct t
            :in-theory (e/d* (single-s-c-res-p
                              regular-rp-evl-of_s-c-res_when_mult-formula-checks_with-ex-from-rp)
                             ())))))

(local
 (defthm valid-sc-of-list-one-element
   (equal (VALID-SC (LIST 'LIST x) A)
          (VALID-SC x A))
   :hints (("Goal"
            :in-theory (e/d (valid-sc
                             is-rp is-if)
                            ())))))

(local
 (defthm rp-termp-list-lemma
   (iff (RP-TERMP (LIST 'LIST x))
        (RP-TERMP x))
   :hints (("Goal"
            :in-theory (e/d (rp-termp) ())))))


(local
 (defthm unpack-booth-meta-correct-bitp-lemma
   (implies (and (or (OR* (BINARY-FNC-P term)
                          (SINGLE-S-P term))
                     (OR* (BINARY-FNC-P (ex-from-rp term))
                          (SINGLE-S-P   (ex-from-rp term))))
                 (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state))
            (and (bitp (rp-evlt term a))
                 (bitp (rp-evlt (ex-from-rp term) a))))
   :hints (("Goal"
            :in-theory (e/d* (or*
                              regular-eval-lemmas-with-ex-from-rp
                              regular-eval-lemmas) ())))))

(local
 (defthm binary-fnc-p-implies
   (implies (binary-fnc-p x)
            (and (not (SINGLE-S-C-RES-P x))
                 (not (SINGLE-S-P x))
                 (not (SINGLE-C-P x))))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (binary-fnc-p) ())))))

(defret unpack-booth-meta-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp term)
                (valid-sc term a))
           (and (valid-sc res a)
                (equal (rp-evlt res a)
                       (rp-evlt term a))))
  :fn unpack-booth-meta
  ;;:otf-flg t
  :hints (("goal"
           :do-not-induct t
           :use ((:instance pp-has-bitp-rp-implies
                            (term (cadr term)))
                 (:instance pp-has-bitp-rp-implies
                            (term (cadr (cadr term)))))
           :expand ((sum-list-eval (list (cadr term)) a)

                    (sum-list-eval (list (cadr (cadr term)))
                                   a))
           :in-theory (e/d* (or*
                             unpack-booth-meta
                             HAS-BITP-RP-FORCE-INSERT
                             ;;has-bitp-rp-force-insert
                             unpack-booth
                             s-c-res
                             regular-rp-evl-of_unpack-booth_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_unpack-booth_when_mult-formula-checks
                             regular-rp-evl-of_s-c-res_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_s-c-res_when_mult-formula-checks
                             regular-rp-evl-of_bit-of_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_bit-of_when_mult-formula-checks
                             (:rewrite regular-rp-evl-of_--_when_mult-formula-checks)
                             )
                            (rp-termp
                             (:REWRITE DUMMY-SUM-CANCEL-LEMMA1)
                             (:REWRITE PP-TERM-P-IS-BITP)
                             PP-TERM-P
                             (:TYPE-PRESCRIPTION VALID-SC)
                             pp-has-bitp-rp-implies
                             bitp
                             rp-trans-opener-when-list
                             rp-trans-opener
                             eval-and-all
                             valid-sc
                             ex-from-rp
                             not-include-rp-means-valid-sc-lst
                             not-include-rp-means-valid-sc
                             not-include-rp
                             include-fnc
                             when-ex-from-rp-is-1
                             sum-of-negated-elements
                             expand-sum-from-the-hyps
                             (:rewrite sum-cancel-common)
                             (:rewrite minus-of-minus)
                             (:definition sum-list-eval)
                             nfix
                             is-falist
                             rp-trans
                             rp-trans-lst
                             valid-sc)))))



(local
 (defthm valid-sc-of-cons
   (implies (and (NOT (EQUAL x 'IF))
                 (NOT (EQUAL x 'RP))
                 (NOT (EQUAL x 'QUOTE)))
            (equal (valid-sc (cons x other) a)
                   (valid-sc-subterms other a)))
   :hints (("Goal"
            :expand ((VALID-SC (CONS X OTHER) A))
            :in-theory (e/d (valid-sc is-rp IS-IF) ())))))

(local
 (defthm valid-sc-single-step-lemma
   (implies (and (rp-termp term)
                 (equal (car term) 'rp)
                 (valid-sc term a))
            (valid-sc (caddr term) a))
   :hints (("Goal"
            :in-theory (e/d (valid-sc-single-step) ())))))

(local
 (defthmd rp-evlt-of-fncall-args
   (implies (and (not (equal fn 'quote))
                 (not (equal fn 'falist))
                 (case-split (not (equal fn 'list))))
            (equal (rp-evlt (cons fn args) a)
                   (rp-evl (cons fn (kwote-lst (rp-evlt-lst args a)))
                           nil)))
   :hints (("goal"
            :expand ((:free (args)
                            (rp-trans (cons fn args))))
            :in-theory (e/d (rp-evl-of-fncall-args
                             rp-trans)
                            ())))))

(local
 (defthmd rp-evlt-of-fncall-args2
   (implies (and (consp term)
                 (not (equal (car term) 'quote))
                 (not (equal (car term) 'falist))

                 (not (equal (car term) 'if))
                 (case-split (not (equal (car term) 'list)))
                 )
            (equal (rp-evlt term a)
                   (rp-evl (cons (car term)
                                 (kwote-lst (rp-evlt-lst (cdr term) a)))
                           nil)))
   :hints (("goal"
            :expand ((:free (args)
                            (rp-trans (cons fn args))))
            :in-theory (e/d (rp-evl-of-fncall-args
                             rp-trans)
                            ())))))

#|(local
 (defthm rp-evlt-cons-equivalance
   (implies (and (AND (SYMBOLP TYPE)
                      (NOT (BOOLEANP TYPE))
                      (NOT (EQUAL TYPE 'QUOTE))
                      (NOT (EQUAL TYPE 'RP))
                      (NOT (EQUAL TYPE 'LIST))
                      (NOT (EQUAL TYPE 'FALIST)))
                 (equal (rp-evlt x a)
                        (rp-evlt y a)))
            (equal (rp-evlt (list type x) a)
                   (rp-evlt (list type y) a)))
   :hints (("Goal"
            :in-theory (e/d (rp-evl-of-fncall-args) ())))))|#

(local
 (defthm is-if-lemma
   (is-if `(if ,x ,y ,z))
   :hints (("Goal"
            :in-theory (e/d (is-if) ())))))

(local
 (defthm rp-evlt-when-list
   (implies (and (consp term)
                 (equal (car term) 'list))
            (equal (rp-evlt term a)
                   (RP-EVLT-LST (CDR term) A)))))

(local
 (progn
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
              )))))

(local
 (create-regular-eval-lemma if 3 MULT-FORMULA-CHECKS))

(defret-mutual unpack-booth-general-meta-correct

  (defret unpack-booth-general-meta-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (rp-termp term)
                  (valid-sc term a))
             (and (valid-sc result a)
                  (equal (rp-evlt result a)
                         (rp-evlt term a))))
    :fn unpack-booth-general-meta)

  (defret unpack-booth-general-meta-lst-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (rp-term-listp lst)
                  (valid-sc-subterms lst a))
             (and (valid-sc-subterms result-lst a)
                  (equal (rp-evlt-lst result-lst a)
                         (rp-evlt-lst lst a))))
    :fn unpack-booth-general-meta-lst)

  :mutual-recursion unpack-booth-general-meta
  :hints (("Goal"
           :expand ()
           :in-theory (e/d* (unpack-booth-general-meta
                             UNPACK-BOOTH-GENERAL-META-LST
                             is-rp-implies-fc
                             rp-evlt-of-fncall-args
                             rp-evlt-of-fncall-args2
                             valid-sc-single-step
                             (:REWRITE
                              REGULAR-RP-EVL-OF_IF_WHEN_MULT-FORMULA-CHECKS)
                             )
                            (FALIST-CONSISTENT
                             EVAL-AND-ALL
                             DEFAULT-CAR
                             eq
                             (:META BINARY-OR**/AND**-GUARD-META-CORRECT)
                             (:DEFINITION RP-EQUAL)
                             (:REWRITE VALID-SC-SUBTERMS-CDR)
                             EX-FROM-RP
                             VALID-SC-EX-FROM-RP-2
                             IS-IF-RP-TERMP
                             cons-equal
                             NOT-INCLUDE-RP
                             INCLUDE-FNC
                             rp-trans-is-term-when-list-is-absent
                             rp-trans
                             RP-TRANS-OPENER
                             RP-TRANS-LST
                             is-rp-of-cons
                             rp-termp

                             )))))
