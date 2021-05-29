; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
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

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

(local
 (include-book "lemmas"))

(include-book "summation-tree-meta-fncs")

(include-book "pp-flatten-meta-correct")

(local
 (in-theory (enable ex-from-rp-loose-is-ex-from-rp)))

(local
 (in-theory (enable rp-trans trans-list)))

(defun-sk rp-evlt-equiv (term1 term2)
  (forall a
          (equal (rp-evlt term1 a)
                 (rp-evlt term2 a))))

(defequiv rp-evlt-equiv
  :otf-flg t
  :hints (("Goal"
           :expand ((RP-EVLT-EQUIV X X)
                    (RP-EVLT-EQUIV X Z)
                    (RP-EVLT-EQUIV Y X))
           :use ((:instance RP-EVLT-EQUIV-NECC
                            (term1 x)
                            (term2 y)
                            (a (RP-EVLT-EQUIV-WITNESS X Z)))
                 (:instance RP-EVLT-EQUIV-NECC
                            (term1 y)
                            (term2 z)
                            (a (RP-EVLT-EQUIV-WITNESS X Z)))
                 (:instance RP-EVLT-EQUIV-NECC
                            (term1 x)
                            (term2 y)
                            (a (RP-EVLT-EQUIV-WITNESS Y X))))
           :in-theory (e/d ()
                           (rp-evlt-equiv
                            rp-evlt-equiv-necc)))))

(local
 (defthm-rp-equal
   (defthm rp-order-is-rp-equal
     (implies (and (rp-termp term1)
                   (rp-termp term2))
              (equal (mv-nth 1 (rp-order term1 term2))
                     (rp-equal term1 term2)))
     :flag rp-equal)
   (defthm rp-order-lst-is-rp-equal-subterms
     (implies (and (rp-term-listp subterm1)
                   (rp-term-listp subterm2))
              (equal (mv-nth 1 (rp-order-lst subterm1 subterm2))
                     (rp-equal-subterms subterm1 subterm2)))
     :flag rp-equal-subterms)
   :hints (("goal"
            :expand ((rp-order term1 term2))
            :in-theory (e/d (rp-order-lst
                             rp-order) ())))))

(progn
  (defthm rp-trans-opener
    (implies (and (not (equal x 'quote))
                  (not (equal x 'list))
                  (not (equal x 'falist)))
             (equal (rp-trans (cons x rest))
                    (cons x (rp-trans-lst rest))))
    :hints (("Goal"
             :in-theory (e/d (rp-trans) ()))))

  (defthm rp-trans-opener-when-list
    (implies t
             (equal (rp-trans (cons 'list rest))
                    (TRANS-LIST (RP-TRANS-LST rest))))
    :hints (("Goal"
             :in-theory (e/d (rp-trans) ()))))

  (defthm rp-trans-opener-when-falist
    (implies (is-falist (cons 'falist rest))
             (equal (rp-trans (cons 'falist rest))
                    (RP-TRANS (CADDR (cons 'falist rest)))))
    :hints (("Goal"
             :in-theory (e/d (rp-trans) ()))))

  (defthm rp-trans-opener-when-quotep
    (implies (rp-trans (cons 'quote rest))
             (cons 'quote rest)))

  (local
   (defthm RP-EVL-OF-TRANS-LIST-opener
     (equal (rp-evl-lst (cons x y) a)
            (cons (rp-evl x a)
                  (rp-evl-lst y a)))
     :hints (("Goal"
              :in-theory (e/d () ())))))
  (local
   (defthm RP-EVL-OF-TRANS-LIST-opener-when-nil
     (equal (RP-EVL-lst nil a)
            nil)
     :hints (("Goal"
              :in-theory (e/d () ())))))

  (in-theory (disable rp-trans)))

(create-regular-eval-lemma -- 1 mult-formula-checks)
(create-regular-eval-lemma binary-append 2 mult-formula-checks)
(create-regular-eval-lemma binary-and 2 mult-formula-checks)
(create-regular-eval-lemma and-list 1 mult-formula-checks)

(defun sum-list-eval (lst a)
  (if (atom lst)
      0
    (sum (rp-evlt (car lst) a)
         (sum-list-eval (cdr lst) a))))

(local
 (defthm to-list*-sum-eval
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state))
            (and (equal (sum-list (rp-evl (trans-list (rp-trans-lst lst)) A))
                        (sum-list-eval lst a))
                 (equal (SUM-LIST (RP-EVL-lst (RP-TRANS-LST LST)
                                              A))
                        (sum-list-eval lst a))))
   :hints (("Goal"
            :do-not-induct t
            :induct (sum-list-eval lst a)
            :in-theory (e/d (sum-list
                             trans-list) ())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; pp-sum-merge and s-sum-merge lemmas

(local
 (define negated-termsp ((term1)
                         (term2))
   (b* (((mv neg1 term1)
         (case-match term1 (('-- a) (mv t a)) (& (mv nil term1))))
        ((mv neg2 term2)
         (case-match term2 (('-- a) (mv t a)) (& (mv nil term2))))
        (equals
         (rp-equal term1 term2)))
     (and (not (equal neg1 neg2))
          equals))))

(local
 (defthm sum-of-negated-terms
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state)
                 (negated-termsp x y))
            (and (equal (sum (rp-evlt x a) (rp-evlt y a))
                        0)
                 (equal (sum (rp-evlt x a) (rp-evlt y a) z)
                        (ifix z))))
   :hints (("Goal"
            :in-theory (e/d* (negated-termsp
                              (:REWRITE REGULAR-RP-EVL-OF_--_WHEN_MULT-FORMULA-CHECKS)
                              sum
                              --)
                             (rp-equal-cnt
                              ex-from-rp
                              rp-equal
                              UNICITY-OF-0
                              rp-evl-of-rp-equal
                              +-is-SUM))
            :use ((:instance rp-evlt-of-rp-equal
                             (term1 x)
                             (term2 (cadr y)))
                  (:instance rp-evlt-of-rp-equal
                             (term1 y)
                             (term2 (cadr x))))))))

(local
 (defthm s-order-and-negated-termsp-redef
   (implies (and (rp-termp term1)
                 (rp-termp term2))
            (equal (MV-NTH 1
                           (s-order-and-negated-termsp term1
                                                       term2))
                   (negated-termsp term1 term2)))
   :hints (("Goal"
            :in-theory (e/d (s-order-and-negated-termsp
                             negated-termsp)
                            ())))))

(local
 (defthm PP-LIST-ORDER-aux-equals-redef
   (equal (mv-nth 1 (PP-LIST-ORDER-aux x y))
          (equal x y))
   :hints (("Goal"
            :in-theory (e/d (pp-list-order-aux) ())))))

(local
 (defthm PP-LIST-ORDER-equals-redef
   (equal (mv-nth 1 (PP-LIST-ORDER x y))
          (equal x y))
   :hints (("Goal"
            :in-theory (e/d (pp-list-order) ())))))

(local
 (defthm rp-trans-when-list
   (implies (and (equal (car lst) 'list)
                 (consp lst))
            (equal (rp-trans lst)
                   (TRANS-LIST (RP-TRANS-LST (cdr lst)))))
   :hints (("Goal"
            :expand (rp-trans lst)
            :in-theory (e/d () ())))
   :rule-classes :rewrite))

(local
 (defthmd pp-order-equals-implies
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state)
                 (mv-nth 1 (pp-order x y)))
            (equal (rp-evlt x a)
                   (rp-evlt y a)))
   :hints (("Goal"
            :do-not-induct t
            :expand ((:free (x) (nth 1 x))
                     (:free (x) (nth 0 x))
                     (:free (x) (nth 2 x))
                     (:free (x) (nth 3 x)))
            :in-theory (e/d (pp-order
                             and$-is-and-list)
                            (rp-termp
                             nth
                             (:REWRITE
                              RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT)
                             (:REWRITE RP-EVL-OF-RP-EQUAL-LOOSE)
                             (:REWRITE ACL2::O-P-O-INFP-CAR)
                             (:DEFINITION RP-EQUAL-LOOSE)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_BINARY-APPEND_WHEN_MULT-FORMULA-CHECKS)
                             (:REWRITE RP-TERMP-OF-RP-TRANS)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_--_WHEN_MULT-FORMULA-CHECKS)
                             (:TYPE-PRESCRIPTION AND-LIST)
                             (:TYPE-PRESCRIPTION O<)
                             (:DEFINITION RP-EQUAL)
                             (:DEFINITION EX-FROM-RP)
                             (:REWRITE RP-EVL-OF-RP-EQUAL2)
                             (:DEFINITION RP-EQUAL2)
                             (:REWRITE DEFAULT-CDR)
                             (:REWRITE RP-EQUAL-IMPLIES-RP-EQUAL2)
                             (:REWRITE RP-EQUAL-IS-SYMMETRIC)
                             (:TYPE-PRESCRIPTION RP-TERMP)
                             (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                             (:TYPE-PRESCRIPTION RP-TRANS-LST)
                             (:REWRITE DEFAULT-CAR)
                             (:REWRITE EX-FROM-SYNP-LEMMA1)
                             (:DEFINITION RP-TRANS)
                             RP-EVL-OF-VARIABLE
                             len))))))

(local
 (defthm pp-order-and-negated-termsp-implies-negated-termsp
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state)
                 (mv-nth 1 (pp-order-and-negated-termsp x y)))
            (and (equal (sum (rp-evlt x a) (rp-evlt y a))
                        0)
                 (equal (sum (rp-evlt x a) (rp-evlt y a) z)
                        (ifix z))))
   :hints (("goal"
            :do-not-induct t
            :use ((:instance pp-order-equals-implies
                             (x (cadr x))
                             (y y))
                  (:instance pp-order-equals-implies
                             (x x)
                             (y (cadr y)))
                  (:instance rp-evlt-of-rp-equal
                             (term1 x)
                             (term2 (cadr y)))
                  (:instance rp-evlt-of-rp-equal
                             (term1 y)
                             (term2 (cadr x))))
            :in-theory (e/d (pp-order-and-negated-termsp)
                            (rp-evlt-of-rp-equal
                             rp-equal))))))

(progn
  (defthm pp-sum-merge-aux-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state))
             (equal (sum-list (rp-evlt `(list . ,(mv-nth 0 (pp-sum-merge-aux
                                                            term1 term2 cnt)))
                                       a))
                    (sum (sum-list (rp-evlt `(list . ,term1) a))
                         (sum-list (rp-evlt `(list . ,term2) a)))))
    :hints (("Goal"
             :do-not-induct t
             :expand ((RP-TRANS (CONS 'LIST* TERM2))
                      (:free (x y)
                             (sum-list (cons x y)))
                      (RP-TRANS (CONS 'LIST* TERM1)))
             :induct (pp-sum-merge-aux term1 term2 cnt)
             :in-theory (e/d (pp-sum-merge-aux)
                             (rp-termp)))))

  (defthm pp-sum-merge-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state))
             (equal (sum-list (rp-evlt (mv-nth 0 (pp-sum-merge term1 term2)) a))
                    (sum (sum-list (rp-evlt term1 a))
                         (sum-list (rp-evlt term2 a)))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance pp-sum-merge-aux-correct
                              (term1 (cdr term1))
                              (term2 (cdr term2))
                              (cnt 0)))
             :in-theory (e/d (pp-sum-merge)
                             (rp-trans
                              pp-sum-merge-aux-correct)))))

  (defthm pp-sum-merge-correct-with-sk
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state))
             (rp-evlt-equiv  `(sum-list ,(mv-nth 0 (pp-sum-merge term1 term2)))
                             `(binary-sum (sum-list ,term1)
                                          (sum-list ,term2))))
    :hints (("Goal"
             :in-theory (e/d () ())))))

(progn
  (defthm s-sum-merge-aux-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (rp-term-listp term1)
                  (rp-term-listp term2))
             (equal (sum-list (rp-evlt `(list . ,(s-sum-merge-aux term1 term2)) a))
                    (sum (sum-list (rp-evlt `(list . ,term1) a))
                         (sum-list (rp-evlt `(list . ,term2) a)))))
    :hints (("Goal"
             :do-not-induct t
             :expand ((RP-TRANS (CONS 'LIST* TERM2))
                      (:free (x y)
                             (sum-list (cons x y)))
                      (RP-TRANS (CONS 'LIST* TERM1)))
             :induct (s-sum-merge-aux term1 term2)
             :in-theory (e/d (s-sum-merge-aux) (rp-termp)))))

  (defthm s-sum-merge-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (rp-termp term1)
                  (rp-termp term2))
             (equal (sum-list (rp-evlt (s-sum-merge term1 term2) a))
                    (sum (sum-list (rp-evlt term1 a))
                         (sum-list (rp-evlt term2 a)))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance s-sum-merge-aux-correct
                              (term1 (cdr term1))
                              (term2 (cdr term2))))
             :in-theory (e/d (s-sum-merge)
                             (rp-termp
                              s-sum-merge-aux-correct
                              rp-trans)))))

  (defthm s-sum-merge-correct-with-sk
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (rp-termp term1)
                  (rp-termp term2))
             (rp-evlt-equiv `(sum-list ,(s-sum-merge term1 term2))
                            `(binary-sum (sum-list ,term1)
                                         (sum-list ,term2))))))

(progn
  (defthm pp-sum-merge-aux-valid-sc-subterms
    (implies (and (valid-sc-subterms lst1 a)
                  (valid-sc-subterms lst2 a))
             (valid-sc-subterms (mv-nth 0 (pp-sum-merge-aux
                                           lst1 lst2 cnt))
                                a))
    :hints (("Goal"
             :induct (pp-sum-merge-aux
                      lst1 lst2 cnt)
             :do-not-induct t
             :in-theory (e/d (pp-sum-merge-aux) ()))))

  (defthm pp-sum-merge-valid-sc
    (implies (and (valid-sc term1 a)
                  (valid-sc term2 a))
             (valid-sc (mv-nth 0 (pp-sum-merge term1 term2)) a))
    :hints (("Goal"
             :expand ((:free (x y) (IS-RP (CONS x y)))
                      (:free (x y) (IS-if (CONS x y))))
             :in-theory (e/d (pp-sum-merge
                              pp-sum-merge-aux-valid-sc-subterms)
                             ()))))

  (defthm s-sum-merge-aux-valid-sc-subterms
    (implies (and (valid-sc-subterms lst1 a)
                  (valid-sc-subterms lst2 a))
             (valid-sc-subterms (s-sum-merge-aux lst1 lst2)
                                a))
    :hints (("Goal"
             :induct (s-sum-merge-aux lst1 lst2 )
             :do-not-induct t
             :in-theory (e/d (s-sum-merge-aux) ()))))

  (defthm s-sum-merge-valid-sc
    (implies (and (valid-sc term1 a)
                  (valid-sc term2 a))
             (valid-sc (s-sum-merge term1 term2) a))
    :hints (("Goal"
             :expand ((:free (x y) (IS-RP (CONS x y)))
                      (:free (x y) (IS-if (CONS x y))))
             :in-theory (e/d (s-sum-merge
                              s-sum-merge-aux-valid-sc-subterms)
                             ())))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; s-fix-args lemmas

(defthmd rp-evlt-of-ex-from-rp-reverse
  (implies (syntaxp (or (atom term)
                        (not (equal (car term) 'ex-from-rp))))
           (EQUAL (RP-EVL (RP-TRANS TERM) A)
                  (RP-EVL (RP-TRANS (EX-FROM-RP TERM)) A))))
(local
 (defthm RP-EVL-OF-TRANS-LIST-of-nil
   (equal (RP-EVL-lst NIL A)
          nil)
   :hints (("Goal"
            :in-theory (e/d () ())))))

(defthm s-fix-pp-args-aux-correct-dummy-lemma1
  (and (equal (equal (m2 (sum rest1 a))
                     (m2 (sum a rest2)))
              (equal (m2 rest1)
                     (m2 rest2)))
       (equal (equal (m2 (sum rest1 a))
                     (m2 (sum rest2 a)))
              (equal (m2 rest1)
                     (m2 rest2)))
       (equal (equal (m2 a)
                     (m2 (sum rest2 a)))
              (equal  (m2 rest2)
                      0))
       (equal (equal (m2 a)
                     (m2 (sum rest1 rest2 a)))
              (equal  (m2 (sum rest1 rest2))
                      0))))

(defthm rp-equal-of-ex-from-rp
  (and (equal (rp-equal (ex-from-rp term1) term2)
              (rp-equal term1 term2))
       (equal (rp-equal term1 (ex-from-rp term2))
              (rp-equal term1 term2)))
  :hints (("Goal"
           :do-not-induct t
           :expand ((rp-equal (ex-from-rp term1) term2)
                    (rp-equal term1 (ex-from-rp term2)))
           :in-theory (e/d () (RP-EQUAL-IS-SYMMETRIC)))))

(progn
  (defthm s-fix-pp-args-aux-correct-dummy-lemma2
    (implies (rp-equal term1 term2)
             (equal (EQUAL (M2 (SUM (RP-EVL (RP-TRANS term1) a)
                                    (RP-EVL (RP-TRANS term2) a)))
                           0)
                    t))
    :hints (("Goal"
             :use ((:instance rp-evlt-of-rp-equal)
                   (:instance m2-of-times2
                              (a (RP-EVL (RP-TRANS term1) A))
                              (b 0)))
             :in-theory (e/d (times2) (rp-evlt-of-rp-equal
                                       m2-of-times2)))))

  (defthm s-fix-pp-args-aux-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (rp-term-listp pp-lst))
             (and (equal (m2 (sum (sum-list-eval (s-fix-pp-args-aux pp-lst) a) c/d))
                         (s (rp-evlt `(list . ,pp-lst) a) c/d))
                  (equal (m2 (sum-list-eval (s-fix-pp-args-aux pp-lst) a))
                         (s (rp-evlt `(list . ,pp-lst) a) 0))))
    :hints (("Goal"
             :do-not-induct t
             :expand ((:free (x y)
                             (sum-list (cons x y)))
                      )
             :induct (s-fix-pp-args-aux pp-lst)
             :in-theory (e/d* (s-fix-pp-args-aux
                               (:REWRITE
                                REGULAR-RP-EVL-OF_--_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                               rp-evlt-of-ex-from-rp-reverse)
                              (rp-evlt-of-ex-from-rp)))))

  (defthmd s-fix-args-correct-lemma1
    (Implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (rp-term-listp lst)
                  (not (s-fix-pp-args-aux lst)))
             (equal (m2 (SUM-LIST-EVAL lst A))
                    0))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance s-fix-pp-args-aux-correct
                              (pp-lst lst)))
             :in-theory (e/d ()
                             (s-fix-pp-args-aux-correct)))))

  (defthm s-fix-args-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (rp-termp term))
             (and (equal (m2 (sum (sum-list (rp-evlt (s-fix-args term) a)) c/d))
                         (s (rp-evlt term a) c/d))
                  (equal (m2 (sum-list (rp-evlt (s-fix-args term) a)))
                         (m2 (sum-list (rp-evlt term a))))
                  (equal (m2 (sum o1 o2 (sum-list (rp-evlt (s-fix-args term) a))))
                         (m2 (sum o1 o2 (sum-list (rp-evlt term a)))))
                  (equal (m2 (sum o1 o2 o3 (sum-list (rp-evlt (s-fix-args term) a))))
                         (m2 (sum o1 o2 o3 (sum-list (rp-evlt term a)))))
                  (equal (m2 (sum o1 (sum-list (rp-evlt (s-fix-args term) a))))
                         (m2 (sum o1 (sum-list (rp-evlt term a)))))))
    :hints (("Goal"
             :in-theory (e/d (s-fix-args
                              s-fix-args-correct-lemma1)
                             (rp-trans RP-EVL-OF-TRANS-LIST-LEMMA))))))

(defthm s-fix-args-correct-with-sk
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp term))
           (and (rp-evlt-equiv `(m2 (binary-sum (sum-list ,(s-fix-args term)) c/d))
                               `(s ,term c/d))
                (rp-evlt-equiv `(m2 (sum-list ,(s-fix-args term)))
                               `(m2 (sum-list ,term)))
                (rp-evlt-equiv `(m2 (binary-sum o1 (binary-sum o2 (sum-list ,(s-fix-args term)))))
                               `(m2 (binary-sum o1 (binary-sum o2 (sum-list ,term)))))
                (rp-evlt-equiv `(m2 (binary-sum o1 (binary-sum o2 (binary-sum o3 (sum-list ,(s-fix-args term))))))
                               `(m2 (binary-sum o1 (binary-sum o2 (binary-sum o3 (sum-list ,term))))))
                (rp-evlt-equiv `(m2 (binary-sum o1 (sum-list ,(s-fix-args term))))
                               `(m2 (binary-sum o1 (sum-list ,term)))))))

(defthm s-fix-pp-args-aux-valid-sc-subterms
  (implies (and (valid-sc-subterms pp-lst a)
                (rp-term-listp pp-lst))
           (valid-sc-subterms (s-fix-pp-args-aux pp-lst) a))
  :hints (("Goal"
           :do-not-induct t
           :induct (s-fix-pp-args-aux pp-lst)
           :in-theory (e/d (s-fix-pp-args-aux) ()))))

(defthm s-fix-args-valid-sc
  (implies (and (valid-sc pp a)
                (rp-termp pp))
           (valid-sc (s-fix-args pp) a))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (s-fix-args
                            is-if is-rp) ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; and c/d-fix-pp-args
;; and c/d-fix-s-args lemmas

(defthmd c/d-fix-arg-aux-correct-lemma
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-term-listp pp-lst))
           (b* (((mv coughed result)
                 (c/d-fix-arg-aux pp-lst neg-flag limit)))
             (and (equal
                   (sum (times2 (sum-list-eval coughed a))
                        (sum-list-eval result a)
                        rest)
                   (sum (sum-list-eval pp-lst a) rest))
                  (equal
                   (sum  (sum-list-eval result a)
                         (times2 (sum-list-eval coughed a))
                         rest)
                   (sum (sum-list-eval pp-lst a) rest))
                  (equal
                   (sum  (sum-list-eval result a)
                         (times2 (sum-list-eval coughed a)))
                   (sum (sum-list-eval pp-lst a)))
                  (equal
                   (sum  (times2 (sum-list-eval coughed a))
                         (sum-list-eval result a))
                   (sum (sum-list-eval pp-lst a))))))
  :hints (("Goal"
           :do-not-induct t
           :expand ((:free (x y)
                           (sum-list (cons x y)))
                    )
           :induct (c/d-fix-arg-aux pp-lst neg-flag limit)
           :in-theory (e/d* (c/d-fix-arg-aux
                             times2
                             (:REWRITE
                              REGULAR-RP-EVL-OF_--_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             rp-evlt-of-ex-from-rp-reverse
                             sum-comm-1-loop-stopper
                             sum-comm-2-loop-stopper
                             )
                            (rp-evlt-of-ex-from-rp
                             sum-comm-1
                             sum-comm-2
                             rp-evlt-of-rp-equal
                             (:DEFINITION RP-TERMP)
                             (:DEFINITION FALIST-CONSISTENT)
                             (:REWRITE DEFAULT-CDR)
                             (:DEFINITION EX-FROM-RP)
                             (:REWRITE DEFAULT-CAR)
                             (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                             F2-OF-TIMES2
                             rp-trans)))
          ("Subgoal *1/3"
           :use ((:instance rp-evlt-of-rp-equal
                            (term1 (EX-FROM-RP (CAR PP-LST)))
                            (term2 (EX-FROM-RP (CADR PP-LST))))))))

(defthmd c/d-fix-arg-aux-correct-dummy-lemma1
  (Implies (force (integerp x))
           (equal (EQUAL x (SUM a (-- c)))
                  (equal (sum c x) (ifix a))))
  :hints (("Goal"
           :in-theory (e/d (sum --)
                           (+-is-SUM)))))

(defthmd f2-of-times2-reverse
  (implies (syntaxp (or (atom a)
                        (not (equal (car a) '--))))
           (EQUAL (SUM A (F2 b))
                  (F2 (SUM (TIMES2 A) B)))))

(defthmd d2-of-times2-reverse
  (implies (syntaxp (or (atom a)
                        (and (not (equal (car a) 'd2))
                             (not (equal (car a) '--)))))
           (EQUAL (SUM A (d2 b))
                  (d2 (SUM (TIMES2 A) B)))))

(defthm c/d-fix-pp-args-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp pp))
           (b* (((mv coughed result)
                 (c/d-fix-pp-args pp limit)))
             (and (equal
                   (sum (times2 (sum-list (rp-evlt coughed a)))
                        (sum-list (rp-evlt result a))
                        rest)
                   (sum (sum-list (rp-evlt pp a)) rest))
                  (equal
                   (sum rest
                        (times2 (sum-list (rp-evlt coughed a)))
                        (sum-list (rp-evlt result a)))
                   (sum (sum-list (rp-evlt pp a)) rest))
                  (equal
                   (sum  (sum-list (rp-evlt result a))
                         (times2 (sum-list (rp-evlt coughed a)))
                         rest)
                   (sum (sum-list (rp-evlt pp a)) rest))
                  (equal
                   (sum  (sum-list (rp-evlt result a))
                         (times2 (sum-list (rp-evlt coughed a))))
                   (sum (sum-list (rp-evlt pp a))))
                  (equal
                   (sum  (times2 (sum-list (rp-evlt coughed a)))
                         (sum-list (rp-evlt result a)))
                   (sum (sum-list (rp-evlt pp a)))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance c/d-fix-arg-aux-correct-lemma
                            (neg-flag t)
                            (pp-lst (cdr pp))))
           :in-theory (e/d (c/d-fix-pp-args)
                           (c/d-fix-arg-aux-correct-lemma)))))

#|(defthm c/d-fix-pp-args-correct-wit-sk
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp pp))
           (b* (((mv coughed result)
                 (c/d-fix-pp-args pp limit)))
             (and (rp-evlt-equiv
                   `(binary-sum (times2 (sum-list ,coughed))
                                (binary-sum (sum-list ,result)
                                            ,rest))
                   `(binary-sum (sum-list ,pp) ,rest))
                  (rp-evlt-equiv
                   `(binary-sum  (sum-list ,result)
                                 (binary-sum (times2 (sum-list ,coughed))
                                             ,rest))
                   `(binary-sum (sum-list ,pp) ,rest))
                  (rp-evlt-equiv
                   `(binary-sum  (sum-list ,result)
                                 (times2 (sum-list ,coughed)))
                   `(sum-list ,pp))
                  (rp-evlt-equiv
                   `(binary-sum  (times2 (sum-list ,coughed))
                                 (sum-list ,result))
                   `(sum-list ,pp)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d ()
                           (c/d-fix-arg-aux-correct-lemma)))))||#

(defthm c/d-fix-s-args-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp pp))
           (b* (((mv coughed result)
                 (c/d-fix-s-args pp)))
             (and (equal
                   (sum (times2 (sum-list (rp-evlt coughed a)))
                        (sum-list (rp-evlt result a))
                        rest)
                   (sum (sum-list (rp-evlt pp a)) rest))
                  (equal
                   (sum  (sum-list (rp-evlt result a))
                         (times2 (sum-list (rp-evlt coughed a)))
                         rest)
                   (sum (sum-list (rp-evlt pp a)) rest))
                  (equal
                   (sum  (sum-list (rp-evlt result a))
                         (times2 (sum-list (rp-evlt coughed a))))
                   (sum (sum-list (rp-evlt pp a))))
                  (equal
                   (sum  (times2 (sum-list (rp-evlt coughed a)))
                         (sum-list (rp-evlt result a)))
                   (sum (sum-list (rp-evlt pp a)))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance c/d-fix-arg-aux-correct-lemma
                            (neg-flag nil)
                            (limit (expt 2 30))
                            (pp-lst (cdr pp))))
           :in-theory (e/d (c/d-fix-s-args)
                           (c/d-fix-arg-aux-correct-lemma)))))

#|(defthm c/d-fix-s-args-correct-with-sk
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp pp))
           (b* (((mv coughed result)
                 (c/d-fix-s-args pp)))
             (and (rp-evlt-equiv
                   `(binary-sum (times2 (sum-list ,coughed))
                                (BINARY-sum (sum-list ,result)
                                            ,rest))
                   `(binary-sum (sum-list ,pp) ,rest))
                  (rp-evlt-equiv
                   `(binary-sum (sum-list ,result)
                                (binary-sum (times2 (sum-list ,coughed))
                                            ,rest))
                   `(binary-sum (sum-list ,pp) ,rest))
                  (rp-evlt-equiv
                   `(binary-sum  (sum-list ,result)
                                 (times2 (sum-list ,coughed)))
                   `(sum-list ,pp))
                  (rp-evlt-equiv
                   `(binary-sum  (times2 (sum-list ,coughed))
                                 (sum-list ,result))
                   `(sum-list ,pp)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d ()
                           (c/d-fix-arg-aux-correct-lemma)))))||#

;; about evenpi:
(defthmd c/d-fix-arg-aux-retains-evenpi
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-term-listp pp-lst))
           (b* (((mv & result)
                 (c/d-fix-arg-aux pp-lst neg-flag limit)))
             (and (equal (evenpi (sum-list-eval result a))
                         (evenpi (sum-list-eval pp-lst a))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance c/d-fix-arg-aux-correct-lemma))
           :in-theory (e/d ()
                           (rp-evlt-of-ex-from-rp
                            rp-evlt-of-rp-equal
                            (:DEFINITION RP-TERMP)
                            (:DEFINITION FALIST-CONSISTENT)
                            (:REWRITE DEFAULT-CDR)
                            (:DEFINITION EX-FROM-RP)
                            (:REWRITE DEFAULT-CAR)
                            (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                            F2-OF-TIMES2
                            rp-trans)))
          ("Subgoal *1/3"
           :use ((:instance rp-evlt-of-rp-equal
                            (term1 (EX-FROM-RP (CAR PP-LST)))
                            (term2 (EX-FROM-RP (CADR PP-LST))))))))

(defthm c/d-fix-pp-args-retains-evenpi
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp pp))
           (b* (((mv ?coughed result)
                 (c/d-fix-pp-args pp limit)))
             (equal (evenpi (sum-list (rp-evlt result a)))
                    (evenpi (sum-list (rp-evlt pp a))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance c/d-fix-arg-aux-retains-evenpi
                            (neg-flag t)
                            (pp-lst (cdr pp))))
           :in-theory (e/d (c/d-fix-pp-args)
                           (c/d-fix-arg-aux-retains-evenpi)))))

(defthm c/d-fix-pp-args-retains-evenpi-with-other
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp pp))
           (b* (((mv ?coughed result)
                 (c/d-fix-pp-args pp limit)))
             (and (equal (evenpi (sum other (sum-list (rp-evlt result a))))
                         (evenpi (sum other (sum-list (rp-evlt pp a)))))
                  (equal (evenpi (sum (sum-list (rp-evlt result a)) other))
                         (evenpi (sum (sum-list (rp-evlt pp a)) other)))
                  (equal (evenpi (sum other1 other2 (sum-list (rp-evlt result a))))
                         (evenpi (sum other1 other2 (sum-list (rp-evlt pp a))))))))
  :hints (("Goal"
           :use ((:instance evenpi-with-other
                            (x (sum-list (rp-evlt (MV-NTH 1 (C/D-FIX-PP-ARGS PP
                                                                             LIMIT)) a)))
                            (y (sum-list (rp-evlt pp a)))
                            (z other))
                 (:instance evenpi-with-other
                            (x (sum-list (rp-evlt (MV-NTH 1 (C/D-FIX-PP-ARGS PP
                                                                             LIMIT)) a)))
                            (y (sum-list (rp-evlt pp a)))
                            (z (sum other1 other2))))
           :in-theory (e/d () ()))))

(defthm c/d-fix-s-args-retains-evenpi
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp pp))
           (b* (((mv ?coughed result)
                 (c/d-fix-s-args pp)))
             (equal (evenpi (sum-list (rp-evlt result a)))
                    (evenpi (sum-list (rp-evlt pp a))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance c/d-fix-arg-aux-retains-evenpi
                            (neg-flag nil)
                            (limit (expt 2 30))
                            (pp-lst (cdr pp))))
           :in-theory (e/d (c/d-fix-s-args)
                           (c/d-fix-arg-aux-retains-evenpi)))))

(defthm c/d-fix-s-args-retains-evenpi-with-other
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp pp))
           (b* (((mv ?coughed result)
                 (c/d-fix-s-args pp)))
             (and (equal (evenpi (sum other (sum-list (rp-evlt result a))))
                         (evenpi (sum other (sum-list (rp-evlt pp a)))))
                  (equal (evenpi (sum (sum-list (rp-evlt result a)) other))
                         (evenpi (sum (sum-list (rp-evlt pp a)) other)))
                  (equal (evenpi (sum other1 other2 (sum-list (rp-evlt result a))))
                         (evenpi (sum other1 other2 (sum-list (rp-evlt pp a)))))
                  (equal (evenpi (sum other1 other2 other3 (sum-list (rp-evlt result a))))
                         (evenpi (sum other1 other2 other3 (sum-list (rp-evlt pp a)))))
                  (equal (evenpi (sum other1 other2 other3 other4 (sum-list (rp-evlt result a))))
                         (evenpi (sum other1 other2 other3 other4 (sum-list (rp-evlt pp a))))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance evenpi-with-other
                            (x (sum-list (rp-evlt (MV-NTH 1 (C/D-FIX-s-ARGS PP)) a)))
                            (y (sum-list (rp-evlt pp a)))
                            (z other))
                 (:instance evenpi-with-other
                            (x (sum-list (rp-evlt (MV-NTH 1 (C/D-FIX-s-ARGS PP)) a)))
                            (y (sum-list (rp-evlt pp a)))
                            (z (sum other1 other2)))
                 (:instance evenpi-with-other
                            (x (sum-list (rp-evlt (MV-NTH 1 (C/D-FIX-s-ARGS PP)) a)))
                            (y (sum-list (rp-evlt pp a)))
                            (z (sum other1 other2 other3)))
                 (:instance evenpi-with-other
                            (x (sum-list (rp-evlt (MV-NTH 1 (C/D-FIX-s-ARGS PP)) a)))
                            (y (sum-list (rp-evlt pp a)))
                            (z (sum other1 other2 other3 other4))))
           :in-theory (e/d ()
                           ()))))

;; (defthm c/d-fix-arg-aux-correct-for-f2
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state)
;;                 (rp-term-listp pp-lst))
;;            (b* (((mv coughed result)
;;                  (c/d-fix-arg-aux pp-lst neg-flag limit)))
;;              (and (equal
;;                    (f2 (sum (sum-list-eval result a) rest))
;;                    (sum (-- (sum-list-eval coughed a))
;;                         (f2 (sum (sum-list-eval pp-lst a)
;;                                  rest))))
;;                   (equal
;;                    (f2 (sum-list-eval result a))
;;                    (sum (-- (sum-list-eval coughed a))
;;                         (f2 (sum-list-eval pp-lst a)))))))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :expand ((:free (x y)
;;                            (sum-list (cons x y)))
;;                     (:free (x y)
;;                            (RP-EVL-OF-TRANS-LIST (cons x y) a)))
;;            :use ((:instance c/d-fix-arg-aux-correct-lemma))
;;            :in-theory (e/d (times2
;;                             c/d-fix-arg-aux-correct-dummy-lemma1
;;                             rp-evlt-of-ex-from-rp-reverse
;;                             f2-of-times2-reverse)
;;                            (rp-evlt-of-ex-from-rp
;;                             rp-evlt-of-rp-equal
;;                             (:DEFINITION RP-TERMP)
;;                             (:DEFINITION FALIST-CONSISTENT)
;;                             (:REWRITE DEFAULT-CDR)
;;                             (:DEFINITION EX-FROM-RP)
;;                             (:REWRITE DEFAULT-CAR)
;;                             (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
;;                             F2-OF-TIMES2
;;                             rp-trans)))))

;; (defthm c/d-fix-arg-aux-correct-for-d2
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state)
;;                 (rp-term-listp pp-lst))
;;            (b* (((mv coughed result)
;;                  (c/d-fix-arg-aux pp-lst neg-flag limit)))
;;              (and (equal
;;                    (d2 (sum (sum-list-eval result a) rest))
;;                    (sum (-- (sum-list-eval coughed a))
;;                         (d2 (sum (sum-list-eval pp-lst a)
;;                                  rest))))
;;                   (equal
;;                    (d2 (sum-list-eval result a))
;;                    (sum (-- (sum-list-eval coughed a))
;;                         (d2 (sum-list-eval pp-lst a)))))))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :expand ((:free (x y)
;;                            (sum-list (cons x y)))
;;                     (:free (x y)
;;                            (RP-EVL-OF-TRANS-LIST (cons x y) a)))
;;            :use ((:instance c/d-fix-arg-aux-correct-lemma))
;;            :in-theory (e/d (times2
;;                             c/d-fix-arg-aux-correct-dummy-lemma1
;;                             rp-evlt-of-ex-from-rp-reverse
;;                             d2-of-times2-reverse)
;;                            (rp-evlt-of-ex-from-rp
;;                             rp-evlt-of-rp-equal
;;                             (:DEFINITION RP-TERMP)
;;                             (:DEFINITION FALIST-CONSISTENT)
;;                             (:REWRITE DEFAULT-CDR)
;;                             (:DEFINITION EX-FROM-RP)
;;                             (:REWRITE DEFAULT-CAR)
;;                             (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
;;                             d2-OF-TIMES2
;;                             rp-trans)))))

;; (defthm c/d-fix-pp-args-correct-for-f2
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state)
;;                 (rp-termp pp))
;;            (b* (((mv coughed result)
;;                  (c/d-fix-pp-args pp limit)))
;;              (equal
;;               (f2 (sum (sum-list (rp-evlt result a)) rest))
;;               (sum (-- (sum-list (rp-evlt coughed a)))
;;                    (f2 (sum (sum-list (rp-evlt pp a))
;;                             rest))))))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :use ((:instance c/d-fix-arg-aux-correct-for-f2
;;                             (neg-flag t)
;;                             (pp-lst (cdr pp))))
;;            :in-theory (e/d (c/d-fix-pp-args)
;;                            (c/d-fix-arg-aux-correct-for-f2)))))

;; (defthm c/d-fix-pp-args-correct-for-d2
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state)
;;                 (rp-termp pp))
;;            (b* (((mv coughed result)
;;                  (c/d-fix-pp-args pp limit)))
;;              (equal
;;               (d2 (sum (sum-list (rp-evlt result a)) rest))
;;               (sum (-- (sum-list (rp-evlt coughed a)))
;;                    (d2 (sum (sum-list (rp-evlt pp a))
;;                             rest))))))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :use ((:instance c/d-fix-arg-aux-correct-for-d2
;;                             (neg-flag t)
;;                             (pp-lst (cdr pp))))
;;            :in-theory (e/d (c/d-fix-pp-args)
;;                            (c/d-fix-arg-aux-correct-for-d2)))))

;; (defthm c/d-fix-s-args-correct-for-f2
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state)
;;                 (rp-termp pp))
;;            (b* (((mv coughed result)
;;                  (c/d-fix-s-args pp)))
;;              (equal
;;               (f2 (sum (sum-list (rp-evlt result a)) rest))
;;               (sum (-- (sum-list (rp-evlt coughed a)))
;;                    (f2 (sum (sum-list (rp-evlt pp a))
;;                             rest))))))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :use ((:instance c/d-fix-arg-aux-correct-for-f2
;;                             (neg-flag nil)
;;                             (pp-lst (cdr pp))
;;                             (limit (expt 2 30))))
;;            :in-theory (e/d (c/d-fix-s-args)
;;                            (c/d-fix-arg-aux-correct-for-f2)))))

;; (defthm c/d-fix-s-args-correct-for-d2
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state)
;;                 (rp-termp pp))
;;            (b* (((mv coughed result)
;;                  (c/d-fix-s-args pp)))
;;              (equal
;;               (d2 (sum (sum-list (rp-evlt result a)) rest))
;;               (sum (-- (sum-list (rp-evlt coughed a)))
;;                    (d2 (sum (sum-list (rp-evlt pp a))
;;                             rest))))))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :use ((:instance c/d-fix-arg-aux-correct-for-d2
;;                             (neg-flag nil)
;;                             (pp-lst (cdr pp))
;;                             (limit (expt 2 30))))
;;            :in-theory (e/d (c/d-fix-s-args)
;;                            (c/d-fix-arg-aux-correct-for-d2)))))

(defthm c/d-fix-arg-aux-valid-sc-subterms
  (implies (and (valid-sc-subterms pp-lst a)
                (rp-term-listp pp-lst))
           (b* (((mv coughed result)
                 (c/d-fix-arg-aux pp-lst neg-flag limit)))
             (and (valid-sc-subterms coughed a)
                  (valid-sc-subterms result a))))
  :hints (("Goal"
           :do-not-induct t
           :induct (c/d-fix-arg-aux pp-lst neg-flag limit)
           :in-theory (e/d (c/d-fix-arg-aux)
                           (nfix
                            ACL2::ZP-OPEN
                            zp
                            atom
                            (:DEFINITION VALID-SC)
                            (:DEFINITION QUOTEP)
                            rp-trans
                            rp-termp
                            rp-equal)))))

(defthm c/d-fix-pp-args-valid-sc
  (implies (and (valid-sc term a)
                (rp-termp term))
           (b* (((mv coughed result)
                 (c/d-fix-pp-args term limit)))
             (and (valid-sc coughed a)
                  (valid-sc result a))))
  :hints (("Goal"
           :in-theory (e/d (c/d-fix-pp-args
                            is-if is-rp) ()))))

(defthm c/d-fix-s-args-valid-sc
  (implies (and (valid-sc term a)
                (rp-termp term))
           (b* (((mv coughed result)
                 (c/d-fix-s-args term)))
             (and (valid-sc coughed a)
                  (valid-sc result a))))
  :hints (("Goal"
           :in-theory (e/d (c/d-fix-s-args
                            is-if is-rp) ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; create-c-instance, d-to-c and c/d-cough lemmas

(defthm create-c-instance-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (rp-evlt (create-c-instance s pp c/d) a)
                  (c (rp-evlt s a)
                     (rp-evlt pp a)
                     (rp-evlt c/d a))))
  :hints (("Goal"
           :in-theory (e/d (create-c-instance)
                           (rp-trans)))))

(defthm create-c-instance-correct-with-sk
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (rp-evlt-equiv (create-c-instance s pp c/d)
                          `(c ,s ,pp ,c/d)))
  :hints (("Goal"
           :in-theory (e/d ()
                           (rp-trans)))))

(defthm create-c-instance-valid-sc
  (implies (and (valid-sc s a)
                (valid-sc pp a)
                (valid-sc c/d a))
           (valid-sc (create-c-instance s pp c/d) a))
  :hints (("Goal"
           :in-theory (e/d (create-c-instance
                            is-rp
                            is-if) ()))))

(progn
  (create-regular-eval-lemma s 2 mult-formula-checks)
  (create-regular-eval-lemma evenpi 1 mult-formula-checks)
  (create-regular-eval-lemma c 3 mult-formula-checks)
  (create-regular-eval-lemma d 1 mult-formula-checks)
  (create-regular-eval-lemma d-sum 3 mult-formula-checks))

(defthm d-to-c-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (rp-evlt (d-to-c c/d) a)
                  (rp-evlt c/d a)))
  :hints (("Goal"
           :use ((:instance rp-evlt-of-rp-equal
                            (term1 (CADDR (CADDR (CADR C/D))))
                            (term2 (CADR (CADR (CADR (CADR (CADDR (CADR
                                                                   C/D))))))))
                 (:instance rp-evlt-of-rp-equal
                            (term1 (CADDDR (CADDR (CADR C/D))))
                            (term2 (CADDR (CADR (CADR (CADR (CADDR (CADR C/D)))))))))
           :in-theory (e/d (d-to-c
                            sum-comm-2-loop-stopper
                            sum-comm-1-loop-stopper
                            f2-to-d2)
                           (rp-evlt-of-rp-equal
                            (:DEFINITION RP-TERMP)
                            sum-comm-2
                            sum-comm-1
                            (:REWRITE RP-EVL-OF-RP-EQUAL2)
                            (:REWRITE RP-TERMP-OF-RP-TRANS)
                            (:DEFINITION RP-TERM-LISTP)
                            (:REWRITE IS-IF-RP-TERMP)
                            (:REWRITE IS-RP-PSEUDO-TERMP)
                            (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:DEFINITION ACL2::APPLY$-BADGEP)
                            (:DEFINITION FALIST-CONSISTENT)
                            d2-to-f2
                            rp-equal)))))

(defthm d-to-c-correct-with-sk
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (rp-evlt-equiv (d-to-c c/d) c/d)))

(defthm d-to-c-valid-sc
  (implies (valid-sc c/d a)
           (valid-sc (d-to-c c/d) a))
  :hints (("Goal"
           :in-theory (e/d (d-to-c
                            is-if
                            valid-sc is-rp)
                           ((:REWRITE CAR-OF-EX-FROM-RP-IS-NOT-RP)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:DEFINITION RP-TERM-LISTP)
                            (:DEFINITION RP-TERMP)
                            (:definition include-fnc))))))

(defthm c/d-cough-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp c/d))
           (b* (((mv s-coughed pp-coughed c/d-cleaned)
                 (c/d-cough c/d)))
             (and (equal (sum (sum-list (rp-evlt s-coughed a))
                              (sum-list (rp-evlt pp-coughed a))
                              (rp-evlt c/d-cleaned a))
                         (ifix (rp-evlt c/d a)))
                  (equal (sum (sum-list (rp-evlt s-coughed a))
                              (sum-list (rp-evlt pp-coughed a))
                              (rp-evlt c/d-cleaned a)
                              rest)
                         (sum (rp-evlt c/d a) rest))
                  (equal (sum rest
                              (sum-list (rp-evlt s-coughed a))
                              (sum-list (rp-evlt pp-coughed a))
                              (rp-evlt c/d-cleaned a))
                         (sum (rp-evlt c/d a) rest)))))
  ;; (equal (rp-evlt c/d-cleaned a)
  ;;        (sum (-- (sum-list (rp-evlt s-coughed a)))
  ;;             (-- (sum-list (rp-evlt pp-coughed a)))
  ;;             (rp-evlt c/d a)))
  :hints (("Goal"
           :in-theory (e/d (equal-sum-of-negated
                            f2-of-times2-reverse
                            d2-of-times2-reverse
                            c/d-cough
                            get-c/d-args)
                           (f2-of-times2
                            rp-termp
                            d2-of-times2)))))

(defthm c/d-cough-correct-with-sk
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp c/d))
           (b* (((mv s-coughed pp-coughed c/d-cleaned)
                 (c/d-cough c/d)))
             (and (rp-evlt-equiv `(binary-sum (sum-list ,s-coughed)
                                              (binary-sum (sum-list ,pp-coughed)
                                                          ,c/d-cleaned))
                                 `(ifix ,c/d))
                  (rp-evlt-equiv `(binary-sum
                                   (sum-list ,s-coughed)
                                   (binary-sum (sum-list ,pp-coughed)
                                               (binary-sum ,c/d-cleaned
                                                           ,rest)))
                                 `(binary-sum ,c/d ,rest))))))

(defthm CONTEXT-FROM-RP-opener
  (implies (is-rp (cons 'rp rest))
           (equal (context-from-rp (cons 'rp rest) context)
                  (LET ((TYPE (CAR (CDR (CAR rest))))
                        (X (CAR (CDR rest))))
                       (B* ((RCONTEXT (CONTEXT-FROM-RP X CONTEXT)))
                         (CONS (CONS TYPE (CONS (EX-FROM-RP X) 'NIL))
                               RCONTEXT)))))
  :hints (("Goal"
           :in-theory (e/d (context-from-rp) ()))))

(defthmd CONTEXT-FROM-RP-slow-opener-when-rp
  (implies (and (equal (car term) 'rp)
                (force (is-rp term)))
           (equal (context-from-rp term context)
                  (LET ((TYPE (CAR (CDR (CAR (CDR TERM)))))
                        (X (CAR (CDR (CDR TERM)))))
                       (B* ((RCONTEXT (CONTEXT-FROM-RP X CONTEXT)))
                         (CONS (CONS TYPE (CONS (EX-FROM-RP X) 'NIL))
                               RCONTEXT)))))
  :hints (("Goal"
           :in-theory (e/d (context-from-rp) ()))))

(defthm CONTEXT-FROM-RP-opener-when-not-rp
  (implies (not (equal fnc 'rp))
           (equal (context-from-rp (cons fnc rest) context)
                  context))
  :hints (("Goal"
           :in-theory (e/d (context-from-rp is-rp) ()))))

(defthm c/d-cough-valid-sc
  (implies (and (valid-sc c/d a)
                (rp-termp c/d)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (b* (((mv s-coughed pp-coughed c/d-cleaned)
                 (c/d-cough c/d)))
             (and (valid-sc s-coughed a)
                  (valid-sc pp-coughed a)
                  (valid-sc c/d-cleaned a))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance evenpi-lemma-1
                            (s1 (SUM-LIST (RP-EVL (RP-TRANS (CADR (CADDR (CADR C/D))))
                                                  A)))
                            (s2 (SUM-LIST (RP-EVL (RP-TRANS (CADDR (CADDR (CADR C/D))))
                                                  A)))
                            (b1 (SUM-LIST
                                 (RP-EVL (RP-TRANS (MV-NTH 1
                                                           (C/D-FIX-S-ARGS (CADR (CADDR (CADR C/D))))))
                                         A)))
                            (b2 (SUM-LIST
                                 (RP-EVL (RP-TRANS (MV-NTH 1
                                                           (C/D-FIX-PP-ARGS (CADDR (CADDR (CADR C/D)))
                                                                            1073741824)))
                                         A)))
                            (a (RP-EVL (RP-TRANS (CADDDR (CADDR (CADR C/D))))
                                       A))))
           :in-theory (e/d (c/d-cough
                            CONTEXT-FROM-RP-slow-opener-when-rp
                            get-c/d-args
                            is-if is-rp)
                           (rp-termp
                            (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                            (:DEFINITION RP-TERM-LISTP)
                            (:REWRITE IS-IF-RP-TERMP)
                            (:REWRITE VALID-SC-CADR)
                            (:REWRITE DEFAULT-CDR)
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE VALID-SC-CADDDR)
                            (:DEFINITION FALIST-CONSISTENT)
                            (:REWRITE CAR-OF-EX-FROM-RP-IS-NOT-RP)
                            evenpi-lemma-1
                            rp-termp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; can-c-merge-fast lemmas

;; (defthm m2-of-negated-subterm-dummy-lemma1
;;   (equal (m2 (sum a b c d e (-- (m2 (sum c e)))))
;;          (m2 (sum a b d)))
;;   :hints (("Goal"
;;            :use ((:instance m2-of---
;;                             (x (m2 (sum c e)))
;;                             (rest1 0)
;;                             (rest (sum a b c d e)))
;;                  (:instance m2-of---
;;                             (x (M2 (SUM C E)))
;;                             (rest1 0)
;;                             (rest (sum c d e)))
;;                  (:instance m2-of-times2
;;                             (a e)
;;                             (b (SUM A B (TIMES2 C) D)))
;;                  (:instance m2-of-times2
;;                             (a c)
;;                             (b (SUM A B D)))
;;                  (:instance M2-OF-M2
;;                             (x (sum c e))
;;                             (y (sum a b c d e))))
;;            :in-theory (e/d (sum-of-repeated-to-times2)
;;                            (m2-of---
;;                             m2-of-times2
;;                             S-OF-S-LEMMA1
;;                             M2-OF-M2
;;                             S-OF-MINUS
;;                             S-FIX-PP-ARGS-AUX-CORRECT-DUMMY-LEMMA1)))))

;; (defthm m2-of-negated-subterm-dummy-lemma2
;;   (equal (m2 (sum a b c d e (-- (m2 (sum b d)))))
;;          (m2 (sum a c e)))
;;   :hints (("Goal"
;;            :use ((:instance m2-of---
;;                             (x (m2 (sum b d)))
;;                             (rest1 0)
;;                             (rest (sum a b c d e)))
;;                  (:instance m2-of---
;;                             (x (M2 (SUM b d)))
;;                             (rest1 0)
;;                             (rest (sum c d e)))
;;                  (:instance m2-of-times2
;;                             (a d)
;;                             (b (SUM A c (TIMES2 b) e)))
;;                  (:instance m2-of-times2
;;                             (a b)
;;                             (b (SUM A c e)))
;;                  (:instance M2-OF-M2
;;                             (x (sum b d))
;;                             (y (sum a b c d e))))
;;            :in-theory (e/d (sum-of-repeated-to-times2)
;;                            (m2-of---
;;                             m2-of-times2
;;                             S-OF-S-LEMMA1
;;                             M2-OF-M2
;;                             S-OF-MINUS
;;                             S-FIX-PP-ARGS-AUX-CORRECT-DUMMY-LEMMA1)))))

(local
 (defthm cdr-of-rp-trans-lst
   (equal (cdr (rp-trans-lst x))
          (rp-trans-lst (cdr x)))
   :hints (("Goal"
            :expand (rp-trans-lst x)
            :in-theory (e/d () ())))))

(encapsulate
  nil

  (local
   (defthmd can-c-merge-fast-correct-lemma-1
     (implies (and (syntaxp (or (equal x '(CAr (cDR (CAr (cDR C/D1)))))
                                (equal x '(CAr (cDR (CAr (cDR C/D2))))))))
              (equal (rp-evlt x a)
                     (rp-evlt (ex-from-rp x) a)))))

  ;; (defthmd can-c-merge-fast-aux-correct-lemma
  ;;   (implies (and (can-c-merge-fast-aux s-lst pp c/d)
  ;;                 (rp-evl-meta-extract-global-facts :state state)
  ;;                 (mult-formula-checks state))
  ;;            (equal (sum (rp-evlt `(c nil ,pp ,c/d) a)
  ;;                                 (rp-evlt `(c (list . ,s-lst) ,pp2 ,c/d2)))
  ;;                   (f2 (sum

  (defthmd can-c-merge-fast-correct-lemma
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (rp-termp c/d1)
                  (rp-termp c/d2))
             (b* ((result (can-c-merge-fast c/d1 c/d2))
                  ((mv s-arg1 pp-arg1 c/d-arg1 ?type1) (get-c/d-args c/d1))
                  ((mv s-arg2 pp-arg2 c/d-arg2 ?type2) (get-c/d-args c/d2)))
               (implies result
                        (equal (sum (rp-evlt c/d1 a) (rp-evlt c/d2 a))
                               (if (equal result 0)
                                   (f2 (sum #|(-- (m2 (sum (sum-list (rp-evlt pp-arg1 a))
                                        (rp-evlt c/d-arg1 a))))||#
                                        (sum-list (rp-evlt pp-arg1 a))
                                        (rp-evlt c/d-arg1 a)
                                        (sum-list (rp-evlt `(list . ,(cddr s-arg2)) a))
                                        (sum-list (rp-evlt pp-arg2 a))
                                        (rp-evlt c/d-arg2 a)))
                                 (f2 (sum #|(-- (m2 (sum (sum-list (rp-evlt pp-arg2 a))
                                      (rp-evlt c/d-arg2 a))))||#
                                      (sum-list (rp-evlt pp-arg2 a))
                                      (rp-evlt c/d-arg1 a)
                                      (sum-list (rp-evlt `(list . ,(cddr s-arg1)) a))
                                      (sum-list (rp-evlt pp-arg1 a))
                                      (rp-evlt c/d-arg2 a))))))))
;:otf-flg t
    :hints (("Goal"
             :expand ((:free (x) (nth 3 x)))
             :in-theory (e/d* (get-c/d-args
                               can-c-merge-fast-correct-lemma-1
                               (:REWRITE REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS)
                               (:REWRITE
                                REGULAR-RP-EVL-OF_S_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                               can-c-merge-fast
                               ;;regular-eval-lemmas
                               can-c-merge-fast-aux
                               f2-to-d2)
                              (d2-to-f2
                               rp-termp
                               D2-OF-MINUS
                               (:DEFINITION EX-FROM-RP)
                               (:REWRITE DEFAULT-CDR)
                               (:DEFINITION INCLUDE-FNC)
                               rp-trans
                               RP-EVLT-OF-EX-FROM-RP))))))

(defthm sum-of-swap-c/ds
  (b* (((mv c/d1-new c/d2-new) (swap-c/ds c/d1 c/d2 cond)))
    (equal (sum (rp-evlt c/d1-new a) (rp-evlt c/d2-new a))
           (sum (rp-evlt c/d1 a) (rp-evlt c/d2 a))))
  :hints (("Goal"
           :in-theory (e/d (swap-c/ds) ()))))

(defthm swap-c/ds-valid-sc
  (implies (and (valid-sc c/d1 a)
                (valid-sc c/d2 a))
           (b* (((mv c/d1-new c/d2-new) (swap-c/ds c/d1 c/d2 cond)))
             (and (valid-sc c/d1-new a)
                  (valid-sc c/d2-new a))))
  :hints (("Goal"
           :in-theory (e/d (swap-c/ds) ()))))

(defthm can-c-merge-fast-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp c/d1)
                (rp-termp c/d2))
           (b* ((result (can-c-merge-fast c/d1 c/d2))
                ((mv c/d-orig1 c/d-orig2) (mv c/d1 c/d2))
                ((mv c/d1 c/d2)
                 (swap-c/ds c/d1 c/d2 (equal result 1)))
                ((mv ?s-arg1 pp-arg1 c/d-arg1 ?type1) (get-c/d-args c/d1))
                ((mv s-arg2 pp-arg2 c/d-arg2 ?type2) (get-c/d-args c/d2)))
             (implies result
                      (equal (sum (rp-evlt c/d-orig1 a) (rp-evlt c/d-orig2 a))
                             (f2 (sum (sum-list (rp-evlt pp-arg1 a))
                                      (rp-evlt c/d-arg1 a)
                                      (sum-list (rp-evlt `(list . ,(cddr s-arg2)) a))
                                      (sum-list (rp-evlt pp-arg2 a))
                                      (rp-evlt c/d-arg2 a)))))))
  :hints (("Goal"
           :use ((:instance can-c-merge-fast-correct-lemma))
           :in-theory (e/d (swap-c/ds)
                           (rp-termp
                            rp-trans)))))

(defthm can-c-merge-fast-correct-with-sk
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp c/d1)
                (rp-termp c/d2))
           (b* ((result (can-c-merge-fast c/d1 c/d2))
                ((mv c/d-orig1 c/d-orig2) (mv c/d1 c/d2))
                ((mv c/d1 c/d2)
                 (swap-c/ds c/d1 c/d2 (equal result 1)))
                ((mv ?s-arg1 pp-arg1 c/d-arg1 ?type1) (get-c/d-args c/d1))
                ((mv s-arg2 pp-arg2 c/d-arg2 ?type2) (get-c/d-args c/d2)))
             (implies result
                      (rp-evlt-equiv `(binary-sum ,c/d-orig1 ,c/d-orig2)
                                     `(f2 (binary-sum
                                           (sum-list ,pp-arg1)
                                           (binary-sum
                                            ,c/d-arg1
                                            (binary-sum
                                             (sum-list ,(cons 'list  (cddr s-arg2)))
                                             (binary-sum
                                              (sum-list ,pp-arg2)
                                              ,c/d-arg2)))))))))
  :hints (("Goal"
           :use ((:instance can-c-merge-fast-correct
                            (a (rp-evlt-equiv-witness
                                (list 'binary-sum c/d1 c/d2)
                                (list
                                 'f2
                                 (list
                                  'binary-sum
                                  (list
                                   'sum-list
                                   (mv-nth 1
                                           (get-c/d-args
                                            (mv-nth 0
                                                    (swap-c/ds c/d1 c/d2
                                                               (equal (can-c-merge-fast c/d1 c/d2)
                                                                      1))))))
                                  (list
                                   'binary-sum
                                   (mv-nth 2
                                           (get-c/d-args
                                            (mv-nth 0
                                                    (swap-c/ds c/d1 c/d2
                                                               (equal (can-c-merge-fast c/d1 c/d2)
                                                                      1)))))
                                   (list
                                    'binary-sum
                                    (list
                                     'sum-list
                                     (cons
                                      'list
                                      (cddr
                                       (mv-nth
                                        0
                                        (get-c/d-args
                                         (mv-nth 1
                                                 (swap-c/ds c/d1 c/d2
                                                            (equal (can-c-merge-fast c/d1 c/d2)
                                                                   1))))))))
                                    (list
                                     'binary-sum
                                     (list
                                      'sum-list
                                      (mv-nth
                                       1
                                       (get-c/d-args
                                        (mv-nth 1
                                                (swap-c/ds c/d1 c/d2
                                                           (equal (can-c-merge-fast c/d1 c/d2)
                                                                  1))))))
                                     (mv-nth
                                      2
                                      (get-c/d-args
                                       (mv-nth 1
                                               (swap-c/ds c/d1 c/d2
                                                          (equal (can-c-merge-fast c/d1 c/d2)
                                                                 1))))))))))))))
           :in-theory (e/d ()
                           (rp-termp
                            rp-trans)))))

(define swapped-1 (c/d1 c/d2)
  (b* ((cond (EQUAL (CAN-C-MERGE-FAST (EX-FROM-RP C/D1)
                                      (EX-FROM-RP C/D2))
                    1))
       ((mv a &)
        (SWAP-C/DS (EX-FROM-RP C/D1)
                   (EX-FROM-RP C/D2)
                   cond)))
    a)
  ///
  (defthm to-swapped-1
    (and (equal (MV-NTH 0
                        (SWAP-C/DS (EX-FROM-RP C/D1)
                                   (EX-FROM-RP C/D2)
                                   (EQUAL (CAN-C-MERGE-FAST (EX-FROM-RP C/D1)
                                                            (EX-FROM-RP C/D2))
                                          1)))
                (swapped-1 c/d1 c/d2))
         (implies (not (CAN-C-MERGE-FAST (EX-FROM-RP C/D1)
                                         (EX-FROM-RP C/D2)))
                  (equal (MV-NTH 0
                                 (SWAP-C/DS (EX-FROM-RP C/D1)
                                            (EX-FROM-RP C/D2)
                                            nil))
                         (swapped-1 c/d1 c/d2))))))

(define swapped-2 (c/d1 c/d2)
  (b* ((cond (EQUAL (CAN-C-MERGE-FAST (EX-FROM-RP C/D1)
                                      (EX-FROM-RP C/D2))
                    1))
       ((mv & A)
        (SWAP-C/DS (EX-FROM-RP C/D1)
                   (EX-FROM-RP C/D2)
                   cond)))
    a)
  ///
  (defthm to-swapped-2
    (and (equal (MV-NTH 1
                        (SWAP-C/DS (EX-FROM-RP C/D1)
                                   (EX-FROM-RP C/D2)
                                   (EQUAL (CAN-C-MERGE-FAST (EX-FROM-RP C/D1)
                                                            (EX-FROM-RP C/D2))
                                          1)))
                (swapped-2 c/d1 c/d2))
         (implies (not (CAN-C-MERGE-FAST (EX-FROM-RP C/D1)
                                         (EX-FROM-RP C/D2)))
                  (equal (MV-NTH 1
                                 (SWAP-C/DS (EX-FROM-RP C/D1)
                                            (EX-FROM-RP C/D2)
                                            nil))
                         (swapped-2 c/d1 c/d2))))))

(defthm sum-of-swap-c/ds-for-swapped-fncs
  (and (equal (sum (rp-evlt (swapped-1 c/d1 c/d2) a)
                   (rp-evlt (swapped-2 c/d1 c/d2) a))
              (sum (rp-evlt c/d1 a) (rp-evlt c/d2 a)))
       (equal (sum (rp-evlt (swapped-2 c/d1 c/d2) a)
                   (rp-evlt (swapped-1 c/d1 c/d2) a))
              (sum (rp-evlt c/d1 a) (rp-evlt c/d2 a))))
  :hints (("Goal"
           :use ((:instance sum-of-swap-c/ds
                            (c/d1 (ex-from-rp c/d1))
                            (cond (EQUAL (CAN-C-MERGE-FAST (EX-FROM-RP C/D1)
                                                           (EX-FROM-RP C/D2))
                                         1))
                            (c/d2 (ex-from-rp c/d2))))
           :in-theory (e/d ( swapped-1
                             swapped-2)
                           (sum-of-swap-c/ds
                            to-swapped-1
                            to-swapped-2)))))

(defthm swapped-fncs-valid-sc
  (implies (and (valid-sc c/d1 a)
                (valid-sc c/d2 a))
           (and (valid-sc (swapped-1 c/d1 c/d2) a)
                (valid-sc (swapped-2 c/d1 c/d2) a)))
  :hints (("Goal"
           :use ((:instance swap-c/ds-valid-sc
                            (c/d1 (ex-from-rp c/d1))
                            (cond (EQUAL (CAN-C-MERGE-FAST (EX-FROM-RP C/D1)
                                                           (EX-FROM-RP C/D2))
                                         1))
                            (c/d2 (ex-from-rp c/d2))))
           :in-theory (e/d (swapped-1
                            swapped-2)
                           (swap-c/ds-valid-sc
                            to-swapped-1
                            to-swapped-2)))))

(defthm can-c-merge-fast-correct-for-swapped-fncs
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp c/d1)
                (rp-termp c/d2))
           (b* ((result (can-c-merge-fast (ex-from-rp c/d1)
                                          (ex-from-rp c/d2)))
                ((mv c/d-orig1 c/d-orig2) (mv c/d1 c/d2))

                ((mv c/d1 c/d2)
                 (mv (swapped-1 c/d1 c/d2 )
                     (swapped-2 c/d1 c/d2 )))

                ((mv ?s-arg1 pp-arg1 c/d-arg1 ?type1) (get-c/d-args c/d1))
                ((mv s-arg2 pp-arg2 c/d-arg2 ?type2) (get-c/d-args c/d2)))
             (implies result
                      (and (equal (sum (rp-evlt c/d-orig1 a) (rp-evlt c/d-orig2 a))
                                  (f2 (sum (sum-list (rp-evlt pp-arg1 a))
                                           (rp-evlt c/d-arg1 a)
                                           (sum-list (rp-evlt `(list . ,(cddr s-arg2)) a))
                                           (sum-list (rp-evlt pp-arg2 a))
                                           (rp-evlt c/d-arg2 a))))
                           (equal (sum (rp-evlt c/d-orig1 a)
                                       (rp-evlt c/d-orig2 a)
                                       other)
                                  (sum (f2 (sum (sum-list (rp-evlt pp-arg1 a))
                                                (rp-evlt c/d-arg1 a)
                                                (sum-list (rp-evlt `(list . ,(cddr s-arg2)) a))
                                                (sum-list (rp-evlt pp-arg2 a))
                                                (rp-evlt c/d-arg2 a)))
                                       other))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance can-c-merge-fast-correct
                            (c/d1 (ex-from-rp c/d1))
                            (c/d2 (ex-from-rp c/d2))))
           :in-theory (e/d (to-swapped-1
                            to-swapped-2)
                           (rp-termp
                            ex-from-rp
                            can-c-merge-fast-correct
                            rp-trans
                            )))))

(defthm rp-termp-of-swapped-fncs
  (implies (and (rp-termp c/d1)
                (rp-termp c/d2))
           (and (rp-termp (swapped-1 c/d1 c/d2 ))
                (rp-termp (swapped-2 c/d1 c/d2 ))))
  :hints (("Goal"

           :in-theory (e/d (swapped-1
                            swapped-2)
                           (to-swapped-2
                            to-swapped-1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; c/d-merge lemmas

(defthmd sum-of-swap-c/ds-reverse
  (implies (syntaxp (and (equal c/d1 'c/d1)
                         (equal c/d2 'c/d2)))
           (equal
            (sum (rp-evlt c/d1 a) (rp-evlt c/d2 a))
            (sum (rp-evlt (MV-NTH 0
                                  (SWAP-C/DS (EX-FROM-RP C/D1)
                                             (EX-FROM-RP C/D2)
                                             (EQUAL (CAN-C-MERGE-FAST (EX-FROM-RP C/D1)
                                                                      (EX-FROM-RP C/D2))
                                                    1)))
                          a)
                 (rp-evlt (MV-NTH 1
                                  (SWAP-C/DS (EX-FROM-RP C/D1)
                                             (EX-FROM-RP C/D2)
                                             (EQUAL (CAN-C-MERGE-FAST (EX-FROM-RP C/D1)
                                                                      (EX-FROM-RP C/D2))
                                                    1)))
                          a))))
  :hints (("Goal"
           :in-theory (e/d (sum-of-swap-c/ds) ()))))

(local
 (defthm is-if-lemma
   (implies (or (atom x)
                (not (equal (car x) 'if)))
            (not (is-if x)))
   :hints (("Goal"
            :in-theory (e/d (is-if) ())))))

(local
 (defthm is-rp-lemma
   (implies (or (atom x)
                (not (equal (car x) 'rp)))
            (not (is-rp x)))
   :hints (("Goal"
            :in-theory (e/d (is-rp) ())))))

(local
 (defthm is-falist-lemma
   (implies (or (atom x)
                (not (equal (car x) 'falist)))
            (not (is-falist x)))
   :hints (("Goal"
            :in-theory (e/d (is-falist) ())))))

(local
 (in-theory (disable falist-consistent)))

;; (include-book "misc/untranslate-patterns" :dir :system)

;; (acl2::add-untranslate-pattern-function (swapped-1 c/d1 c/d2)
;;                                         swapped-1)

;; (acl2::add-untranslate-pattern-function (swapped-2 c/d1 c/d2)
;;                                         swapped-2)

(defthm sum-list-of-negated-m2
  (equal (sum-list (list (-- (m2 x))))
         (-- (m2 x)))
  :hints (("Goal"
           :in-theory (e/d (sum-list) ()))))

(defthm rid-of-get-extra-s-arg
  (implies (EQUAL
            (RP-EVL (RP-TRANS (GET-EXTRA-S-ARG cadr caddr cadddr limit))
                    A)
            (LIST (-- (M2 (SUM (SUM-LIST (RP-EVL (RP-TRANS cadr)
                                                 A))
                               (SUM-LIST (RP-EVL (RP-TRANS caddr)
                                                 A))
                               (RP-EVL (RP-TRANS cadddr)
                                       A))))))
           (equal (SUM-LIST (RP-EVL (RP-TRANS (GET-EXTRA-S-ARG cadr caddr cadddr limit))
                                    A))
                  (-- (M2 (SUM (SUM-LIST (RP-EVL (RP-TRANS cadr)
                                                 A))
                               (SUM-LIST (RP-EVL (RP-TRANS caddr)
                                                 A))
                               (RP-EVL (RP-TRANS cadddr)
                                       A)))))))

(defthm rid-of-c/d-merge-sum
  (implies (EQUAL
            (SUM (SUM-LIST (RP-EVL (RP-TRANS (MV-NTH 0
                                                     (C/D-MERGE param1
                                                                param2
                                                                flg limit)))
                                   A))
                 (SUM-LIST (RP-EVL (RP-TRANS (MV-NTH 1
                                                     (C/D-MERGE param1
                                                                param2
                                                                flg limit)))
                                   A))
                 (RP-EVL (RP-TRANS (MV-NTH 2
                                           (C/D-MERGE param1
                                                      param2
                                                      flg limit)))
                         A))
            (SUM (RP-EVL (RP-TRANS param1)
                         A)
                 (RP-EVL (RP-TRANS param2)
                         A)))
           (equal
            (sum (SUM-LIST (RP-EVL (RP-TRANS (MV-NTH 0
                                                     (C/D-MERGE param1
                                                                param2
                                                                flg limit)))
                                   A))
                 (SUM-LIST (RP-EVL (RP-TRANS (MV-NTH 1
                                                     (C/D-MERGE param1
                                                                param2
                                                                flg limit)))
                                   A))
                 (RP-EVL (RP-TRANS (MV-NTH 2
                                           (C/D-MERGE param1
                                                      param2
                                                      flg limit)))
                         A)
                 other)
            (SUM (RP-EVL (RP-TRANS param1)
                         A)
                 (RP-EVL (RP-TRANS param2)
                         A)
                 other)))
  :hints (("Goal"
           :in-theory (e/d (sum-comm-1-loop-stopper
                            sum-comm-2-loop-stopper)
                           (sum-comm-1
                            sum-comm-2)))))

(defthm rid-of-c/d-merge-sum-2
  (implies (EQUAL
            (SUM
             (SUM-LIST (RP-EVL (RP-TRANS (MV-NTH 1
                                                 (C/D-MERGE param1
                                                            param2
                                                            flg limit)))
                               A))
             (RP-EVL (RP-TRANS (MV-NTH 2
                                       (C/D-MERGE param1
                                                  param2
                                                  flg limit)))
                     A))
            (SUM (RP-EVL (RP-TRANS param1)
                         A)
                 (RP-EVL (RP-TRANS param2)
                         A)))
           (equal
            (sum
             (SUM-LIST (RP-EVL (RP-TRANS (MV-NTH 1
                                                 (C/D-MERGE param1
                                                            param2
                                                            flg limit)))
                               A))
             (RP-EVL (RP-TRANS (MV-NTH 2
                                       (C/D-MERGE param1
                                                  param2
                                                  flg limit)))
                     A)
             other)
            (SUM (RP-EVL (RP-TRANS param1)
                         A)
                 (RP-EVL (RP-TRANS param2)
                         A)
                 other)))
  :hints (("Goal"
           :in-theory (e/d (sum-comm-1-loop-stopper
                            sum-comm-2-loop-stopper)
                           (sum-comm-1
                            sum-comm-2)))))

(defthm valid-sc-lemma1
  (implies (and (valid-sc term a)
                (case-match term (('d ('rp ''evenpi ('d-sum & & &))) t)))
           (and (VALID-SC (CADDDR (CADDR (CADR term))) A)
                (VALID-SC (CADR (CADDR (CADR term))) A)
                (VALID-SC (CADDR (CADDR (CADR term))) A)
                (VALID-SC (CADR TERM) A)))
  :hints (("Goal"
           :do-not-induct t
           :expand ((EVAL-AND-ALL (CONTEXT-FROM-RP (CADR TERM) NIL)
                                  A)
                    (CONTEXT-FROM-RP (CADR TERM) NIL)
                    (valid-sc term a)
                    (VALID-SC (CADR TERM) A)
                    (VALID-SC (CADR TERM) A)
                    (VALID-SC-SUBTERMS (CDR TERM) A))
           :in-theory (e/d (is-if is-rp
                                  valid-sc-subterms
                                  valid-sc)
                           (is-if-lemma
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE CAR-OF-EX-FROM-RP-IS-NOT-RP)
                            (:DEFINITION RP-TERMP)
                            is-rp-lemma)))))

(defthm valid-sc-lemma2
  (implies (and (valid-sc term a)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (case-match term (('d ('rp ''evenpi ('d-sum & & &))) t)))
           (and (evenpi (rp-evlt (CADDR (CADR term)) a))
                (evenpi (rp-evlt (CADR term) a))
                (evenpi (SUM (SUM-LIST (RP-EVL (RP-TRANS (CADR (CADDR (CADR term))))
                                               A))
                             (SUM-LIST (RP-EVL (RP-TRANS (CADDR (CADDR (CADR term))))
                                               A))
                             (RP-EVL (RP-TRANS (CADDDR (CADDR (CADR term))))
                                     A)))
                (evenpi (SUM (SUM-LIST (RP-EVL (RP-TRANS (CADDR (CADDR (CADR term))))
                                               A))
                             (RP-EVL (RP-TRANS (CADDDR (CADDR (CADR term))))
                                     A)
                             (SUM-LIST (RP-EVL (RP-TRANS (CADR (CADDR (CADR term))))
                                               A))
                             ))))
  :hints (("Goal"
           :do-not-induct t
           :expand ((EVAL-AND-ALL (CONTEXT-FROM-RP (CADR TERM) NIL)
                                  A)
                    (CONTEXT-FROM-RP (CADR TERM) NIL)
                    (valid-sc term a)
                    (VALID-SC (CADR TERM) A)
                    (VALID-SC-SUBTERMS (CDR TERM) A))
           :in-theory (e/d (is-if is-rp)
                           (is-if-lemma
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE CAR-OF-EX-FROM-RP-IS-NOT-RP)
                            (:DEFINITION RP-TERMP)
                            is-rp-lemma)))))

(defthm dummy-lemma1
  (implies (case-match term (('rp & &) t))
           (equal (RP-EVL (RP-TRANS term) A)
                  (RP-EVL (RP-TRANS (caddr term)) A))))

(defthmd can-c-merge-fast-and-consp
  (implies
   (can-c-merge-fast c/d1 c/d2)
   (and (consp
         (mv-nth
          0
          (get-c/d-args
           (mv-nth 1
                   (swap-c/ds c/d1 c/d2
                              (equal (can-c-merge-fast c/d1 c/d2)
                                     1))))))
        (consp
         (cdr (mv-nth
               0
               (get-c/d-args
                (mv-nth 1
                        (swap-c/ds c/d1 c/d2
                                   (equal (can-c-merge-fast c/d1 c/d2)
                                          1)))))))
        (equal (car (mv-nth
                     0
                     (get-c/d-args
                      (mv-nth 1
                              (swap-c/ds c/d1 c/d2
                                         (equal (can-c-merge-fast c/d1 c/d2)
                                                1))))))
               'list)))
  :hints (("goal"
           :in-theory (e/d (can-c-merge-fast
                            can-c-merge-fast-aux
                            get-c/d-args
                            swap-c/ds) ()))))

(local
 (defthm dummy-lemma2
   (implies (and (can-c-merge-fast (ex-from-rp c/d1) (ex-from-rp c/d2))
                 (equal (car (swapped-2 c/d1 c/d2)) 'c))
            (and (consp (cadr (swapped-2 c/d1 c/d2)))
                 (consp (cdr (cadr (swapped-2 c/d1 c/d2))))
                 (equal (car (cadr (swapped-2 c/d1 c/d2))) 'list)))
   :hints (("goal"
            :use ((:instance can-c-merge-fast-and-consp
                             (c/d1 (ex-from-rp c/d1))
                             (c/d2 (ex-from-rp c/d2))))
            :in-theory (e/d (get-c/d-args)
                            ())))))

(local
 (defthm valid-sc-dummy-lemma
   (implies (and (valid-sc term a)
                 (consp (cdr term))
                 (consp term)
                 (equal (car term) 'list))
            (VALID-SC-SUBTERMS (CDDR term) A))
   :hints (("Goal"
            :expand (valid-sc term a)
            :in-theory (e/d (is-if is-rp) ())))))

(local
 (defthm rp-termp-dummy-lemma
   (implies (and (rp-termp term)
                 (consp (cdr term))
                 (consp term)
                 (equal (car term) 'list))
            (rp-term-listp (CDDR term)))
   :hints (("Goal"
            :expand ((rp-termp term)
                     (RP-TERM-LISTP (CDR TERM)))
            :in-theory (e/d (is-if is-rp is-falist) ())))))

(defthm REMOVE-S-FROM-FOR-FAST-MERGE-valid-sc
  (implies (and (can-c-merge-fast (ex-from-rp c/d1) (ex-from-rp c/d2))
                (valid-sc c/d1 a)
                (valid-sc c/d2 a))
           (valid-sc (REMOVE-S-FROM-FOR-FAST-MERGE
                      (CADR (SWAPPED-2 C/D1 C/D2)) x y)
                     a))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (REMOVE-S-FROM-FOR-FAST-MERGE
                            SWAP-C/DS
                            GET-C/D-ARGS
                            CAN-C-MERGE-FAST-AUX
                            CAN-C-MERGE-FAST
                            SWAPPED-2)
                           (to-SWAPPED-2
                            (:DEFINITION EVAL-AND-ALL)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC-LST)
                            rp-termp
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:DEFINITION ACL2::APPLY$-BADGEP)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                            (:DEFINITION SUBSETP-EQUAL)
                            (:DEFINITION MEMBER-EQUAL)
                            (:DEFINITION VALID-SC-SUBTERMS)
                            (:REWRITE VALID-SC-LEMMA1)
                            (:REWRITE
                             ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                            (:DEFINITION EX-FROM-RP)
                            (:DEFINITION RP-TERMP)
                            (:REWRITE EX-FROM-RP-LOOSE-IS-EX-FROM-RP)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE IS-IF-RP-TERMP)
                            (:REWRITE DEFAULT-CAR)
                            (:REWRITE NOT-INCLUDE-RP)
                            (:TYPE-PRESCRIPTION RP-TERMP))))))

(defthm REMOVE-S-FROM-FOR-FAST-MERGE-rp-termp
  (implies (and (can-c-merge-fast (ex-from-rp c/d1) (ex-from-rp c/d2))
                (rp-termp c/d1)
                (rp-termp c/d2))
           (rp-termp (REMOVE-S-FROM-FOR-FAST-MERGE
                      (CADR (SWAPPED-2 C/D1 C/D2)) x y)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (REMOVE-S-FROM-FOR-FAST-MERGE
                            SWAP-C/DS
                            GET-C/D-ARGS
                            CAN-C-MERGE-FAST-AUX
                            CAN-C-MERGE-FAST
                            SWAPPED-2)
                           (to-SWAPPED-2
                            (:DEFINITION RP-TERM-LISTP)
                            (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                            (:DEFINITION ACL2::APPLY$-BADGEP)
                            (:DEFINITION SUBSETP-EQUAL)
                            (:DEFINITION MEMBER-EQUAL)
                            (:DEFINITION EX-FROM-RP)
                            (:REWRITE
                             ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 2)
                            (:REWRITE NOT-INCLUDE-RP)
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE DEFAULT-CAR)
                            (:REWRITE IS-RP-LEMMA)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS)
                            (:DEFINITION ATOM)
                            (:TYPE-PRESCRIPTION IS-RP$INLINE))))))

#|(skip-proofs
 (defthm REMOVE-S-FROM-FOR-FAST-MERGE-redef
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state)
                 (CAN-C-MERGE-FAST (EX-FROM-RP C/D1)
                                   (EX-FROM-RP C/D2)))
            (equal (sum-list
                    (RP-EVLt (remove-s-from-for-fast-merge (cadr (swapped-2 c/d1 c/d2))
                                                           (caddr (swapped-1 c/d1 c/d2))
                                                           (cadddr (swapped-1 c/d1 c/d2)))
                             a))
                   (sum-list (rp-evlt (s-sum-merge (cadr (swapped-2 c/d1 c/d2))
                                                   `(list (-- (s ,(caddr
                                                                   (swapped-1 c/d1 c/d2))
                                                                 ,(cadddr
                                                                   (swapped-1 c/d1 c/d2))))))
                                      a))))))||#

(defthm sum-of-SWAP-C/DS-when-one-is-zero
  (and (equal (SUM (RP-EVL (RP-TRANS (MV-NTH 0
                                             (SWAP-C/DS c/d1 ''0 cond)))
                           A)
                   (RP-EVL (RP-TRANS (MV-NTH 1
                                             (SWAP-C/DS c/d1 ''0 cond)))
                           A))
              (IFIX (RP-EVL (RP-TRANS C/D1) A)))
       (equal (SUM (RP-EVL (RP-TRANS (MV-NTH 0
                                             (SWAP-C/DS ''0 c/d1 cond)))
                           A)
                   (RP-EVL (RP-TRANS (MV-NTH 1
                                             (SWAP-C/DS ''0 c/d1 cond)))
                           A))
              (IFIX (RP-EVL (RP-TRANS C/D1) A))))
  :hints (("Goal"
           :in-theory (e/d (SWAP-C/DS) ()))))

(defthm rp-evlt-when-quotep
  (implies (and (consp x)
                (consp (cdr x))
                (equal (car x) 'quote))
           (equal (rp-evlt x a)
                  (unquote x)))
  :hints (("Goal"
           :in-theory (e/d (rp-trans) ()))))

(defthm m2-of-ex-from-rp/--
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp term))
           (equal (M2 (SUM (RP-EVL (RP-TRANS (EX-FROM-RP/-- term))  A) rest))
                  (M2 (SUM (RP-EVL (RP-TRANS term)  A) rest))))
  :hints (("Goal"
           :do-not-induct t
           :induct (EX-FROM-RP/-- term)
           :in-theory (e/d (EX-FROM-RP/--) ()))))

(defthm ex-from-rp/--valid-sc
  (implies (valid-sc term a)
           (VALID-SC (EX-FROM-RP/-- term) A))
  :hints (("Goal"
           :induct (EX-FROM-RP/-- term)
           :in-theory (e/d (is-rp is-if
                                  EX-FROM-RP/--)
                           ()))))

(defthm m2-of-lemma1
  (implies (and (EQUAL (EX-FROM-RP/-- term) ''NIL)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp term))
           (equal (M2 (RP-EVL (RP-TRANS term) A))
                  0))
  :hints (("Goal"
           :use ((:instance m2-of-ex-from-rp/--
                            (rest 0)))
           :in-theory (e/d () (m2-of-ex-from-rp/--)))))

(defthm m2-of-lemma2
  (implies (and (equal (m2 (sum a b)) (m2 c))
                (equal (m2 (sum x y)) (m2 (sum k l m))))
           (equal (equal (m2 (sum a b x y))
                         (m2 (sum k l m c)))
                  t))
  :hints (("Goal"
           :use ((:instance m2-with-extra
                            (x (sum a b))
                            (y c)
                            (other (sum x y)))
                 (:instance m2-with-extra
                            (x (sum x y))
                            (y (sum k l m))))
           :in-theory (e/d () (m2-with-extra)))))

(defthm is-rp-evenpi
  (is-rp (list 'rp ''evenpi x))
  :hints (("Goal"
           :in-theory (e/d (is-rp) ()))))

(defthm sum-merge-aux-retains-evenpi-lemma
  (implies (equal (evenpi x) (evenpi (sum a b)))
           (equal (equal (evenpi (sum other x))
                         (evenpi (sum a b other)))
                  t))
  :hints (("Goal"
           :use ((:instance EVENPI-WITH-OTHER
                            (x x)
                            (y (sum a b))
                            (z other)))
           :in-theory (e/d ()
                           (EVENPI-WITH-OTHER)))))

(defthm sum-merge-aux-retains-evenpi
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-term-listp s-lst1)
                (rp-term-listp s-lst2))
           (equal (evenpi (sum-list-eval (s-sum-merge-aux s-lst1 s-lst2) a))
                  (evenpi (sum (sum-list-eval s-lst1 a)
                               (sum-list-eval s-lst2 a)))))
  :hints (("Goal"
           :induct (s-sum-merge-aux s-lst1 s-lst2)
           :do-not-induct t
           :in-theory (e/d (s-sum-merge-aux
                            sum-comm-1-loop-stopper
                            sum-comm-2-loop-stopper
                            sum-merge-aux-retains-evenpi-lemma
                            )
                           (sum-comm-2
                            sum-comm-1)))))

(defthm sum-merge-retains-evenpi
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp s1)
                (rp-termp s2))
           (equal (evenpi (sum-list (rp-evlt (s-sum-merge s1 s2) a)))
                  (evenpi (sum (sum-list (rp-evlt s1 a))
                               (sum-list (rp-evlt s2 a))))))
  :hints (("Goal"
           :use ((:instance s-sum-merge-aux-correct
                            (term1 (cdr s1))
                            (term2 (cdr s2))))
           :in-theory (e/d (s-sum-merge
                            sum-comm-1-loop-stopper
                            sum-comm-2-loop-stopper)
                           (SUM-MERGE-AUX-RETAINS-EVENPI
                            sum-comm-1
                            sum-comm-2)))))

(defthm pp-merge-retains-evenpi
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp s1)
                (rp-termp s2))
           (equal (evenpi (sum-list (rp-evlt (mv-nth 0 (pp-sum-merge s1 s2)) a)))
                  (evenpi (sum (sum-list (rp-evlt s1 a))
                               (sum-list (rp-evlt s2 a))))))
;:otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance pp-sum-merge-aux-correct
                            (term1 (cdr s1))
                            (cnt 0)
                            (term2 (cdr s2))))
           :in-theory (e/d (pp-sum-merge)
                           ()))))

(local
 (defthm rp-termp-of-d
   (iff (rp-termp `(d ,x))
        (rp-termp x))))

(local
 (defthm rp-termp-of---
   (iff (rp-termp `(-- ,x))
        (rp-termp x))))

(local
 (defthm rp-termp-of-list
   (iff (rp-termp `(list . ,x))
        (rp-term-listp x))))

(local
 (defthm rp-termp-of-d-sum
   (iff (rp-termp `(d-sum ,x ,y ,z))
        (and (rp-termp x)
             (rp-termp y)
             (rp-termp z)))))

(local
 (defthm rp-termp-of-of-rp-evenpi
   (iff (rp-termp `(rp 'evenpi ,x))
        (rp-termp x))
   :hints (("Goal"
            :in-theory (e/d (is-rp) ())))))

(defthm c/d-merge-slow-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp pp-arg1) (rp-termp pp-arg2)
                (rp-termp pp-coughed-from-arg)
                (rp-termp s-arg1) (rp-termp s-arg2)
                (rp-termp s-coughed-from-arg)
                (if c/d1-is-c (rp-termp extra-s-arg1) t)
                (if c/d2-is-c (rp-termp extra-s-arg2) t)
                (rp-termp c/d-arg))
           (b* (((mv s-coughed pp-coughed c/d-merged)
                 (c/d-merge-slow-aux pp-arg1 pp-arg2 pp-coughed-from-arg
                                     s-arg1 s-arg2 s-coughed-from-arg
                                     extra-s-arg1 extra-s-arg2
                                     c/d-arg clean-flg
                                     c/d1-is-c c/d2-is-c)))
             (equal (sum (sum-list  (rp-evlt s-coughed a))
                         (sum-list (rp-evlt pp-coughed a))
                         (rp-evlt c/d-merged a))
                    (d2 (sum (rp-evlt `(sum-list ,pp-arg1) a)
                             (rp-evlt `(sum-list ,pp-arg2) a)
                             (rp-evlt `(sum-list ,pp-coughed-from-arg) a)
                             (rp-evlt `(sum-list ,s-arg1) a)
                             (rp-evlt `(sum-list ,s-arg2) a)
                             (rp-evlt `(sum-list ,s-coughed-from-arg) a)
                             (if c/d1-is-c (rp-evlt `(sum-list ,extra-s-arg1) a) 0)
                             (if c/d2-is-c (rp-evlt `(sum-list ,extra-s-arg2) a) 0)
                             (rp-evlt c/d-arg a))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (c/d-merge-slow-aux
                            clean-c/d-args
                            d2-of-times2-reverse)
                           (d2-of-times2
                            (:TYPE-PRESCRIPTION RP-TERMP)
                            (:REWRITE DUMMY-SUM-CANCEL-LEMMA1)
                            (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                            (:TYPE-PRESCRIPTION IS-RP$INLINE)
                            (:TYPE-PRESCRIPTION FALIST-CONSISTENT)
                            falist-consistent
                            (:TYPE-PRESCRIPTION S-SUM-MERGE)
                            (:TYPE-PRESCRIPTION BINARY-SUM)
                            (:REWRITE DEFAULT-CAR)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:REWRITE DEFAULT-CDR)
                            (:DEFINITION IS-SYNP$INLINE)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_S_WHEN_MULT-FORMULA-CHECKS)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_EVENPI_WHEN_MULT-FORMULA-CHECKS)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_AND-LIST_WHEN_MULT-FORMULA-CHECKS)
                            rp-termp)))))

(defthm c/d-merge-slow-aux-valid-sc
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp pp-arg1) (rp-termp pp-arg2)
                (rp-termp pp-coughed-from-arg)
                (rp-termp s-arg1) (rp-termp s-arg2)
                (rp-termp s-coughed-from-arg)
                (if c/d1-is-c (rp-termp extra-s-arg1) t)
                (if c/d2-is-c (rp-termp extra-s-arg2) t)
                (rp-termp c/d-arg)

                (valid-sc pp-arg1 a) (valid-sc pp-arg2 a)
                (valid-sc pp-coughed-from-arg a)
                (valid-sc s-arg1 a) (valid-sc s-arg2 a)
                (valid-sc s-coughed-from-arg a)
                (valid-sc extra-s-arg1 a)
                (valid-sc extra-s-arg2 a)
                (valid-sc c/d-arg a))
           (b* (((mv s-coughed pp-coughed ?c/d-merged)
                 (c/d-merge-slow-aux pp-arg1 pp-arg2 pp-coughed-from-arg
                                     s-arg1 s-arg2 s-coughed-from-arg
                                     extra-s-arg1 extra-s-arg2
                                     c/d-arg clean-flg
                                     c/d1-is-c c/d2-is-c)))
             (and (valid-sc s-coughed a)
                  (valid-sc pp-coughed a)
                  )))
  :hints (("Goal"
           :do-not-induct t
           :expand ((VALID-SC ''NIL A))
           :in-theory (e/d (c/d-merge-slow-aux
                            clean-c/d-args
                            d2-of-times2-reverse)
                           (d2-of-times2

                            (:TYPE-PRESCRIPTION S-SUM-MERGE)

                            (:DEFINITION RP-TERMP)
                            (:REWRITE IS-IF-RP-TERMP)
                            (:DEFINITION VALID-SC)
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE VALID-SC-LEMMA1)
                            (:DEFINITION ACL2::APPLY$-BADGEP)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                            (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                            (:DEFINITION SUBSETP-EQUAL)
                            (:DEFINITION MEMBER-EQUAL)
                            (:DEFINITION TRUE-LISTP)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 2)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE
                             ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                            c/d-merge-slow-aux-correct)))))

(defthm c/d-merge-slow-aux-valid-sc-2
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp pp-arg1) (rp-termp pp-arg2)
                (rp-termp pp-coughed-from-arg)
                (rp-termp s-arg1) (rp-termp s-arg2)
                (rp-termp s-coughed-from-arg)
                (if c/d1-is-c (rp-termp extra-s-arg1) t)
                (if c/d2-is-c (rp-termp extra-s-arg2) t)
                (rp-termp c/d-arg)

                (valid-sc pp-arg1 a) (valid-sc pp-arg2 a)
                (valid-sc pp-coughed-from-arg a)
                (valid-sc s-arg1 a) (valid-sc s-arg2 a)
                (valid-sc s-coughed-from-arg a)
                (valid-sc extra-s-arg1 a)
                (valid-sc extra-s-arg2 a)
                (valid-sc c/d-arg a))
           (b* (((mv ?s-coughed ?pp-coughed c/d-merged)
                 (c/d-merge-slow-aux pp-arg1 pp-arg2 pp-coughed-from-arg
                                     s-arg1 s-arg2 s-coughed-from-arg
                                     extra-s-arg1 extra-s-arg2
                                     c/d-arg clean-flg
                                     c/d1-is-c c/d2-is-c)))
             (and (implies (evenpi (sum (rp-evlt `(sum-list ,pp-arg1) a)
                                        (rp-evlt `(sum-list ,pp-arg2) a)
                                        (rp-evlt `(sum-list ,pp-coughed-from-arg) a)
                                        (rp-evlt `(sum-list ,s-arg1) a)
                                        (rp-evlt `(sum-list ,s-arg2) a)
                                        (rp-evlt `(sum-list ,s-coughed-from-arg) a)
                                        (if c/d1-is-c (rp-evlt `(sum-list ,extra-s-arg1) a) 0)
                                        (if c/d2-is-c (rp-evlt `(sum-list ,extra-s-arg2) a) 0)
                                        (rp-evlt c/d-arg a)))
                           (valid-sc c/d-merged a))
                  )))
  :hints (("Goal"
           :do-not-induct t
           :expand ((:free (x) (valid-sc (cons 'd x) a))
                    (:free (x) (valid-sc (cons 'd-sum x) a))
                    (:free (x) (valid-sc (cons 'rp x) a)))
           :use ((:instance c/d-merge-slow-aux-correct)
                 (:instance c/d-fix-s-args-retains-evenpi-with-other
                            (other (sum  (RP-EVL (RP-TRANS C/D-ARG) A)
                                         (SUM-LIST (RP-EVL (RP-TRANS PP-ARG1) A))
                                         (SUM-LIST (RP-EVL (RP-TRANS PP-ARG2) A))
                                         (SUM-LIST (RP-EVL (RP-TRANS PP-COUGHED-FROM-ARG)
                                                           A))))
                            (pp (S-SUM-MERGE (S-SUM-MERGE S-ARG1
                                                          (S-SUM-MERGE S-ARG2 S-COUGHED-FROM-ARG))
                                             (S-SUM-MERGE EXTRA-S-ARG1 EXTRA-S-ARG2)))))
           :in-theory (e/d (c/d-merge-slow-aux
                            clean-c/d-args
                            d2-of-times2-reverse)
                           (d2-of-times2
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE DUMMY-SUM-CANCEL-LEMMA1)
                            (:TYPE-PRESCRIPTION S-SUM-MERGE)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:TYPE-PRESCRIPTION VALID-SC)
                            (:DEFINITION IS-SYNP$INLINE)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE DEFAULT-CAR)
                            (:REWRITE RP-TRANS-WHEN-LIST)
                            (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_S_WHEN_MULT-FORMULA-CHECKS)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_BIT-OF_WHEN_MULT-FORMULA-CHECKS)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_BINARY-APPEND_WHEN_MULT-FORMULA-CHECKS)
                            rp-termp
                            valid-sc
                            c/d-merge-slow-aux-correct)))))

(defthm sum-of-c-args-gives-evenpi
  (evenpi (sum (-- (m2 (sum a1 b1 c1)))
               (-- (m2 (sum a2 b2 c2)))
               a1 b1 c1 a2 b2 c2))
  :hints (("Goal"
           :use ((:instance evenpi-for-3-d2-arguments
                            (a a1)
                            (b b1)
                            (c c1))
                 (:instance evenpi-for-3-d2-arguments
                            (a a2)
                            (b b2)
                            (c c2))
                 (:instance evenpi-of-sum
                            (x (SUM A1 B1 C1 (-- (M2 (SUM A1 B1 C1)))))
                            (y (SUM A2 B2 C2 (-- (M2 (SUM A2 B2 C2)))))))
           :in-theory (e/d () (evenpi-for-3-d2-arguments
                               evenpi-of-sum)))))

(defthm sum-of-c-and-d-args-gives-evenpi
  (implies (evenpi (sum a2 b2 c2))
           (and (evenpi (sum (-- (m2 (sum a1 b1 c1))) a1 b1 c1 a2 b2 c2 ))
                (evenpi (sum (-- (m2 (sum a1 b1 c1))) a2 b2 c2 a1 b1 c1  ))))
  :hints (("Goal"
           :use ((:instance evenpi-for-3-d2-arguments
                            (a a1)
                            (b b1)
                            (c c1))
                 (:instance evenpi-of-sum
                            (x (SUM A1 B1 C1 (-- (M2 (SUM A1 B1 C1)))))
                            (y (SUM A2 B2 C2))))
           :in-theory (e/d () (evenpi-for-3-d2-arguments
                               evenpi-of-sum)))))

(defthm sum-of-d-args-gives-evenpi
  (implies (and (evenpi (sum a1 b1 c1))
                (evenpi (sum a2 b2 c2)))
           (evenpi (sum a1 b1 c1 a2 b2 c2)))
  :hints (("Goal"
           :use (:instance evenpi-of-sum
                           (x (sum a1 b1 c1))
                           (y (sum a2 b2 c2)))
           :in-theory (e/d () (evenpi-of-sum)))))

(defthm m2-of-ex-from-rp/--2
  (implies
   (and (rp-evl-meta-extract-global-facts :state state)
        (mult-formula-checks state)
        (rp-termp term)
        (b* ((term (ex-from-rp/-- term))) (case-match term  (('s & &) t))))
   (and (equal (m2 (sum (sum-list (rp-evl (rp-trans (cadr (ex-from-rp/-- term)))
                                          a))
                        (rp-evl (rp-trans (caddr (ex-from-rp/-- term)))
                                a)
                        rest ))
               (m2 (sum (rp-evl (rp-trans term) a) rest)))
        (equal (m2 (sum (sum-list (rp-evl (rp-trans (cadr (ex-from-rp/-- term)))
                                          a))
                        (rp-evl (rp-trans (caddr (ex-from-rp/-- term)))
                                a)))
               (m2 (sum (rp-evl (rp-trans term) a))))
        ))
  :hints (("goal"
           :use ((:instance m2-of-ex-from-rp/--)
                 (:instance m2-of-ex-from-rp/--
                            (rest 0)))
           :in-theory (e/d* (regular-eval-lemmas)
                            (m2-of-ex-from-rp/--
                             s-fix-pp-args-aux-correct-dummy-lemma1)))))

(defthm m2-equals-dummy-lemma
  (implies (equal (m2 (sum x y)) (m2 (sum a b c)))
           (equal (equal (m2 (sum x y other))
                         (m2 (sum a b other c)))
                  t)))

(defthm c/d-merge-fast-aux-valid-sc
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp pp-arg1) (rp-termp pp-arg2)
                (rp-termp pp-coughed-from-arg)
                (rp-termp s-arg2)
                (rp-termp s-coughed-from-arg)
                (rp-termp c/d-arg)
                (consp s-arg2)
                (equal (car s-arg2) 'list)
                (consp (cdr s-arg2))
                (valid-sc pp-arg1 a) (valid-sc pp-arg2 a)
                (valid-sc pp-coughed-from-arg a)
                (valid-sc s-arg2 a)
                (valid-sc s-coughed-from-arg a)
                (valid-sc c/d-arg a))
           (b* (((mv s-coughed pp-coughed c/d-merged)
                 (c/d-merge-fast-aux pp-arg1 pp-arg2 pp-coughed-from-arg
                                     s-arg2 s-coughed-from-arg
                                     c/d-arg clean-flg)))
             (and (valid-sc s-coughed a)
                  (valid-sc c/d-merged a)
                  (valid-sc pp-coughed a))))
  :hints (("Goal"
           :do-not-induct t
           :expand ((VALID-SC ''NIL A)
                    (RP-TERMP (CONS 'LIST (CDDR S-ARG2)))
                    (:free (x) (valid-sc (cons 'list x) a)))
           :in-theory (e/d (c/d-merge-fast-aux
                            clean-c/d-args
                            d2-of-times2-reverse)
                           (d2-of-times2
                            (:DEFINITION RP-TERMP)
                            (:REWRITE IS-IF-RP-TERMP)
                            (:DEFINITION VALID-SC)
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE VALID-SC-LEMMA1)
                            (:DEFINITION ACL2::APPLY$-BADGEP)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                            (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                            (:DEFINITION SUBSETP-EQUAL)
                            (:DEFINITION MEMBER-EQUAL)
                            (:DEFINITION TRUE-LISTP)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 2)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE
                             ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                            c/d-merge-slow-aux-correct)))))

(defthm c/d-merge-fast-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp pp-arg1) (rp-termp pp-arg2)
                (rp-termp pp-coughed-from-arg)
                (rp-termp s-arg2)
                (rp-termp s-coughed-from-arg)
                (rp-termp c/d-arg)
                (consp s-arg2)
                (equal (car s-arg2) 'list)
                (consp (cdr s-arg2))
                (valid-sc pp-arg1 a) (valid-sc pp-arg2 a)
                (valid-sc pp-coughed-from-arg a)
                (valid-sc s-arg2 a)
                (valid-sc s-coughed-from-arg a)
                (valid-sc c/d-arg a))
           (b* (((mv s-coughed pp-coughed c/d-merged)
                 (c/d-merge-fast-aux pp-arg1 pp-arg2 pp-coughed-from-arg
                                     s-arg2 s-coughed-from-arg
                                     c/d-arg clean-flg)))
             (equal (sum (sum-list (rp-evlt s-coughed a))
                         (sum-list (rp-evlt pp-coughed a))
                         (rp-evlt c/d-merged a))
                    (f2 (sum (rp-evlt `(sum-list ,pp-arg1) a)
                             (rp-evlt `(sum-list ,pp-arg2) a)
                             (rp-evlt `(sum-list ,pp-coughed-from-arg) a)
                             (rp-evlt `(sum-list (list . ,(cddr s-arg2))) a)
                             (rp-evlt `(sum-list ,s-coughed-from-arg) a)
                             (rp-evlt c/d-arg a))))))
  :hints (("Goal"
           :do-not-induct t
           :expand ((VALID-SC ''NIL A)
                    (RP-TERMP (CONS 'LIST (CDDR S-ARG2)))
                    (:free (x) (valid-sc (cons 'list x) a)))
           :in-theory (e/d (c/d-merge-fast-aux
                            clean-c/d-args
                            f2-of-times2-reverse
                            d2-of-times2-reverse)
                           (d2-of-times2
                            f2-of-times2
                            (:DEFINITION RP-TERMP)
                            (:REWRITE IS-IF-RP-TERMP)
                            (:DEFINITION VALID-SC)
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE VALID-SC-LEMMA1)
                            (:DEFINITION ACL2::APPLY$-BADGEP)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                            (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                            (:DEFINITION SUBSETP-EQUAL)
                            (:DEFINITION MEMBER-EQUAL)
                            (:DEFINITION TRUE-LISTP)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 2)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE
                             ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                            c/d-merge-slow-aux-correct)))))

(local
 (defthm limit-1-to-sum
   (implies (not (zp limit))
            (equal (+ -1 limit)
                   (sum limit -1)))
   :hints (("Goal"
            :in-theory (e/d (zp) ())))))

(defthm m2-of-and$
  (equal (m2 (and$ a b))
         (and$ a b))
  :hints (("Goal"
           :in-theory (e/d (and$) ()))))

(encapsulate
  nil

  ;; (local
  ;;  (skip-proofs
  ;;   (defthm CAN-C-MERGE-FAST-override
  ;;     (equal (CAN-C-MERGE-FAST x y)
  ;;            nil))))

  (local
   (in-theory (e/d* (get-c/d-args
                     (:REWRITE REGULAR-RP-EVL-OF_--_WHEN_MULT-FORMULA-CHECKS)
                     (:REWRITE REGULAR-RP-EVL-OF_BINARY-AND_WHEN_MULT-FORMULA-CHECKS)
                     (:REWRITE REGULAR-RP-EVL-OF_BINARY-APPEND_WHEN_MULT-FORMULA-CHECKS)
                     (:REWRITE REGULAR-RP-EVL-OF_BINARY-SUM_WHEN_MULT-FORMULA-CHECKS)
                     (:REWRITE REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS)
                     (:REWRITE REGULAR-RP-EVL-OF_D-SUM_WHEN_MULT-FORMULA-CHECKS)
                     (:REWRITE REGULAR-RP-EVL-OF_D_WHEN_MULT-FORMULA-CHECKS)
                     (:REWRITE REGULAR-RP-EVL-OF_S_WHEN_MULT-FORMULA-CHECKS)

                     clean-c/d-args
                     remove-s-from-for-fast-merge
                     sum-of-swap-c/ds-reverse
                     f2-to-d2
                     d2-of-times2-reverse)
                    (RP-EVL-OF-VARIABLE

                     rp-termp
                     is-falist
                     d2-to-f2
                     d2-of-times2
                     D2-OF-MINUS
                     f2-of-minus
                     valid-sc
                     sum-of-swap-c/ds
                     sum-of-swap-c/ds-for-swapped-fncs
                     rp-trans-is-term-when-list-is-absent))))

  (defthm-c/d-merge
    (defthm s-of-s-fix-aux-correct
      (implies (and (rp-evl-meta-extract-global-facts :state state)
                    (mult-formula-checks state)
                    (rp-term-listp s-lst)
                    (rp-termp pp)
                    (integerp limit)
                    (rp-termp c/d)
                    (valid-sc-subterms s-lst a)
                    (valid-sc pp a)
                    (valid-sc c/d a))
               (b* (((mv pp-res c/d-res)
                     (s-of-s-fix-aux s-lst pp c/d limit)))
                 (and (equal (m2 (sum (sum-list (rp-evlt pp-res a))
                                      (rp-evlt c/d-res a)))
                             (m2 (sum (sum-list-eval s-lst a)
                                      (sum-list (rp-evlt pp a))
                                      (rp-evlt c/d a))))
                      (valid-sc pp-res a)
                      (valid-sc c/d-res a))))
      :flag s-of-s-fix-aux)

    (defthm s-of-s-fix-correct
      (implies (and (rp-evl-meta-extract-global-facts :state state)
                    (mult-formula-checks state)
                    (rp-termp s)
                    (rp-termp pp)
                    (integerp limit)
                    (rp-termp c/d)
                    (valid-sc s a)
                    (valid-sc pp a)
                    (valid-sc c/d a))
               (b* (((mv pp-res c/d-res)
                     (s-of-s-fix s pp c/d limit)))
                 (and (equal (m2 (sum (sum-list (rp-evlt pp-res a))
                                      (rp-evlt c/d-res a)))
                             (m2 (sum (sum-list (rp-evlt s a))
                                      (sum-list (rp-evlt pp a))
                                      (rp-evlt c/d a))))
                      (valid-sc pp-res a)
                      (valid-sc c/d-res a))))
      :flag s-of-s-fix)
    (defthm get-extra-s-arg-correct
      (implies (and (rp-evl-meta-extract-global-facts :state state)
                    (mult-formula-checks state)
                    (rp-termp s-arg)
                    (integerp limit)
                    (rp-termp pp-arg)
                    (rp-termp c/d-arg)
                    (valid-sc s-arg a)
                    (valid-sc pp-arg a)
                    (valid-sc c/d-arg a))
               (b* ((extra-s-arg
                     (get-extra-s-arg s-arg pp-arg c/d-arg limit)))
                 (and (equal (rp-evlt extra-s-arg a)
                             (list (-- (m2 (sum (sum-list (rp-evlt s-arg a))
                                                (sum-list (rp-evlt pp-arg a))
                                                (rp-evlt c/d-arg a))))))
                      (valid-sc extra-s-arg a))))
      :flag get-extra-s-arg)
    (defthm c/d-merge-correct
      (implies (and (rp-evl-meta-extract-global-facts :state state)
                    (mult-formula-checks state)
                    (rp-termp c/d1)
                    (integerp limit)
                    (rp-termp c/d2)
                    (valid-sc c/d1 a)
                    (valid-sc c/d2 a))
               (b* (((mv s-coughed pp-coughed c/d-merged)
                     (c/d-merge c/d1 c/d2 clean-flg limit)))
                 (and (valid-sc s-coughed a)
                      (valid-sc pp-coughed a)
                      (valid-sc c/d-merged a)
                      (equal (sum (sum-list (rp-evlt s-coughed a))
                                  (sum-list (rp-evlt pp-coughed a))
                                  (rp-evlt c/d-merged a))
                             (sum (rp-evlt c/d1 a)
                                  (rp-evlt c/d2 a))))))
      :flag c/d-merge)
    :hints (("Subgoal *1/27"
             :use ((:instance can-c-merge-fast-correct
                              (c/d1 (ex-from-rp c/d1))
                              (c/d2 (ex-from-rp c/d2)))
                   (:instance can-c-merge-fast-and-consp
                              (c/d1 (ex-from-rp c/d1))
                              (c/d2 (ex-from-rp c/d2)))))
            ("Subgoal *1/5"
             :use ((:instance m2-of-ex-from-rp/--
                              (term (CAR S-LST))
                              (rest 0))))
            ("Subgoal *1/4"
             :use ((:instance m2-of-ex-from-rp/--
                              (term (CAR S-LST))
                              (rest 0))))
            ("Subgoal *1/3"
             :use ((:instance m2-of-ex-from-rp/--
                              (term (CAR S-LST))
                              (rest 0))))
            ("Subgoal *1/2"
             :use ((:instance m2-of-ex-from-rp/--
                              (term (CAR S-LST))
                              (rest 0))))
            ("Subgoal *1/2.1"
             :use ((:instance rid-of-c/d-merge-sum
                              (other (SUM-LIST
                                      (RP-EVL (RP-TRANS (MV-NTH 0
                                                                (S-OF-S-FIX-AUX (CDR S-LST)
                                                                                PP C/D (SUM LIMIT -1))))
                                              A)))
                              (param1 (MV-NTH 1
                                              (S-OF-S-FIX-AUX (CDR S-LST)
                                                              PP C/D (SUM LIMIT -1))))
                              (param2 (CADDR (EX-FROM-RP/-- (CAR S-LST))))
                              (flg nil)
                              (limit (SUM LIMIT -1)))
                   (:instance m2-of-ex-from-rp/--
                              (term (CAR S-LST))
                              (rest (sum (SUM-LIST
                                          (RP-EVL (RP-TRANS (MV-NTH 0
                                                                    (S-OF-S-FIX-AUX (CDR S-LST)
                                                                                    PP C/D (SUM LIMIT -1))))
                                                  A))
                                         (RP-EVL (RP-TRANS (MV-NTH 1
                                                                   (S-OF-S-FIX-AUX (CDR S-LST)
                                                                                   PP C/D (SUM LIMIT -1))))
                                                 A))))))
            ("Subgoal *1/17"
             :use ((:instance c/d-cough-correct
                              (c/d (MV-NTH 1
                                           (S-OF-S-FIX-AUX (CDR S)
                                                           PP C/D (SUM -1
                                                                       LIMIT))))
                              (rest (SUM-LIST
                                     (RP-EVL (RP-TRANS (MV-NTH 0
                                                               (S-OF-S-FIX-AUX (CDR S)
                                                                               PP C/D (+ -1 LIMIT))))
                                             A)))))
             :in-theory (disable c/d-cough-correct))
            ("Goal"
             :do-not-induct t
             :expand ((C/D-MERGE C/D1 C/D2 CLEAN-FLG LIMIT)
                      (S-OF-S-FIX-AUX NIL PP C/D LIMIT)
                      (S-OF-S-FIX-AUX S-LST PP C/D LIMIT)
                      (GET-EXTRA-S-ARG S-ARG PP-ARG C/D-ARG LIMIT)
                      (S-OF-S-FIX S PP C/D LIMIT)
                      (S-OF-S-FIX ''NIL PP C/D LIMIT)
                      (:free (x) (rp-trans (cons 'quote x)))
                      (:free (x) (is-rp (cons 'rp x)))
                      (:free (x) (is-falist (cons 'rp x)))
                      (:free (x) (rp-termp (cons 'list x)))
                      (:free (x) (is-if (cons 'if x)))
                      (:free (x) (GET-C/D-ARGS$INLINE x))
                      (:free (x) (valid-sc (cons 'binary-sum x) a))
                      (:free (x) (valid-sc (cons 'd x) a))
                      (:free (x) (valid-sc (cons 'binary-append x) a))
                      (:free (x) (valid-sc (cons '-- x) a))
                      (:free (x) (valid-sc (cons 'rp x) a))
                      (:free (x) (valid-sc (cons 'd-sum x) a))
                      (:free (x) (valid-sc (cons 'cons x) a))
                      (:free (x) (valid-sc (cons 'c x) a))
                      (:free (x) (valid-sc (cons 's x) a))
                      (:free (x) (valid-sc (cons 'list x) a))
                      (:free (x y) (valid-sc-subterms (cons x y) a)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; c/d-merge lemmas

(defthm sum-list-eval-of-quote-all
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (sum-list-eval (quote-all lst) a)
                  (sum-list lst)))
  :hints (("goal"
           :induct (quote-all lst)
           :do-not-induct t
           :in-theory (e/d (quote-all
                            SUM-LIST) ()))))

(defthm quotep-valid-sc-subterms
  (valid-sc-subterms (QUOTE-ALL lst) a)
  :hints (("Goal"
           :induct (quote-all lst)
           :do-not-induct t
           :in-theory (e/d (quote-all
                            SUM-LIST) ()))))

(defthmd new-sum-merge-aux-correct-lemma1
  (implies (and (case-match term (('cons & &) t)))
           (equal (rp-evlt (ex-from-rp term) a)
                  (cons (rp-evlt (ex-from-rp (cadr term)) a)
                        (rp-evlt (ex-from-rp (caddr term)) a)))))

(defthmd new-sum-merge-aux-correct-lemma2
  (implies (and (equal (car term) 'quote)
                (RP-TERMP TERM))
           (equal (rp-evlt (ex-from-rp term) a)
                  (unquote term))))

(create-regular-eval-lemma sum-list 1 mult-formula-checks)
(create-regular-eval-lemma c-res 3 mult-formula-checks)

(defthmd
  rp-evlt-of-ex-from-rp-reverse-2
  (implies (syntaxp (or (atom term)))
           (equal (rp-evl (rp-trans term) a)
                  (rp-evl (rp-trans (ex-from-rp term))
                          a))))

(progn
  (defthm is-rp-of-bitp
    (is-rp `(rp 'bitp ,x))
    :hints (("Goal"
             :in-theory (e/d (is-rp) ()))))
  (local
   (create-regular-eval-lemma cons 2 mult-formula-checks))
  (local
   (create-regular-eval-lemma binary-not 1 mult-formula-checks))
  (local
   (create-regular-eval-lemma binary-xor 2 mult-formula-checks))
  (local
   (create-regular-eval-lemma binary-or 2 mult-formula-checks))
  (local
   (create-regular-eval-lemma binary-and 2 mult-formula-checks))
  (local
   (create-regular-eval-lemma binary-? 3 mult-formula-checks))

  (local
   (defthm pp-termp-is-bitp-lemma
     (implies (and (PP-HAS-BITP-RP TERM)
                   (rp-evl-meta-extract-global-facts :state state)
                   (VALID-SC TERM A)
                   (MULT-FORMULA-CHECKS STATE))
              (and (BITP (RP-EVLt TERM A))
                   (BITP (RP-EVLt (EX-FROM-RP TERM) A))))
     :hints (("Goal"
              :induct (PP-HAS-BITP-RP TERM)
              :in-theory (e/d* (is-if is-rp
                                      PP-HAS-BITP-RP)
                               (bitp
                                NOT-INCLUDE-RP-MEANS-VALID-SC
                                ))))))

  (local
   (defthm pp-termp-is-bitp
     (implies (and (rp-evl-meta-extract-global-facts :state state)
                   (mult-formula-checks state)
                   (pp-term-p term)
                   (valid-sc term a))
              (bitp (rp-evlt term a)))
     :hints (("Goal"
              :do-not-induct t
              :expand ((PP-TERM-P TERM))
              :in-theory (e/d* (pp-term-p
                                (:REWRITE
                                 REGULAR-RP-EVL-OF_BINARY-?_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                                (:REWRITE
                                 REGULAR-RP-EVL-OF_BINARY-AND_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                                (:REWRITE
                                 REGULAR-RP-EVL-OF_BINARY-NOT_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                                (:REWRITE
                                 REGULAR-RP-EVL-OF_BINARY-OR_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                                (:REWRITE
                                 REGULAR-RP-EVL-OF_BINARY-XOR_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                                (:REWRITE
                                 REGULAR-RP-EVL-OF_BIT-OF_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                                is-rp
                                rp-evlt-of-ex-from-rp-reverse-2
                                is-if)
                               (bitp
                                pp-term-p
                                RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                                rp-evlt-of-ex-from-rp
                                EX-FROM-RP-LEMMA1
                                rp-evlt-of-ex-from-rp))))))

  (local
   (defthm light-pp-termp-is-bitp
     (implies (and (rp-evl-meta-extract-global-facts :state state)
                   (mult-formula-checks state)
                   (LIGHT-PP-TERM-P term)
                   (valid-sc term a))
              (bitp (rp-evlt term a)))
     :hints (("Goal"
              :do-not-induct t
              :expand ((LIGHT-PP-TERM-P TERM))
              :in-theory (e/d* (LIGHT-PP-TERM-p
                                is-rp
                                (:REWRITE
                                 REGULAR-RP-EVL-OF_BINARY-?_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                                (:REWRITE
                                 REGULAR-RP-EVL-OF_BINARY-AND_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                                (:REWRITE
                                 REGULAR-RP-EVL-OF_BINARY-NOT_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                                (:REWRITE
                                 REGULAR-RP-EVL-OF_BINARY-OR_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                                (:REWRITE
                                 REGULAR-RP-EVL-OF_BINARY-XOR_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                                (:REWRITE
                                 REGULAR-RP-EVL-OF_BIT-OF_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                                rp-evlt-of-ex-from-rp-reverse-2
                                is-if)
                               (bitp
                                pp-term-p
                                RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                                rp-evlt-of-ex-from-rp
                                EX-FROM-RP-LEMMA1
                                rp-evlt-of-ex-from-rp))))))

  (local
   (defthm PP-HAS-BITP-RP-EX-FROM-RP
     (not (PP-HAS-BITP-RP (EX-FROM-RP TERM)))
     :hints (("Goal"
              :induct (EX-FROM-RP TERM)
              :do-not-induct t
              :in-theory (e/d (EX-FROM-RP pp-has-bitp-rp
                                          is-rp) ())))))

  (local
   (defthm pp-termp-of-ex-from-rp
     (implies (pp-term-p (ex-from-rp term))
              (pp-term-p term))
     :hints (("Goal"
              :expand ((PP-TERM-P (EX-FROM-RP TERM))
                       (pp-term-p term))
              :do-not-induct t
              :in-theory (e/d (pp-term-p) ())))))

  (local
   (defthm LIGHT-PP-TERM-P-of-ex-from-rp
     (implies (LIGHT-PP-TERM-P (ex-from-rp term))
              (LIGHT-PP-TERM-P term))
     :hints (("Goal"
              :expand ((LIGHT-PP-TERM-P (EX-FROM-RP TERM))
                       (LIGHT-PP-TERM-P term))
              :do-not-induct t
              :in-theory (e/d (LIGHT-PP-TERM-P) ()))))))

(defthm 4vec->pp-term-valid-sc
  (implies (and (valid-sc term a))
           (valid-sc (4vec->pp-term term) a))
  :hints (("Goal"
           :do-not-induct t
           :induct (4vec->pp-term term)
           :in-theory (e/d (is-rp
                            is-if
                            good-4vec-term-p
                            4vec->pp-term)
                           (pp-term-p
                            (:REWRITE VALID-SC-LEMMA1)
                            (:DEFINITION INCLUDE-FNC-SUBTERMS)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 2)
                            (:REWRITE ACL2::FN-CHECK-DEF-NOT-QUOTE)
                            (:REWRITE VALID-SC-OF-EX-FROM-RP)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC)
                            (:REWRITE VALID-SC-SINGLE-STEP)
                            (:DEFINITION EVAL-AND-ALL)
                            (:DEFINITION EX-FROM-RP)
                            (:REWRITE DEFAULT-CAR)
                            (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:DEFINITION ACL2::APPLY$-BADGEP)
;(:REWRITE VALID-SC-CADR)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:REWRITE ATOM-RP-TERMP-IS-SYMBOLP)
                            natp
                            rp-termp
                            include-fnc)))))

(encapsulate
  nil
  (local
   (progn
     (create-regular-eval-lemma svl::bits 3 mult-formula-checks)
     (create-regular-eval-lemma svl::4vec-bitnot$ 2 mult-formula-checks)
     (create-regular-eval-lemma svl::4vec-bitand 2 mult-formula-checks)
     (create-regular-eval-lemma sv::4vec-bitxor 2 mult-formula-checks)
     (create-regular-eval-lemma svl::4vec-bitor 2 mult-formula-checks)
     (create-regular-eval-lemma svl::4vec-? 3 mult-formula-checks)

     (create-regular-eval-lemma sv::3vec-fix 1 mult-formula-checks)
     (create-regular-eval-lemma svl::4vec-?* 3 mult-formula-checks)))

  (local
   (create-regular-eval-lemma sv::4vec-fix$inline 1 mult-formula-checks))

  (local
   (encapsulate
     nil

     (local
      (include-book "centaur/bitops/ihsext-basics" :dir :system))

     (defthmd bits-is-bit-of
       (implies (and (natp start)
                     (integerp num)
                     (equal size 1))
                (equal (svl::bits num start size)
                       (bit-of num start)))
       :hints (("Goal"
                :in-theory (e/d (svl::bits
                                 bit-of
                                 SV::4VEC-SHIFT-CORE
                                 SV::4VEC-RSH
                                 SV::4VEC->UPPER
                                 SV::4VEC->LOWER
                                 SV::4VEC-PART-SELECT
                                 SV::4VEC-ZERO-EXT)
                                (SVL::4VEC-ZERO-EXT-IS-4VEC-CONCAT
                                 +-IS-SUM
                                 FLOOR2-IF-F2
                                 MOD2-IS-M2)))))))

  (progn
    (local
     (defthm 4vec-bitnot$-is-not$
       (implies (bitp num)
                (equal (svl::4vec-bitnot$ 1 num)
                       (not$ num)))))
    (local
     (defthm 4vec-fix$-when-bitp
       (implies (bitp num)
                (equal (sv::4vec-fix num)
                       num))))

    (local
     (defthm 3vec-fix$-when-bitp
       (implies (bitp num)
                (equal (sv::3vec-fix num)
                       num))))

    (local
     (defthm 4vec-bitand-is-and$
       (implies (and (bitp num)
                     (bitp num2))
                (equal (svl::4vec-bitand num num2)
                       (and$ num num2)))))

    (local
     (defthm 4vec-bitor-is-or$
       (implies (and (bitp num)
                     (bitp num2))
                (equal (svl::4vec-bitor num num2)
                       (or$ num num2)))))

    (local
     (defthm 4vec-bitxor-is-binary-xor
       (implies (and (bitp num)
                     (bitp num2))
                (equal (sv::4vec-bitxor num num2)
                       (binary-xor num num2)))))

    (local
     (defthm 4vec-?-is-binary-?
       (implies (and (bitp num)
                     (bitp num2)
                     (bitp num3))
                (and (equal (svl::4vec-? num num2 num3)
                            (binary-? num num2 num3))
                     (equal (svl::4vec-?* num num2 num3)
                            (binary-? num num2 num3)))))))

  (local
   (defthm 4vec->pp-term-correct-bitp-lemma
     (implies (and (valid-sc term a)
                   (rp-evl-meta-extract-global-facts :state state)
                   (mult-formula-checks state)
                   (good-4vec-term-p term)
                   (equal (rp-evlt (4vec->pp-term term) a)
                          (rp-evlt term a)))
              (bitp (rp-evlt term a)))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d () (bitp
                                  pp-term-p))))))

  (local
   (encapsulate
     nil

     (local
      (in-theory (e/d (valid-sc-single-step is-rp)
                      (bitp
                       rp-trans
                       rp-termp
                       not-include-rp-means-valid-sc
                       valid-sc
                       VALID-SC-EX-FROM-RP
                       VALID-SC-OF-EX-FROM-RP
                       rp-evl-of-variable))))

     (defthm 4vec->pp-term-correct-bitp-lemma-2
       (implies (and (valid-sc term a)
                     (rp-evl-meta-extract-global-facts :state state)
                     (mult-formula-checks state)
                     (good-4vec-term-p term)
                     (b* ((term (ex-from-rp term)))
                       (case-match term (('svl::bits & & &) t))))
                (integerp (rp-evl (rp-trans (caddr (cadr (ex-from-rp term)))) a)))
       :otf-flg t
       :hints (("Subgoal 1"
                :expand ((VALID-SC (EX-FROM-RP TERM) A)
                         (GOOD-4VEC-TERM-P TERM)))
               ("Subgoal 2"
                :in-theory (e/d (VALID-SC-EX-FROM-RP)
                                ()))
               ("goal"
                :do-not-induct t
                :expand ((good-4vec-term-p term))
                :cases ((valid-sc (ex-from-rp term) a)))))))

  (defthm 4vec->pp-term-correct
    (implies (and (valid-sc term a)
                  (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (good-4vec-term-p term))
             (equal (rp-evlt (4vec->pp-term term) a)
                    (rp-evlt term a)))
    :hints (("Goal"
             :do-not-induct t
             :induct (4vec->pp-term term)
             :expand ((:free (x) (nth 3 x))
                      (:free (x) (nth 2 x))
                      (:free (x) (nth 1 x)))
             :in-theory (e/d* (4vec->pp-term
                               rp-evlt-of-ex-from-rp-reverse-2
                               regular-eval-lemmas
                               bits-is-bit-of
                               good-4vec-term-p
                               )
                              (pp-term-p
                               regular-eval-lemmas-with-ex-from-rp
                               rp-termp
                               (:DEFINITION VALID-SC)
                               (:DEFINITION INCLUDE-FNC)
                               (:REWRITE VALID-SC-LEMMA1)
                               (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                               (:DEFINITION ACL2::APPLY$-BADGEP)
                               (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                               (:DEFINITION EX-FROM-RP)
                               (:REWRITE DEFAULT-CDR)
                               (:DEFINITION SUBSETP-EQUAL)
                               (:DEFINITION MEMBER-EQUAL)
                               (:REWRITE PP-TERMP-OF-EX-FROM-RP)
                               (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 2)
                               (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                               (:REWRITE NOT-INCLUDE-RP)
                               (:REWRITE
                                ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                               (:REWRITE DEFAULT-CAR)
                               (:DEFINITION EVAL-AND-ALL)
                               (:DEFINITION RP-TERM-LISTP)
                               (:DEFINITION TRUE-LISTP)
                               (:REWRITE ACL2::O-P-O-INFP-CAR)
                               (:DEFINITION QUOTEP)
                               natp
                               bitp
                               rp-evlt-of-ex-from-rp))))))

(local
 (defthm rp-evlt-of-ex-from-rp-equivalance
   (and (equal (equal (RP-EVLT (EX-FROM-RP x) A)
                      (RP-EVLT x A))
               t)
        (equal (equal (RP-EVLT x A)
                      (RP-EVLT (EX-FROM-RP x) A))
               t)
        (equal (equal (SUM-LIST (RP-EVLT x A))
                      (SUM-LIST (RP-EVLT (EX-FROM-RP x) A)))
               t))))

(local
 (defthm dummy-lemma3
   (implies (and
             (equal (sum a b c) d1)
             (equal x y)
             (equal d1 d2))
            (and (equal (equal (sum a b c x)
                          (sum d2 y))
                        t)
                 (equal (equal (sum a b c x)
                               (sum y d2))
                   t)))))

(defthm new-sum-merge-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a)
                (well-formed-new-sum term)
                (rp-termp term))
           (b* (((mv s pp c/d)
                 (new-sum-merge-aux term)))
             (and (equal (sum (sum-list (rp-evlt s a))
                              (sum-list (rp-evlt pp a))
                              (rp-evlt c/d a))
                         (sum-list (rp-evlt term a)))
                  (valid-sc s a)
                  (valid-sc pp a)
                  (valid-sc c/d a))))
  ;;:otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :induct (new-sum-merge-aux term)
           :expand ((:free (x) (valid-sc (cons 'list x) a))
                    (well-formed-new-sum term)
                    (valid-SC ''NIL A)
                    (VALID-SC ''0 A)
                    (:free (x) (rp-termp (cons 'list x))))
           :in-theory (e/d* (new-sum-merge-aux
                             c-res
                             ;;regular-eval-lemmas-with-ex-from-rp
                             RP-EVLT-OF-EX-FROM-RP-REVERSE-2
                             
                             new-sum-merge-aux-correct-lemma1
                             new-sum-merge-aux-correct-lemma2
                             
                             #|(:REWRITE
                              REGULAR-RP-EVL-OF_C-RES_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)||#
                             (:REWRITE
                              REGULAR-RP-EVL-OF_C-RES_WHEN_MULT-FORMULA-CHECKS)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_CONS_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_D_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_D_WHEN_MULT-FORMULA-CHECKS)
                             #|(:REWRITE
                              regular-rp-evl-of_sum-list_when_mult-formula-checks_with-ex-from-rp)||#
                             (:REWRITE
                              regular-rp-evl-of_sum-list_when_mult-formula-checks)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_S_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_S_WHEN_MULT-FORMULA-CHECKS)
                             )
                            (valid-sc
                             (:TYPE-PRESCRIPTION FALIST-CONSISTENT)
                             (:DEFINITION EVAL-AND-ALL)
                             (:REWRITE VALID-SC-EX-FROM-RP-2)
                             (:REWRITE RP-EVL-OF-UNARY-/-CALL)
                             (:REWRITE RP-EVL-OF-TYPESPEC-CHECK-CALL)
                             (:REWRITE EX-FROM-RP-X2)
                             (:REWRITE RP-EVLT-WHEN-QUOTEP)
                             (:REWRITE
                              RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT)
                             (:TYPE-PRESCRIPTION EVAL-AND-ALL)
                             (:TYPE-PRESCRIPTION CONTEXT-FROM-RP)
                             (:REWRITE IS-RP-PSEUDO-TERMP)
                             (:REWRITE VALID-SC-LEMMA1)
                             (:DEFINITION WELL-FORMED-NEW-SUM)
                             4vec->pp-term
                             pp-flatten
                             pp-sum-merge
                             (:REWRITE RP-EVL-OF-VARIABLE)
                             (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                             (:REWRITE RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS)
                             include-fnc

                             (:TYPE-PRESCRIPTION NEW-SUM-MERGE-AUX)
                             (:TYPE-PRESCRIPTION MULT-FORMULA-CHECKS)
                             (:TYPE-PRESCRIPTION GOOD-4VEC-TERM-P)
                             (:TYPE-PRESCRIPTION IS-RP$INLINE)
                             (:DEFINITION WELL-FORMED-NEW-SUM)
                             (:TYPE-PRESCRIPTION IS-RP-LOOSE$INLINE)
                             (:REWRITE IS-IF-RP-TERMP)
                             (:TYPE-PRESCRIPTION O<)
                             (:REWRITE RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL)
                             (:REWRITE EX-FROM-SYNP-LEMMA1)
                             (:TYPE-PRESCRIPTION BINARY-SUM)
                             (:REWRITE RP-EVL-OF-STRINGP-CALL)
                             (:REWRITE RP-EVL-OF-ZP-CALL)
                             (:REWRITE RP-EVL-OF-UNARY---CALL)
                             (:DEFINITION INCLUDE-FNC)
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                             (:REWRITE ACL2::O-P-O-INFP-CAR)
                             (:DEFINITION INCLUDE-FNC-SUBTERMS)
                             (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                             (:TYPE-PRESCRIPTION INCLUDE-FNC)
                             ;;(:DEFINITION WELL-FORMED-NEW-SUM)
                             rp-evlt-of-ex-from-rp
                             rp-termp
                             (:TYPE-PRESCRIPTION VALID-SC)
                             (:TYPE-PRESCRIPTION WELL-FORMED-NEW-SUM)
                             (:REWRITE DEFAULT-CAR)
                             (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                             (:DEFINITION PP-TERM-P)
                             (:TYPE-PRESCRIPTION SUM-LIST)
                             (:TYPE-PRESCRIPTION RP-TERMP)
                             (:DEFINITION EX-FROM-RP)
                             (:REWRITE DEFAULT-CDR)
                             (:DEFINITION IS-RP$INLINE))))))

#|(defthm new-sum-merge-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a)
                (well-formed-new-sum term)
                (rp-termp term))
           (b* (((mv s pp c/d)
                 (new-sum-merge term)))
             (and (equal (sum (sum-list (rp-evlt s a))
                              (sum-list (rp-evlt pp a))
                              (rp-evlt c/d a))
                         (sum-list (rp-evlt term a)))
                  (valid-sc s a)
                  (valid-sc pp a)
                  (valid-sc c/d a))))
  :hints (("Goal"
:in-theory (e/d (new-sum-merge) ()))))||#

(defthm f2-of-quarternaryp
  (implies (quarternaryp sum)
           (bitp (f2 sum)))
  :hints (("Goal"
           :in-theory (e/d (quarternaryp) ()))))

(encapsulate
  nil

  (local
   (define maxp (val (max natp))
     :measure (nfix max)
     :prepwork
     ((Local
       (in-theory (e/d ()  (+-is-sum limit-1-to-sum)))))
     (if (zp max)
         (equal val 0)
       (or (equal val max)
           (maxp val (1- max))))))

  (local
   (defthm maxp-lemma1
     (implies (and (natp x)
                   (natp y)
                   (<= x y))
              (maxp x y))
     :hints (("Goal"
              :induct (maxp x y)
              :in-theory (e/d (maxp)
                              (LIMIT-1-TO-SUM
                               +-is-sum))))))

  (local
   (defthmd
     rp-evlt-of-ex-from-rp-reverse-3
     (implies (and (syntaxp (equal term '(car (cdr term))))
                   (or (not (equal (car term) 'rp))
                       (EQUAL (CAR (EX-FROM-RP term))
                              'S)))
              (equal (rp-evl (rp-trans term) a)
                     (rp-evl (rp-trans (ex-from-rp term))
                             a)))))

  (local
   (defthm lemma1
     (implies (EQUAL (EX-FROM-RP term) ''0)
              (equal (RP-EVL (RP-TRANS term) A)
                     0))
     :hints (("Goal"
              :in-theory (e/d (rp-evlt-of-ex-from-rp-reverse)
                              (rp-evlt-of-ex-from-rp))))))

  (local
   (defthmd maxp-of-bitp-lemma
     (implies (and (not (zp max))
                   (not (zp x)))
              (equal (maxp x max)
                     (maxp (1- x) (1- max))))
     :hints (("Goal"
              :induct (maxp x max)
              :do-not-induct t
              :in-theory (e/d (maxp sum)
                              (+-is-sum
                               LIMIT-1-TO-SUM
                               natp))))))

  (local
   (defthm maxp-of-bitp
     (implies (and (bitp x)
                   (not (zp max))
                   (maxp (ifix rest) (1- max)))
              (and (maxp (sum x rest) max)
                   (maxp (sum rest x) max)))
     :hints (("Goal"
              :use ((:instance maxp-of-bitp-lemma
                               (x (sum x rest))))
              :in-theory (e/d (maxp sum)
                              (+-is-sum
                               LIMIT-1-TO-SUM
                               natp))))))

  (Local
   (defthm lemma2
     (implies (natp x)
              (NOT (ZP (SUM x 1))))
     :hints (("Goal"
              :in-theory (e/d (sum)
                              (+-is-sum))))))

  (local
   (defthm lemma3
     (implies (and (rp-evl-meta-extract-global-facts :state state)
                   (mult-formula-checks state)
                   (valid-sc term a)
                   (case-match term (('rp ''bitp &) t)))
              (and (bitp (rp-evlt term a))
                   (bitp (rp-evlt (ex-from-rp term) a))
                   (bitp (rp-evlt (caddr term) a))))
     :hints (("Goal"
              :in-theory (e/d () (bitp))))))

  (local
   (defthm lemma4
     (implies (NAT-LISTP lst)
              (natp (sum-list lst)))
     :hints (("Goal"
              :induct (sum-list lst)
              :do-not-induct t
              :in-theory (e/d (sum-list
                               nat-listp
                               sum)
                              (+-is-sum))))
     :rule-classes (:type-prescription :rewrite)))

  (local
   (defthm quarternaryp-sum-aux-correct
     (implies (and (rp-evl-meta-extract-global-facts :state state)
                   (mult-formula-checks state)
                   (valid-sc term a)
                   (rp-termp term))
              (b* (((mv res valid)
                    (quarternaryp-sum-aux term)))
                (implies valid
                         (maxp (sum-list (rp-evlt term a))
                               res))))
     :hints (("Goal"
              :do-not-induct t
              :induct (quarternaryp-sum-aux term)
              :in-theory (e/d* (quarternaryp-sum-aux
                                SUM-LIST
                                (:REWRITE REGULAR-RP-EVL-OF_CONS_WHEN_MULT-FORMULA-CHECKS)
                                (:REWRITE
                                 REGULAR-RP-EVL-OF_S_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                                rp-evlt-of-ex-from-rp-reverse-3)
                               (natp
                                REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS
                                zp
                                REGULAR-RP-EVL-OF_C-RES_WHEN_MULT-FORMULA-CHECKS
                                rp-evlt-of-ex-from-rp
                                ex-from-rp-lemma1
                                RP-EVL-OF-VARIABLE
                                RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                                ex-from-rp
                                ex-from-rp-loose
                                valid-sc
                                rp-termp))))))

  (local
   (defthm quarternaryp-is-maxp
     (equal (quarternaryp x)
            (maxp x 3))
     :hints (("Goal"
              :in-theory (e/d (quarternaryp maxp) ())))))

  (local
   (defthm maxp-trans
     (implies (and (maxp x y)
                   (maxp y z))
              (maxp x z))
     :hints (("Goal"
              :in-theory (e/d (maxp) ())))))

  (defthm quarternaryp-sum-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc term a)
                  (rp-termp term)
                  (quarternaryp-sum term))
             (quarternaryp (sum-list (rp-evlt term a))))
    :hints (("Goal"
             :use ((:instance maxp-trans
                              (z 3)
                              (y (MV-NTH 0 (quarternaryp-sum-aux TERM)))
                              (x (SUM-LIST (RP-EVL (RP-TRANS TERM) A)))))
             :in-theory (e/d (quarternaryp-sum
                              quarternaryp-sum-aux-correct)
                             (natp
                              maxp-trans
                              quarternaryp-sum-aux
                              REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS
                              zp
                              REGULAR-RP-EVL-OF_C-RES_WHEN_MULT-FORMULA-CHECKS
                              rp-evlt-of-ex-from-rp
                              ex-from-rp-lemma1
                              RP-EVL-OF-VARIABLE
                              RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                              ex-from-rp
                              ex-from-rp-loose
                              valid-sc
                              rp-termp))))))

(defthm contet-from-create-c-instance
  (equal (CONTEXT-FROM-RP (CREATE-C-INSTANCE a b c) context)
         context)
  :hints (("Goal"
           :in-theory (e/d (CREATE-C-INSTANCE
                            is-rp) ()))))

(defthm c-spec-meta-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc s a)
                (valid-sc pp a)
                (valid-sc c/d a)
                (rp-termp s)
                (rp-termp pp)
                (if quarternaryp
                    (quarternaryp (sum (sum-list (rp-evlt s a))
                                       (sum-list (rp-evlt pp a))
                                       (rp-evlt c/d a)))
                  t)
                (rp-termp c/d))
           (and (equal (rp-evlt (c-spec-meta-aux s pp c/d quarternaryp) a)
                       (f2 (sum (sum-list (rp-evlt s a))
                                (sum-list (rp-evlt pp a))
                                (rp-evlt c/d a))))
                (valid-sc (c-spec-meta-aux s pp c/d quarternaryp) a)))
  :hints (("Goal"
           :use ((:instance c/d-fix-s-args-correct
                            (rest 0)
                            (pp (S-SUM-MERGE (MV-NTH 0 (C/D-COUGH C/D))
                                             S)))
                 (:instance c/d-fix-pp-args-correct
                            (pp (MV-NTH 0
                                        (PP-SUM-MERGE (MV-NTH 1 (C/D-COUGH C/D))
                                                      PP)))
                            (rest (SUM-LIST (RP-EVL (RP-TRANS S) A)))
                            (limit (MV-NTH 1
                                           (PP-SUM-MERGE (MV-NTH 1 (C/D-COUGH C/D))
                                                         PP))))
                 (:instance c/d-fix-pp-args-correct
                            (pp (MV-NTH 0
                                        (PP-SUM-MERGE (MV-NTH 1 (C/D-COUGH C/D))
                                                      PP)))
                            (rest 0)
                            (limit (MV-NTH 1
                                           (PP-SUM-MERGE (MV-NTH 1 (C/D-COUGH C/D))
                                                         PP))))
                 (:instance c/d-fix-pp-args-correct
                            (pp (MV-NTH 0
                                        (PP-SUM-MERGE (MV-NTH 1 (C/D-COUGH C/D))
                                                      PP)))
                            (rest (SUM-LIST
                                   (RP-EVL
                                    (RP-TRANS
                                     (MV-NTH 1
                                             (C/D-FIX-S-ARGS (S-SUM-MERGE (MV-NTH 0 (C/D-COUGH C/D))
                                                                          S))))
                                    A)))
                            (limit (MV-NTH 1
                                           (PP-SUM-MERGE (MV-NTH 1 (C/D-COUGH C/D))
                                                         PP)))))
           :in-theory (e/d (c-spec-meta-aux
                            c-res
                            times2
                            f2-of-times2-reverse)
                           (c/d-fix-s-args-correct
                            bitp
                            c/d-fix-pp-args-correct
                            C/D-FIX-PP-ARGS
                            f2-of-times2)))))

(defthm c-spec-meta-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a)
                (rp-termp term))
           (and (equal (rp-evlt (mv-nth 0 (c-spec-meta term)) a)
                       (rp-evlt term a))
                (valid-sc (mv-nth 0 (c-spec-meta term)) a)))
  :hints (("Goal"
           :cases ((quarternaryp-sum (CADR TERM)))
           :in-theory (e/d (c-spec-meta
                            new-sum-merge) ()))))

(defthm m2-of-and$
  (equal (m2 (and$ a b))
         (and$ a b))
  :hints (("Goal"
           :in-theory (e/d (and$) ()))))

(defthm create-s-instance-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (force (valid-sc pp a))
                (force (valid-sc c/d a))
                (force (rp-termp pp))
                (force (rp-termp c/d)))
           (and (equal (rp-evlt (create-s-instance pp c/d) a)
                       (m2 (sum (sum-list (rp-evlt pp a))
                                (rp-evlt c/d a))))
                (valid-sc (create-s-instance pp c/d) a)))
  :hints (("Goal"
           :in-theory (e/d (create-s-instance) ()))))

(defthm m2-equals-dummy-lemma2
  (implies (and (equal (m2 a) (m2 b))
                (syntaxp (> (cons-count a)
                            (cons-count b))))
           (equal (equal (m2 (sum x a)) (m2 other))
                  (equal (m2 (sum x b)) (m2 other)))))

(defthm s-spec-meta-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc s a)
                (valid-sc pp a)
                (valid-sc c/d a)
                (rp-termp s)
                (rp-termp pp)
                (rp-termp c/d))
           (and (equal (rp-evlt (s-spec-meta-aux s pp c/d) a)
                       (m2 (sum (sum-list (rp-evlt s a))
                                (sum-list (rp-evlt pp a))
                                (rp-evlt c/d a))))
                (valid-sc (s-spec-meta-aux s pp c/d) a)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance s-of-s-fix-correct
                            (s (MV-NTH 0 (C/D-COUGH C/D)))
                            (pp (MV-NTH 0
                                        (PP-SUM-MERGE PP (MV-NTH 1 (C/D-COUGH C/D)))))
                            (c/d (MV-NTH 2 (C/D-COUGH C/D)))
                            (limit (EXPT 2 40)))
                 (:instance s-of-s-fix-correct
                            (s s)
                            (pp pp)
                            (c/d c/d)
                            (limit (EXPT 2 40)))
                 (:instance s-fix-args-correct
                            (term (MV-NTH
                                   0
                                   (S-OF-S-FIX (MV-NTH 0 (C/D-COUGH C/D))
                                               (MV-NTH 0
                                                       (PP-SUM-MERGE PP (MV-NTH 1 (C/D-COUGH C/D))))
                                               (MV-NTH 2 (C/D-COUGH C/D))
                                               1099511627776)))
                            (c/d 0))
                 (:instance s-fix-args-correct
                            (term (MV-NTH 0 (S-OF-S-FIX S PP C/D 1099511627776)))
                            (c/d 0)))

           :in-theory (e/d (s-spec-meta-aux
                            create-s-instance-correct
                            s)
                           (s-of-s-fix-correct
                            s-fix-args-correct
                            NOT-INCLUDE-RP-MEANS-VALID-SC
                            RP-EVL-OF-VARIABLE)))))

(defthm s-spec-meta-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a)
                (rp-termp term))
           (and (equal (rp-evlt (mv-nth 0 (s-spec-meta term)) a)
                       (rp-evlt term a))
                (valid-sc (mv-nth 0 (s-spec-meta term)) a)))
  :hints (("Goal"
           :in-theory (e/d (s-spec-meta
                            new-sum-merge) ()))))

(create-regular-eval-lemma s-c-spec 1 mult-formula-checks)
(create-regular-eval-lemma c-s-spec 1 mult-formula-checks)

(defthm context-from-rp-of-c-spec-meta-aux
  (equal (CONTEXT-FROM-RP (C-SPEC-META-AUX a b c nil) context)
         context)
  :hints (("Goal"
           :expand (C-SPEC-META-AUX a b c nil)
           :in-theory (e/d () ()))))

(defthm s-c-spec-meta-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a)
                (rp-termp term))
           (and (equal (rp-evlt (mv-nth 0 (s-c-spec-meta term)) a)
                       (rp-evlt term a))
                (valid-sc (mv-nth 0 (s-c-spec-meta term)) a)))
  :hints (("Goal"
           :cases ((quarternaryp-sum (CADR TERM)))
           :in-theory (e/d (s-c-spec-meta
                            new-sum-MERGE)
                           (bitp)))))

;; (defthm c-spec-valid-rp-meta-rulep
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state))
;;            (let ((rule (make rp-meta-rule-rec
;;                              :fnc 's-c-spec-meta
;;                              :trig-fnc 'c-spec
;;                              :dont-rw t
;;                              :valid-syntax t)))
;;              (and (valid-rp-meta-rulep rule state)
;;                   (rp-meta-valid-syntaxp-sk rule state))))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :in-theory (e/d (rp-meta-valid-syntaxp)
;;                            (rp-termp
;;                             rp-term-listp
;;                             valid-sc
;;                             )))))

;; (defthm s-spec-valid-rp-meta-rulep
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state))
;;            (let ((rule (make rp-meta-rule-rec
;;                              :fnc 's-c-spec-meta
;;                              :trig-fnc 's-spec
;;                              :dont-rw t
;;                              :valid-syntax t)))
;;              (and (valid-rp-meta-rulep rule state)
;;                   (rp-meta-valid-syntaxp-sk rule state))))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :in-theory (e/d (rp-meta-valid-syntaxp)
;;                            (rp-termp
;;                             rp-term-listp
;;                             valid-sc)))))

;; (defthm s-c-spec-valid-rp-meta-rulep
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state))
;;            (let ((rule (make rp-meta-rule-rec
;;                              :fnc 's-c-spec-meta
;;                              :trig-fnc 's-c-spec
;;                              :dont-rw t
;;                              :valid-syntax t)))
;;              (and (valid-rp-meta-rulep rule state)
;;                   (rp-meta-valid-syntaxp-sk rule state))))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :in-theory (e/d (rp-meta-valid-syntaxp)
;;                            (rp-termp
;;                             rp-term-listp
;;                             valid-sc)))))

;; (defthm c-s-spec-valid-rp-meta-rulep
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state))
;;            (let ((rule (make rp-meta-rule-rec
;;                              :fnc 's-c-spec-meta
;;                              :trig-fnc 'c-s-spec
;;                              :dont-rw t
;;                              :valid-syntax t)))
;;              (and (valid-rp-meta-rulep rule state)
;;                   (rp-meta-valid-syntaxp-sk rule state))))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :in-theory (e/d (rp-meta-valid-syntaxp)
;;                            (rp-termp
;;                             rp-term-listp
;;                             valid-sc)))))

;; (defthm sort-sum-meta-valid-rp-meta-rulep
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state))
;;            (let ((rule (make rp-meta-rule-rec
;;                              :fnc 'sort-sum-meta
;;                              :trig-fnc 'sort-sum
;;                              :dont-rw t
;;                              :valid-syntax t)))
;;              (and (valid-rp-meta-rulep rule state)
;;                   (rp-meta-valid-syntaxp-sk rule state))))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :in-theory (e/d (rp-meta-valid-syntaxp)
;;                            (rp-termp
;;                             rp-term-listp
;;                             valid-sc)))))
