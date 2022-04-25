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

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

(local
 (include-book "lemmas"))

(include-book "sum-merge-fncs")

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
   (defthm s-order-is-rp-equal
     (equal (mv-nth 1 (s-order term1 term2))
            (rp-equal term1 term2))
     :flag rp-equal)
   (defthm s-order-lst-is-rp-equal-subterms
     (equal (mv-nth 1 (s-order-lst subterm1 subterm2))
            (rp-equal-subterms subterm1 subterm2))
     :flag rp-equal-subterms)
   :hints (("goal"
            :expand ((s-order term1 term2))
            :in-theory (e/d (s-order-lst
                             s-order) ())))))

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
     (equal (RP-EVL-LST (cons x y) a)
            (cons (rp-evl x a)
                  (RP-EVL-LST y a)))
     :hints (("Goal"
              :in-theory (e/d () ())))))
  (local
   (defthm RP-EVL-OF-TRANS-LIST-opener-when-nil
     (equal (RP-EVL-LST nil a)
            nil)
     :hints (("Goal"
              :in-theory (e/d () ())))))

  (in-theory (disable rp-trans)))

(create-regular-eval-lemma -- 1 mult-formula-checks)
(create-regular-eval-lemma binary-append 2 mult-formula-checks)
(create-regular-eval-lemma binary-and 2 mult-formula-checks)
(create-regular-eval-lemma and-list 2 mult-formula-checks)

(defun sum-list-eval (lst a)
  (if (atom lst)
      0
    (sum (rp-evlt (car lst) a)
         (sum-list-eval (cdr lst) a))))

(defthm to-list*-sum-eval
  (and (equal (sum-list (rp-evl (trans-list (rp-trans-lst lst)) A))
              (sum-list-eval lst a))
       (equal (SUM-LIST (RP-EVL-lsT (RP-TRANS-LST LST)
                                    A))
              (sum-list-eval lst a)))
  :hints (("Goal"
           :do-not-induct t
           :induct (sum-list-eval lst a)
           :in-theory (e/d (sum-list
                            rp-trans
                            trans-list) ()))))

(defthm to-list*-sum-eval-2
  (implies (and ;(consp term)
            (equal (car term) 'list))
           (equal (sum-list (rp-evlt term a))
                  (sum-list-eval (cdr term) a)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (rp-trans) ()))))

(define negated-termsp ((term1 rp-termp)
                        (term2 rp-termp))
  (b* (((mv neg1 term1)
        (case-match term1 (('-- a) (mv t a)) (& (mv nil term1))))
       ((mv neg2 term2)
        (case-match term2 (('-- a) (mv t a)) (& (mv nil term2))))
       (equals
        (rp-equal term1 term2)))
    (and (not (equal neg1 neg2))
         equals)))

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
                            (term2 (cadr x)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; pp-sum-merge and s-sum-merge lemmas

(defthm rp-equal-of-ex-from-rp
  (and (equal (rp-equal (ex-from-rp term1) (ex-from-rp term2))
              (rp-equal term1 term2)))
  
  :hints (("Goal"
           :do-not-induct t
           :expand ((EX-FROM-RP-ALL (EX-FROM-RP TERM1))
                    (EX-FROM-RP-ALL TERM1)
                    (EX-FROM-RP-ALL TERM2)
                    (EX-FROM-RP-ALL (EX-FROM-RP TERM2)))
           :in-theory (e/d (rp-equal-alt-def)
                           (ex-from-rp include-fnc)))))

(defthmd rp-equal-of-ex-from-rp-reverse
  (and (implies (syntaxp (and (not (include-fnc term1 'ex-from-rp))
                              (not (include-fnc term2 'ex-from-rp))))
                (equal (rp-equal term1 term2)
                       (rp-equal (ex-from-rp term1) (ex-from-rp term2))))
       (implies (syntaxp (and (include-fnc term1 'ex-from-rp)))
                (and (equal (rp-equal (ex-from-rp term1) term2)
                            (rp-equal term1 term2))
                     (equal (rp-equal term2 (ex-from-rp term1))
                            (rp-equal term1 term2)))))
  :hints (("Goal"
           :do-not-induct t
           :expand ((EX-FROM-RP-ALL (EX-FROM-RP TERM1))
                    (EX-FROM-RP-ALL TERM1)
                    (EX-FROM-RP-ALL TERM2)
                    (EX-FROM-RP-ALL (EX-FROM-RP TERM2)))
           :in-theory (e/d (rp-equal-alt-def)
                           (ex-from-rp
                            include-fnc)))))


(defret s-order-and-negated-termsp-redef-1
  (and (equal negated-termsp
              (negated-termsp term1 term2))
       )
  :fn S-ORDER-AND-NEGATED-TERMSP
  :hints (("Goal"
           :do-not-induct t
           :expand ((RP-EQUAL (EX-FROM-RP TERM1)
                              (EX-FROM-RP TERM2))
                    (RP-EQUAL-SUBTERMS (CDR (EX-FROM-RP TERM2))
                                       (CDR (EX-FROM-RP (CADR TERM1))))
                    (RP-EQUAL (EX-FROM-RP TERM2)
                              (EX-FROM-RP (CADR TERM1)))
                    (RP-EQUAL (EX-FROM-RP TERM1)
                              (EX-FROM-RP (CADR TERM2))))
           #|:use ((:instance rp-equal-of-ex-from-rp
                            (term1 term2)
                            (term2 (cadr term1)))
                 (:instance rp-equal-of-ex-from-rp
                            (term1 term1)
                            (term2 (cadr term2))))|#
           :in-theory (e/d (rp-equal-of-ex-from-rp-reverse
                            s-order-and-negated-termsp
                            negated-termsp)
                           (rp-equal
                            ;;RP-EQUAL-SUBTERMS
                            rp-equal-of-ex-from-rp
                            NOT-INCLUDE-RP
                            INCLUDE-FNC
                            EX-FROM-RP)))))


(local
 (defthmd s-order-and-negated-termsp-redef-2-lemma
   (implies (and (equal (car term1) '--)
                 (consp term1)
                 (or (not (consp term2))
                     (not (consp (ex-from-rp term2)))))
            (and (equal (EQUAL (EX-FROM-RP TERM1)
                               (EX-FROM-RP TERM2))
                        nil)
                 (equal (EQUAL (EX-FROM-RP TERM2)
                               (EX-FROM-RP TERM1))
                        nil)))
   :hints (("Goal"
            :in-theory (e/d (EX-FROM-RP is-rp) ())))
   ))

(local
 (defthmd s-order-and-negated-termsp-redef-2-lemma2
   (implies (and (equal (car term1) '--)
                 (consp term1)
                 (consp (cdr term1))
                 (not (cddr term1))
                 (syntaxp (atom term1)))
            (and (consp (ex-from-rp term1))
                 (not (EQUAL 'QUOTE (CAR (EX-FROM-RP TERM1))))
                 (consp (cdr (ex-from-rp term1)))
                 (not (cddr (ex-from-rp term1)))
                 (EQUAL (CAR (EX-FROM-RP TERM1))
                        '--)
                 (equal (EX-FROM-RP (CADR TERM1))
                        (ex-from-rp (cadr (ex-from-rp term1))))))
   ;;:rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (EX-FROM-RP is-rp) ())))
   ))

(defret s-order-and-negated-termsp-redef-2
  (implies equals
         (rp-equal term1 term2))
  :fn S-ORDER-AND-NEGATED-TERMSP
  :hints (("Goal"
           :do-not-induct t
           :expand ((:free (x) (hide x))
                    (RP-EQUAL TERM1 TERM2)
                    (RP-EQUAL (EX-FROM-RP TERM1)
                              (EX-FROM-RP TERM2))
                    (RP-EQUAL-SUBTERMS (CDR (EX-FROM-RP TERM1))
                                       (CDR (EX-FROM-RP TERM2)))
                    )
           #|:use ((:instance rp-equal-of-ex-from-rp
                            (term1 term2)
                            (term2 (cadr term1)))
                 (:instance rp-equal-of-ex-from-rp
                            (term1 term1)
                            (term2 (cadr term2))))|#
           :in-theory (e/d (rp-equal-of-ex-from-rp-reverse
                            s-order-and-negated-termsp-redef-2-lemma
                            s-order-and-negated-termsp-redef-2-lemma2
                            s-order-and-negated-termsp
                            )
                           (rp-equal
                            
                            ;;RP-EQUAL-SUBTERMS
                            rp-equal-of-ex-from-rp
                            NOT-INCLUDE-RP
                            INCLUDE-FNC
                            ex-from-rp
                            )))))

(local
 (defthm PP-LIST-ORDER-aux-equals-redef
   (equal (mv-nth 1 (PP-LIST-ORDER-aux x y))
          (equal x y))
   :hints (("Goal"
            :in-theory (e/d (pp-list-order-aux
                             rp-equal-subterms)
                            ())))))

(local
 (defun two-cdrs (x y)
   (if (atom x)
       nil
     (if (atom y)
         nil
       (acons (car x)
              (car y)
              (two-cdrs (cdr x) (cdr y)))))))

(local
 (defthm pp-list-order-equals-redef-lemma-1
   (implies (not (equal (len x) (len y)))
            (not (rp-equal-subterms x y)))
   :hints (("Goal"
            :induct (two-cdrs x y)
            :in-theory (e/d (rp-equal-subterms) ())))))

;; (local
;;  (defthm pp-list-order-equals-redef-lemma-1.1
;;    (implies (NOT (EQUAL (LOGAPP (MV-NTH 1 (AND-LIST-HASH-AUX (CDR X)))
;;                                 (MV-NTH 0 (AND-LIST-HASH-AUX (CDR X)))
;;                                 (SUM 5 (CADR (CADDR (CAR X)))))
;;                         (LOGAPP (MV-NTH 1 (AND-LIST-HASH-AUX (CDR X)))
;;                                 (MV-NTH 0 (AND-LIST-HASH-AUX (CDR X)))
;;                                 0)))

;; (local
;;  (defthm pp-list-order-equals-redef-lemma-1.5
;;    (implies (not (equal (and-list-hash-aux x)
;;                         (and-list-hash-aux y)))
;;             (not (rp-equal-subterms x y)))
;;    :hints (("goal"
;;             :induct (two-cdrs x y)
;;             :do-not-induct t
;;             :expand ((RP-EQUAL (CAR X) (CAR Y))
;;                      (RP-EQUAL-SUBTERMS X Y)
;;                      (RP-EQUAL-SUBTERMS (CDR X) (CDR Y))
;;                      (RP-EQUAL-SUBTERMS (CDR (CAR X))
;;                                         (CDR (CAR Y))))
;;             :in-theory (e/d (rp-equal-subterms
;;                              rp-equal
;;                              is-rp
;;                              EX-FROM-RP
;;                              AND-LIST-HASH-AUX
;;                              and-list-hash)
;;                             (floor logapp IFIX-OPENER FLOOR))))))

;; (skip-proofs
;;  (local
;;  (defthm pp-list-order-equals-redef-lemma-2
;;    (implies (not (equal (and-list-hash x)
;;                         (and-list-hash y)))
;;             (not (rp-equal-subterms x y)))
;;    :hints (("goal"
;;             :induct (two-cdrs x y)
;;             :do-not-induct t
;;             :in-theory (e/d (rp-equal-subterms
;;                              AND-LIST-HASH-AUX
;;                              and-list-hash)
;;                             (floor logapp IFIX-OPENER FLOOR)))))))

(local
 (defthm PP-LIST-ORDER-equals-redef
   (equal (mv-nth 1 (PP-LIST-ORDER x y))
          (equal x y))
   :hints (("Goal"
            :in-theory (e/d (pp-list-order
                             rp-equal-subterms)
                            ())))))

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

(defthmd rp-evlt-of-ex-from-rp-reverse
  (implies (syntaxp (or (atom term)
                        (not (equal (car term) 'ex-from-rp))))
           (EQUAL (RP-EVL (RP-TRANS TERM) A)
                  (RP-EVL (RP-TRANS (EX-FROM-RP TERM)) A))))

(local
 (defthm and-list-of-single-argument
   (equal (and-list hash (list single-e))
          (bit-fix single-e))
   :hints (("Goal"
            :in-theory (e/d (and-list
                             AND$) ())))))


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
           :in-theory (e/d* (pp-order
                             (:REWRITE
                              REGULAR-RP-EVL-OF_AND-LIST_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             rp-evlt-of-ex-from-rp-reverse
                             and$-is-and-list)
                            (rp-termp
                             rp-evlt-of-ex-from-rp
                             nth
                             (:REWRITE
                              RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT)
                             (:REWRITE RP-EVL-OF-RP-EQUAL-LOOSE)
;;                             (:REWRITE ACL2::O-P-O-INFP-CAR)
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
                             ;;RP-EVL-OF-QUOTE
                             len)))))




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
            :in-theory (e/d* (pp-order-and-negated-termsp
                              regular-rp-evl-of_--_when_mult-formula-checks)
                             (rp-evlt-of-rp-equal
                              rp-equal))))))

(local
 (defthm when-ex-from-rp-is-0
   (implies (EQUAL (EX-FROM-RP x) ''0)
            (equal (rp-evlt x a) 0))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance rp-evlt-of-ex-from-rp
                             (term x)))
            :in-theory (e/d ()
                            (rp-evlt-of-ex-from-rp))))))

(progn
  (defthm pp-sum-merge-aux-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state))
             (and (equal (sum-list (rp-evlt-lst (pp-sum-merge-aux term1 term2)
                                                a))
                         (sum (sum-list (rp-evlt-lst term1 a))
                              (sum-list (rp-evlt-lst term2 a))))
                  (equal (sum-list-eval (pp-sum-merge-aux term1 term2) a)
                         (sum (sum-list (rp-evlt-lst term1 a))
                              (sum-list (rp-evlt-lst term2 a))))))
    :hints (("Goal"
             :do-not-induct t
             :expand ((RP-TRANS (CONS 'LIST* TERM2))
                      (:free (x y)
                             (sum-list (cons x y)))
                      (RP-TRANS (CONS 'LIST* TERM1)))
             :induct (pp-sum-merge-aux term1 term2 )
             :in-theory (e/d (pp-sum-merge-aux)
                             (rp-termp)))))

  (defthm pp-sum-merge-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state))
             (equal (sum-list (rp-evlt (pp-sum-merge term1 term2) a))
                    (sum (sum-list (rp-evlt term1 a))
                         (sum-list (rp-evlt term2 a)))))
    :hints (("Goal"
             :do-not-induct t
             :expand ()
             :use ((:instance pp-sum-merge-aux-correct
                              (term1 (cdr term1))
                              (term2 (cdr term2))))
             :in-theory (e/d (pp-sum-merge)
                             (rp-trans
                              pp-sum-merge-aux-correct)))))

  (defthm pp-sum-merge-correct-with-sk
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state))
             (rp-evlt-equiv  `(sum-list ,(pp-sum-merge term1 term2))
                             `(binary-sum (sum-list ,term1)
                                          (sum-list ,term2))))
    :hints (("Goal"
             :in-theory (e/d () ())))))

(progn
  (defthm s-sum-merge-aux-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  ;;(rp-term-listp term1)
                  ;;(rp-term-listp term2)
                  )
             (and
              (equal (sum-list (rp-evlt-lst (s-sum-merge-aux term1 term2) a))
                     (sum (sum-list (rp-evlt `(list . ,term1) a))
                          (sum-list (rp-evlt `(list . ,term2) a))))
              (equal (sum-list-eval (s-sum-merge-aux term1 term2) a)
                     (sum (sum-list (rp-evlt `(list . ,term1) a))
                          (sum-list (rp-evlt `(list . ,term2) a))))))
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
                  ;;(rp-termp term1)
                  ;;(rp-termp term2)
                  )
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
                  ;;(rp-termp term1)
                  ;;(rp-termp term2)
                  )
             (rp-evlt-equiv `(sum-list ,(s-sum-merge term1 term2))
                            `(binary-sum (sum-list ,term1)
                                         (sum-list ,term2))))))




(defthm valid-sc-of-create-list-instance
  (equal (valid-sc (create-list-instance lst) a)
         (valid-sc-subterms lst a))
  :hints (("Goal"
           :expand (VALID-SC (CONS 'LIST LST) A)
           :in-theory (e/d (create-list-instance
                            IS-IF
                            IS-rp)
                           ()))))

(progn
  (defthm pp-sum-merge-aux-valid-sc-subterms
    (implies (and (valid-sc-subterms lst1 a)
                  (valid-sc-subterms lst2 a))
             (valid-sc-subterms (pp-sum-merge-aux lst1 lst2) a))
    :hints (("Goal"
             :induct (pp-sum-merge-aux
                      lst1 lst2)
             :do-not-induct t
             :in-theory (e/d (pp-sum-merge-aux) ()))))

  (defthm pp-sum-merge-valid-sc
    (implies (and (valid-sc term1 a)
                  (valid-sc term2 a))
             (valid-sc (pp-sum-merge term1 term2) a))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; s-fix-args lemmas

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

(defthm rp-equal-of-ex-from-rp-2
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
;(rp-term-listp pp-lst)
                  )
             (and (equal (m2 (sum (sum-list-eval (s-fix-pp-args-aux pp-lst) a)
                                  other))
                         (m2 (sum (sum-list-eval pp-lst a) other)))
                  (equal (m2 (sum other
                                  (sum-list-eval (s-fix-pp-args-aux pp-lst) a)))
                         (m2 (sum (sum-list-eval pp-lst a) other)))
                  (equal (m2 (sum-list-eval (s-fix-pp-args-aux pp-lst) a))
                         (s 0 (rp-evlt-lst pp-lst a) 0))))
    :hints (("Goal"
             :do-not-induct t
             :expand ((:free (x y)
                             (sum-list (cons x y))))
             :induct (s-fix-pp-args-aux pp-lst)
             :in-theory (e/d* (s-fix-pp-args-aux
                               (:REWRITE
                                REGULAR-RP-EVL-OF_--_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                               rp-evlt-of-ex-from-rp-reverse)
                              (rp-evlt-of-ex-from-rp)))))

  (defthmd s-fix-args-correct-lemma1
    (Implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  ;;(rp-term-listp lst)
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
                  ;;(rp-termp term)
                  )
             (and (equal (m2 (sum (sum-list (rp-evlt (s-fix-args term) a))
                                  (sum-list c/d)))
                         (s 0 (rp-evlt term a) c/d))
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
                ;;(rp-termp term)
                )
           (and (rp-evlt-equiv `(m2 (binary-sum (sum-list ,(s-fix-args term))
                                                (sum-list c/d)))
                               `(s '0 ,term c/d))
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
                ;;(rp-term-listp pp-lst)
                )
           (valid-sc-subterms (s-fix-pp-args-aux pp-lst) a))
  :hints (("Goal"
           :do-not-induct t
           :induct (s-fix-pp-args-aux pp-lst)
           :in-theory (e/d (s-fix-pp-args-aux) ()))))

(defthm s-fix-args-valid-sc
  (implies (and (valid-sc pp a)
                ;;(rp-termp pp)
                )
           (valid-sc (s-fix-args pp) a))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (s-fix-args
                            is-if is-rp) ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; and c/d-fix-pp-args
;; and c/d-fix-s-args lemmas

(defthmd c-fix-arg-aux-correct-lemma
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
;(rp-term-listp pp-lst)
                )
           (b* (((mv coughed result)
                 (c-fix-arg-aux pp-lst neg-flag)))
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
                           (sum-list (cons x y))))
           :induct (c-fix-arg-aux pp-lst neg-flag)
           :in-theory (e/d* (c-fix-arg-aux
                             times2
                             rp-evlt-of-ex-from-rp-reverse
                             sum-comm-1-loop-stopper
                             sum-comm-2-loop-stopper
                             (:REWRITE
                              REGULAR-RP-EVL-OF_--_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             ;;sum-of-repeated-to-times2
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

(defthm c-fix-arg-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (b* (((mv coughed result)
                 (c-fix-arg-aux pp-lst neg-flag)))
             (equal
              (sum (sum-list-eval coughed a)
                   (sum-list-eval coughed a)
                   (sum-list-eval result a)
                   rest)
              (sum (sum-list-eval pp-lst a) rest))))
  :hints (("Goal"
           :use ((:instance c-fix-arg-aux-correct-lemma))
           :in-theory (e/d (times2) (c-fix-arg-aux-correct-lemma)))))

(defthm c-fix-arg-aux-with-cond-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (b* (((mv coughed result)
                 (c-fix-arg-aux-with-cond pp-lst neg-flag cond)))
             (equal
              (sum (sum-list-eval coughed a)
                   (sum-list-eval coughed a)
                   (sum-list-eval result a)
                   rest)
              (sum (sum-list-eval pp-lst a) rest))))
  :hints (("Goal"
           :use ((:instance c-fix-arg-aux-correct))
           :in-theory (e/d (c-fix-arg-aux-with-cond) (c-fix-arg-aux-correct-lemma)))))

(defthmd c/d-fix-arg-aux-correct-dummy-lemma1
  (Implies (force (integerp x))
           (equal (EQUAL x (SUM a (-- c)))
                  (equal (sum c x) (ifix a))))
  :hints (("Goal"
           :in-theory (e/d (sum --)
                           (+-is-SUM)))))

(defthmd f2-of-times2-reverse-2
  (implies (syntaxp (or (atom a)
                        (not (equal (car a) '--))))
           (EQUAL (SUM A (F2 b))
                  (F2 (SUM (TIMES2 A) B)))))

;; (defthmd d2-of-times2-reverse
;;   (implies (syntaxp (or (atom a)
;;                         (and (not (equal (car a) 'd2))
;;                              (not (equal (car a) '--)))))
;;            (EQUAL (SUM A (d2 b))
;;                   (d2 (SUM (TIMES2 A) B)))))

(defthm c-fix-pp-args-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
;(rp-termp pp)
                )
           (b* (((mv coughed result)
                 (c-fix-pp-args pp )))
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
           :use ((:instance c-fix-arg-aux-correct-lemma
                            (neg-flag t)
                            (pp-lst (cdr pp))))
           :in-theory (e/d (c-fix-pp-args)
                           (c-fix-arg-aux-correct-lemma)))))

(defthm c-fix-pp-args-correct-2
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
;(rp-termp pp)
                )
           (b* (((mv coughed result)
                 (c-fix-pp-args pp )))
             (and (equal
                   (sum (sum-list (rp-evlt coughed a))
                        (sum-list (rp-evlt coughed a))
                        (sum-list (rp-evlt result a))
                        rest)
                   (sum (sum-list (rp-evlt pp a)) rest))
                  )))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance c-fix-arg-aux-correct
                            (neg-flag t)
                            (pp-lst (cdr pp))))
           :in-theory (e/d (c-fix-pp-args)
                           (c-fix-arg-aux-correct)))))

(defthm c-fix-pp-args-correct-on-f2
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
;(rp-termp pp)
                )
           (b* (((mv coughed result)
                 (c-fix-pp-args pp )))
             (and (equal
                   (sum  (sum-list (rp-evlt coughed a))
                         (f2 (sum-list (rp-evlt result a))))
                   (f2 (sum-list (rp-evlt pp a))))
                  (equal
                   (sum   (f2 (sum-list (rp-evlt result a)))
                          (sum-list (rp-evlt coughed a)))
                   (f2 (sum-list (rp-evlt pp a))))
                  (equal
                   (sum  (sum-list (rp-evlt coughed a))
                         (f2 (sum-list (rp-evlt result a)))
                         rest)
                   (sum (f2 (sum-list (rp-evlt pp a)))
                        rest))
                  (equal
                   (sum  (f2 (sum-list (rp-evlt result a)))
                         (sum-list (rp-evlt coughed a))
                         rest)
                   (sum (f2 (sum-list (rp-evlt pp a)))
                        rest)))))
  :hints (("Goal"
           :in-theory (e/d (f2-of-times2-reverse)
                           (f2-of-times2)))))

;; #|(defthm c/d-fix-pp-args-correct-wit-sk
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state)
;;                 (rp-termp pp))
;;            (b* (((mv coughed result)
;;                  (c/d-fix-pp-args pp limit)))
;;              (and (rp-evlt-equiv
;;                    `(binary-sum (times2 (sum-list ,coughed))
;;                                 (binary-sum (sum-list ,result)
;;                                             ,rest))
;;                    `(binary-sum (sum-list ,pp) ,rest))
;;                   (rp-evlt-equiv
;;                    `(binary-sum  (sum-list ,result)
;;                                  (binary-sum (times2 (sum-list ,coughed))
;;                                              ,rest))
;;                    `(binary-sum (sum-list ,pp) ,rest))
;;                   (rp-evlt-equiv
;;                    `(binary-sum  (sum-list ,result)
;;                                  (times2 (sum-list ,coughed)))
;;                    `(sum-list ,pp))
;;                   (rp-evlt-equiv
;;                    `(binary-sum  (times2 (sum-list ,coughed))
;;                                  (sum-list ,result))
;;                    `(sum-list ,pp)))))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :in-theory (e/d ()
;;                            (c/d-fix-arg-aux-correct-lemma)))))||#

(defthm c-fix-s-args-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
;(rp-termp pp)
                )
           (b* (((mv coughed result)
                 (c-fix-s-args pp)))
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
           :use ((:instance c-fix-arg-aux-correct-lemma
                            (neg-flag t)
                            (pp-lst (cdr pp))))
           :in-theory (e/d (c-fix-s-args)
                           (c-fix-arg-aux-correct-lemma)))))

(defthm c-fix-s-args-correct-2
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
;(rp-termp pp)
                )
           (b* (((mv coughed result)
                 (c-fix-s-args pp)))
             (and (equal
                   (sum (sum-list (rp-evlt coughed a))
                        (sum-list (rp-evlt coughed a))
                        (sum-list (rp-evlt result a))
                        rest)
                   (sum (sum-list (rp-evlt pp a)) rest))
                  )))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance c-fix-arg-aux-correct
                            (neg-flag t)
                            (pp-lst (cdr pp))))
           :in-theory (e/d (c-fix-s-args)
                           (c-fix-arg-aux-correct)))))

;; #|(defthm c/d-fix-s-args-correct-with-sk
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state)
;;                 (rp-termp pp))
;;            (b* (((mv coughed result)
;;                  (c/d-fix-s-args pp)))
;;              (and (rp-evlt-equiv
;;                    `(binary-sum (times2 (sum-list ,coughed))
;;                                 (BINARY-sum (sum-list ,result)
;;                                             ,rest))
;;                    `(binary-sum (sum-list ,pp) ,rest))
;;                   (rp-evlt-equiv
;;                    `(binary-sum (sum-list ,result)
;;                                 (binary-sum (times2 (sum-list ,coughed))
;;                                             ,rest))
;;                    `(binary-sum (sum-list ,pp) ,rest))
;;                   (rp-evlt-equiv
;;                    `(binary-sum  (sum-list ,result)
;;                                  (times2 (sum-list ,coughed)))
;;                    `(sum-list ,pp))
;;                   (rp-evlt-equiv
;;                    `(binary-sum  (times2 (sum-list ,coughed))
;;                                  (sum-list ,result))
;;                    `(sum-list ,pp)))))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :in-theory (e/d ()
;;                            (c/d-fix-arg-aux-correct-lemma)))))||#

;; ;; about evenpi:
;; (defthmd c/d-fix-arg-aux-retains-evenpi
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state)
;;                 (rp-term-listp pp-lst))
;;            (b* (((mv & result)
;;                  (c/d-fix-arg-aux pp-lst neg-flag limit)))
;;              (and (equal (evenpi (sum-list-eval result a))
;;                          (evenpi (sum-list-eval pp-lst a))))))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :use ((:instance c/d-fix-arg-aux-correct-lemma))
;;            :in-theory (e/d ()
;;                            (rp-evlt-of-ex-from-rp
;;                             rp-evlt-of-rp-equal
;;                             (:DEFINITION RP-TERMP)
;;                             (:DEFINITION FALIST-CONSISTENT)
;;                             (:REWRITE DEFAULT-CDR)
;;                             (:DEFINITION EX-FROM-RP)
;;                             (:REWRITE DEFAULT-CAR)
;;                             (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
;;                             F2-OF-TIMES2
;;                             rp-trans)))
;;           ("Subgoal *1/3"
;;            :use ((:instance rp-evlt-of-rp-equal
;;                             (term1 (EX-FROM-RP (CAR PP-LST)))
;;                             (term2 (EX-FROM-RP (CADR PP-LST))))))))

;; (defthm c/d-fix-pp-args-retains-evenpi
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state)
;;                 (rp-termp pp))
;;            (b* (((mv ?coughed result)
;;                  (c/d-fix-pp-args pp limit)))
;;              (equal (evenpi (sum-list (rp-evlt result a)))
;;                     (evenpi (sum-list (rp-evlt pp a))))))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :use ((:instance c/d-fix-arg-aux-retains-evenpi
;;                             (neg-flag t)
;;                             (pp-lst (cdr pp))))
;;            :in-theory (e/d (c/d-fix-pp-args)
;;                            (c/d-fix-arg-aux-retains-evenpi)))))

;; (defthm c/d-fix-pp-args-retains-evenpi-with-other
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state)
;;                 (rp-termp pp))
;;            (b* (((mv ?coughed result)
;;                  (c/d-fix-pp-args pp limit)))
;;              (and (equal (evenpi (sum other (sum-list (rp-evlt result a))))
;;                          (evenpi (sum other (sum-list (rp-evlt pp a)))))
;;                   (equal (evenpi (sum (sum-list (rp-evlt result a)) other))
;;                          (evenpi (sum (sum-list (rp-evlt pp a)) other)))
;;                   (equal (evenpi (sum other1 other2 (sum-list (rp-evlt result a))))
;;                          (evenpi (sum other1 other2 (sum-list (rp-evlt pp a))))))))
;;   :hints (("Goal"
;;            :use ((:instance evenpi-with-other
;;                             (x (sum-list (rp-evlt (MV-NTH 1 (C/D-FIX-PP-ARGS PP
;;                                                                              LIMIT)) a)))
;;                             (y (sum-list (rp-evlt pp a)))
;;                             (z other))
;;                  (:instance evenpi-with-other
;;                             (x (sum-list (rp-evlt (MV-NTH 1 (C/D-FIX-PP-ARGS PP
;;                                                                              LIMIT)) a)))
;;                             (y (sum-list (rp-evlt pp a)))
;;                             (z (sum other1 other2))))
;;            :in-theory (e/d () ()))))

;; (defthm c/d-fix-s-args-retains-evenpi
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state)
;;                 (rp-termp pp))
;;            (b* (((mv ?coughed result)
;;                  (c/d-fix-s-args pp)))
;;              (equal (evenpi (sum-list (rp-evlt result a)))
;;                     (evenpi (sum-list (rp-evlt pp a))))))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :use ((:instance c/d-fix-arg-aux-retains-evenpi
;;                             (neg-flag nil)
;;                             (limit (expt 2 30))
;;                             (pp-lst (cdr pp))))
;;            :in-theory (e/d (c/d-fix-s-args)
;;                            (c/d-fix-arg-aux-retains-evenpi)))))

;; (defthm c/d-fix-s-args-retains-evenpi-with-other
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state)
;;                 (rp-termp pp))
;;            (b* (((mv ?coughed result)
;;                  (c/d-fix-s-args pp)))
;;              (and (equal (evenpi (sum other (sum-list (rp-evlt result a))))
;;                          (evenpi (sum other (sum-list (rp-evlt pp a)))))
;;                   (equal (evenpi (sum (sum-list (rp-evlt result a)) other))
;;                          (evenpi (sum (sum-list (rp-evlt pp a)) other)))
;;                   (equal (evenpi (sum other1 other2 (sum-list (rp-evlt result a))))
;;                          (evenpi (sum other1 other2 (sum-list (rp-evlt pp a)))))
;;                   (equal (evenpi (sum other1 other2 other3 (sum-list (rp-evlt result a))))
;;                          (evenpi (sum other1 other2 other3 (sum-list (rp-evlt pp a)))))
;;                   (equal (evenpi (sum other1 other2 other3 other4 (sum-list (rp-evlt result a))))
;;                          (evenpi (sum other1 other2 other3 other4 (sum-list (rp-evlt pp a))))))))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :use ((:instance evenpi-with-other
;;                             (x (sum-list (rp-evlt (MV-NTH 1 (C/D-FIX-s-ARGS PP)) a)))
;;                             (y (sum-list (rp-evlt pp a)))
;;                             (z other))
;;                  (:instance evenpi-with-other
;;                             (x (sum-list (rp-evlt (MV-NTH 1 (C/D-FIX-s-ARGS PP)) a)))
;;                             (y (sum-list (rp-evlt pp a)))
;;                             (z (sum other1 other2)))
;;                  (:instance evenpi-with-other
;;                             (x (sum-list (rp-evlt (MV-NTH 1 (C/D-FIX-s-ARGS PP)) a)))
;;                             (y (sum-list (rp-evlt pp a)))
;;                             (z (sum other1 other2 other3)))
;;                  (:instance evenpi-with-other
;;                             (x (sum-list (rp-evlt (MV-NTH 1 (C/D-FIX-s-ARGS PP)) a)))
;;                             (y (sum-list (rp-evlt pp a)))
;;                             (z (sum other1 other2 other3 other4))))
;;            :in-theory (e/d ()
;;                            ()))))

;; ;; (defthm c/d-fix-arg-aux-correct-for-f2
;; ;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;; ;;                 (mult-formula-checks state)
;; ;;                 (rp-term-listp pp-lst))
;; ;;            (b* (((mv coughed result)
;; ;;                  (c/d-fix-arg-aux pp-lst neg-flag limit)))
;; ;;              (and (equal
;; ;;                    (f2 (sum (sum-list-eval result a) rest))
;; ;;                    (sum (-- (sum-list-eval coughed a))
;; ;;                         (f2 (sum (sum-list-eval pp-lst a)
;; ;;                                  rest))))
;; ;;                   (equal
;; ;;                    (f2 (sum-list-eval result a))
;; ;;                    (sum (-- (sum-list-eval coughed a))
;; ;;                         (f2 (sum-list-eval pp-lst a)))))))
;; ;;   :hints (("Goal"
;; ;;            :do-not-induct t
;; ;;            :expand ((:free (x y)
;; ;;                            (sum-list (cons x y)))
;; ;;                     (:free (x y)
;; ;;                            (RP-EVL-OF-TRANS-LIST (cons x y) a)))
;; ;;            :use ((:instance c/d-fix-arg-aux-correct-lemma))
;; ;;            :in-theory (e/d (times2
;; ;;                             c/d-fix-arg-aux-correct-dummy-lemma1
;; ;;                             rp-evlt-of-ex-from-rp-reverse
;; ;;                             f2-of-times2-reverse)
;; ;;                            (rp-evlt-of-ex-from-rp
;; ;;                             rp-evlt-of-rp-equal
;; ;;                             (:DEFINITION RP-TERMP)
;; ;;                             (:DEFINITION FALIST-CONSISTENT)
;; ;;                             (:REWRITE DEFAULT-CDR)
;; ;;                             (:DEFINITION EX-FROM-RP)
;; ;;                             (:REWRITE DEFAULT-CAR)
;; ;;                             (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
;; ;;                             F2-OF-TIMES2
;; ;;                             rp-trans)))))

;; ;; (defthm c/d-fix-arg-aux-correct-for-d2
;; ;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;; ;;                 (mult-formula-checks state)
;; ;;                 (rp-term-listp pp-lst))
;; ;;            (b* (((mv coughed result)
;; ;;                  (c/d-fix-arg-aux pp-lst neg-flag limit)))
;; ;;              (and (equal
;; ;;                    (d2 (sum (sum-list-eval result a) rest))
;; ;;                    (sum (-- (sum-list-eval coughed a))
;; ;;                         (d2 (sum (sum-list-eval pp-lst a)
;; ;;                                  rest))))
;; ;;                   (equal
;; ;;                    (d2 (sum-list-eval result a))
;; ;;                    (sum (-- (sum-list-eval coughed a))
;; ;;                         (d2 (sum-list-eval pp-lst a)))))))
;; ;;   :hints (("Goal"
;; ;;            :do-not-induct t
;; ;;            :expand ((:free (x y)
;; ;;                            (sum-list (cons x y)))
;; ;;                     (:free (x y)
;; ;;                            (RP-EVL-OF-TRANS-LIST (cons x y) a)))
;; ;;            :use ((:instance c/d-fix-arg-aux-correct-lemma))
;; ;;            :in-theory (e/d (times2
;; ;;                             c/d-fix-arg-aux-correct-dummy-lemma1
;; ;;                             rp-evlt-of-ex-from-rp-reverse
;; ;;                             d2-of-times2-reverse)
;; ;;                            (rp-evlt-of-ex-from-rp
;; ;;                             rp-evlt-of-rp-equal
;; ;;                             (:DEFINITION RP-TERMP)
;; ;;                             (:DEFINITION FALIST-CONSISTENT)
;; ;;                             (:REWRITE DEFAULT-CDR)
;; ;;                             (:DEFINITION EX-FROM-RP)
;; ;;                             (:REWRITE DEFAULT-CAR)
;; ;;                             (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
;; ;;                             d2-OF-TIMES2
;; ;;                             rp-trans)))))

;; ;; (defthm c/d-fix-pp-args-correct-for-f2
;; ;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;; ;;                 (mult-formula-checks state)
;; ;;                 (rp-termp pp))
;; ;;            (b* (((mv coughed result)
;; ;;                  (c/d-fix-pp-args pp limit)))
;; ;;              (equal
;; ;;               (f2 (sum (sum-list (rp-evlt result a)) rest))
;; ;;               (sum (-- (sum-list (rp-evlt coughed a)))
;; ;;                    (f2 (sum (sum-list (rp-evlt pp a))
;; ;;                             rest))))))
;; ;;   :hints (("Goal"
;; ;;            :do-not-induct t
;; ;;            :use ((:instance c/d-fix-arg-aux-correct-for-f2
;; ;;                             (neg-flag t)
;; ;;                             (pp-lst (cdr pp))))
;; ;;            :in-theory (e/d (c/d-fix-pp-args)
;; ;;                            (c/d-fix-arg-aux-correct-for-f2)))))

;; ;; (defthm c/d-fix-pp-args-correct-for-d2
;; ;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;; ;;                 (mult-formula-checks state)
;; ;;                 (rp-termp pp))
;; ;;            (b* (((mv coughed result)
;; ;;                  (c/d-fix-pp-args pp limit)))
;; ;;              (equal
;; ;;               (d2 (sum (sum-list (rp-evlt result a)) rest))
;; ;;               (sum (-- (sum-list (rp-evlt coughed a)))
;; ;;                    (d2 (sum (sum-list (rp-evlt pp a))
;; ;;                             rest))))))
;; ;;   :hints (("Goal"
;; ;;            :do-not-induct t
;; ;;            :use ((:instance c/d-fix-arg-aux-correct-for-d2
;; ;;                             (neg-flag t)
;; ;;                             (pp-lst (cdr pp))))
;; ;;            :in-theory (e/d (c/d-fix-pp-args)
;; ;;                            (c/d-fix-arg-aux-correct-for-d2)))))

;; ;; (defthm c/d-fix-s-args-correct-for-f2
;; ;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;; ;;                 (mult-formula-checks state)
;; ;;                 (rp-termp pp))
;; ;;            (b* (((mv coughed result)
;; ;;                  (c/d-fix-s-args pp)))
;; ;;              (equal
;; ;;               (f2 (sum (sum-list (rp-evlt result a)) rest))
;; ;;               (sum (-- (sum-list (rp-evlt coughed a)))
;; ;;                    (f2 (sum (sum-list (rp-evlt pp a))
;; ;;                             rest))))))
;; ;;   :hints (("Goal"
;; ;;            :do-not-induct t
;; ;;            :use ((:instance c/d-fix-arg-aux-correct-for-f2
;; ;;                             (neg-flag nil)
;; ;;                             (pp-lst (cdr pp))
;; ;;                             (limit (expt 2 30))))
;; ;;            :in-theory (e/d (c/d-fix-s-args)
;; ;;                            (c/d-fix-arg-aux-correct-for-f2)))))

;; ;; (defthm c/d-fix-s-args-correct-for-d2
;; ;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;; ;;                 (mult-formula-checks state)
;; ;;                 (rp-termp pp))
;; ;;            (b* (((mv coughed result)
;; ;;                  (c/d-fix-s-args pp)))
;; ;;              (equal
;; ;;               (d2 (sum (sum-list (rp-evlt result a)) rest))
;; ;;               (sum (-- (sum-list (rp-evlt coughed a)))
;; ;;                    (d2 (sum (sum-list (rp-evlt pp a))
;; ;;                             rest))))))
;; ;;   :hints (("Goal"
;; ;;            :do-not-induct t
;; ;;            :use ((:instance c/d-fix-arg-aux-correct-for-d2
;; ;;                             (neg-flag nil)
;; ;;                             (pp-lst (cdr pp))
;; ;;                             (limit (expt 2 30))))
;; ;;            :in-theory (e/d (c/d-fix-s-args)
;; ;;                            (c/d-fix-arg-aux-correct-for-d2)))))

(defthm c-fix-arg-aux-valid-sc-subterms
  (implies (and (valid-sc-subterms pp-lst a)
                ;;(rp-term-listp pp-lst)
                )
           (b* (((mv coughed result)
                 (c-fix-arg-aux pp-lst neg-flag)))
             (and (valid-sc-subterms coughed a)
                  (valid-sc-subterms result a))))
  :hints (("Goal"
           :do-not-induct t
           :induct (c-fix-arg-aux pp-lst neg-flag)
           :in-theory (e/d (c-fix-arg-aux)
                           (nfix
                            ACL2::ZP-OPEN
                            zp
                            atom
                            (:DEFINITION VALID-SC)
                            (:DEFINITION QUOTEP)
                            rp-trans
                            rp-termp
                            rp-equal)))))

(defthm c-fix-arg-aux-with-cond-valid-sc-subterms
  (implies (and (valid-sc-subterms pp-lst a))
           (b* (((mv coughed result)
                 (c-fix-arg-aux-with-cond pp-lst neg-flag cond)))
             (and (valid-sc-subterms coughed a)
                  (valid-sc-subterms result a))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (c-fix-arg-aux-with-cond)
                           ()))))

(defthm c-fix-pp-args-valid-sc
  (implies (and (valid-sc term a)
                ;;(rp-termp term)
                )
           (b* (((mv coughed result)
                 (c-fix-pp-args term)))
             (and (valid-sc coughed a)
                  (valid-sc result a))))
  :hints (("Goal"
           :in-theory (e/d (c-fix-pp-args
                            is-if is-rp) ()))))

(defthm c-fix-s-args-valid-sc
  (implies (and (valid-sc term a)
                ;;(rp-termp term)
                )
           (b* (((mv coughed result)
                 (c-fix-s-args term)))
             (and (valid-sc coughed a)
                  (valid-sc result a))))
  :hints (("Goal"
           :in-theory (e/d (c-fix-s-args
                            is-if is-rp) ()))))


(local
 (defthm dummy-m2-lemma1
   (equal (equal (m2 (sum a x))
                 (m2 (sum z a y)))
          (equal (m2 x)
                 (m2 (sum z y))))))

(local
 (defthmd dummy-m2-lemma2
   (implies (rp-equal x y)
            (equal (m2 (sum (rp-evlt x a) z2 (rp-evlt y a) z1))
                   (m2 (sum z1 z2))))))
                   
(local
 (defthm dummy-m2-lemma3
   (equal (m2 (sum x y (-- a) z))
          (m2 (sum x y a z)))))

(defret sum-merge-lst-for-s-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (equal (m2 (sum-list-eval merged-s-lst a))
                       (m2 (sum (sum-list-eval s1-lst a)
                                (sum-list-eval s2-lst a))))
                (equal (m2 (sum (sum-list-eval merged-s-lst a) other))
                       (m2 (sum (sum-list-eval s1-lst a)
                                (sum-list-eval s2-lst a)
                                other)))))
  :fn sum-merge-lst-for-s
  :hints (("Goal"
           :do-not-induct t
           :induct (sum-merge-lst-for-s s1-lst s2-lst)
           :in-theory (e/d* (sum-merge-lst-for-s
                             dummy-m2-lemma2
                             EX-FROM---
                             regular-rp-evl-of_--_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_--_when_mult-formula-checks)
                            (rp-trans
                             INCLUDE-FNC)))))

(defret sum-merge-lst-for-s-valid-sc
  (implies (and (valid-sc-subterms s1-lst a)
                (valid-sc-subterms s2-lst a))
           (valid-sc-subterms merged-s-lst a))
  :fn sum-merge-lst-for-s
  :hints (("Goal"
           :do-not-induct t
           :induct (sum-merge-lst-for-s s1-lst s2-lst)
           :in-theory (e/d* (sum-merge-lst-for-s
                             EX-FROM---
                             is-rp is-if)
                            (rp-trans
                             INCLUDE-FNC)))))



(local
 (defthm dummy-m2-lemma4
   (implies (equal (m2 x) (m2 (sum y z)))
            (equal (m2 (sum x other))
                   (m2 (sum y other z))))))

(defret pp-sum-merge-lst-for-s-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (equal (m2 (sum-list-eval merged-pp-lst a))
                       (m2 (sum (sum-list-eval pp1-lst a)
                                (sum-list-eval pp2-lst a))))
                (equal (m2 (sum (sum-list-eval merged-pp-lst a) other))
                       (m2 (sum (sum-list-eval pp1-lst a)
                                (sum-list-eval pp2-lst a)
                                other)))))
  :fn pp-sum-merge-lst-for-s
  :hints (("Goal"
           :do-not-induct t
           :induct (pp-sum-merge-lst-for-s pp1-lst pp2-lst)
           :in-theory (e/d* (pp-order-equals-implies
                             pp-sum-merge-lst-for-s
                             dummy-m2-lemma2
                             EX-FROM---
                             regular-rp-evl-of_--_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_--_when_mult-formula-checks)
                            (rp-trans
                             EX-FROM-SYNP-LEMMA1
                             RP-TRANS-WHEN-LIST
                             DEFAULT-CDR
                             ;;SUM-LIST-EVAL
                             SUM-OF-NEGATED-ELEMENTS
                             RP-EQUAL
                             cons-equal
                             ex-from-rp
                             INCLUDE-FNC)))))


(defret pp-sum-merge-lst-for-s-valid-sc
  (implies (and (valid-sc-subterms pp1-lst a)
                (valid-sc-subterms pp2-lst a))
           (valid-sc-subterms merged-pp-lst a))
  :fn pp-sum-merge-lst-for-s
  :hints (("Goal"
           :do-not-induct t
           :induct (pp-sum-merge-lst-for-s pp1-lst pp2-lst)
           :in-theory (e/d* (pp-sum-merge-lst-for-s
                             EX-FROM---
                             is-rp is-if)
                            (rp-trans
                             INCLUDE-FNC)))))


(defthm sum-list-eval-of-odds-and-evens
  (equal (sum (sum-list-eval (odds lst) a)
              (sum-list-eval (evens lst) a))
         (sum-list-eval lst a)))

(defthm pp-sum-sort-lst-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state))
           (equal (sum-list-eval (pp-sum-sort-lst pp-lst) a)
                  (sum-list-eval pp-lst a)))
  :hints (("Goal"
           :in-theory (e/d (pp-sum-sort-lst)
                           (evens odds)))))

(defthm valid-sc-subterms-of-odds-and-evens
  (implies (valid-sc-subterms lst a)
           (and (valid-sc-subterms (odds lst) a)
                (valid-sc-subterms (evens lst) a))))

(defthm pp-sum-sort-lst-valid-sc
  (implies (valid-sc-subterms pp-lst a)
           (valid-sc-subterms (pp-sum-sort-lst pp-lst) a))
  :hints (("Goal"
           :in-theory (e/d (pp-sum-sort-lst) ()))))


(defthm s-sum-sort-lst-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state))
           (equal (sum-list-eval (s-sum-sort-lst s-lst) a)
                  (sum-list-eval s-lst a)))
  :hints (("Goal"
           :in-theory (e/d (s-sum-sort-lst)
                           (evens odds)))))

(defthm s-sum-sort-lst-valid-sc
  (implies (valid-sc-subterms s-lst a)
           (valid-sc-subterms (s-sum-sort-lst s-lst) a))
  :hints (("Goal"
           :in-theory (e/d (s-sum-sort-lst) ()))))


(create-regular-eval-lemma s-c-res 3 mult-formula-checks)

(defthm sum-list-eval-of-append-wog
  (implies (and (mult-formula-checks state)
                (rp-evl-meta-extract-global-facts))
           (equal (sum-list-eval (append-wog x y) a)
                  (sum (sum-list (rp-evlt-lst x a))
                       (sum-list (rp-evlt-lst y a)))))
  :hints (("Goal"
           :induct (append-wog x y)
           :do-not-induct t
           :in-theory (e/d (append-wog) ()))))


(local
 (defthm --of-sum
   (equal (-- (sum a b))
          (sum (-- a)
               (-- b)))
   :hints (("Goal"
            :in-theory (e/d (-- sum)
                            (+-is-SUM))))))



(defthm  sum-list-eval-of-negate-lst
  (implies (and (mult-formula-checks state)
                (rp-evl-meta-extract-global-facts))
           (equal (sum-list-eval (negate-lst lst enabled) a)
                  (if enabled
                      (-- (sum-list-eval lst a))
                    (sum-list-eval lst a))))
  :hints (("Goal"
           :induct (negate-lst-aux lst)
           :do-not-induct t
           :in-theory (e/d (NEGATE-LST
                            regular-rp-evl-of_--_when_mult-formula-checks
                            regular-rp-evl-of_--_when_mult-formula-checks_with-ex-from-rp
                            negate-lst-aux)
                           ()))))



