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

;;(include-book "pp-flatten-meta-correct")

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
  :hints (("goal"
           :expand ((rp-evlt-equiv x x)
                    (rp-evlt-equiv x z)
                    (rp-evlt-equiv y x))
           :use ((:instance rp-evlt-equiv-necc
                            (term1 x)
                            (term2 y)
                            (a (rp-evlt-equiv-witness x z)))
                 (:instance rp-evlt-equiv-necc
                            (term1 y)
                            (term2 z)
                            (a (rp-evlt-equiv-witness x z)))
                 (:instance rp-evlt-equiv-necc
                            (term1 x)
                            (term2 y)
                            (a (rp-evlt-equiv-witness y x))))
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

(defthm s-order-main-is-rp-equal
  (equal (mv-nth 1 (s-order-main term1 term2))
         (rp-equal term1 term2))
  :hints (("Goal"
           :in-theory (e/d (s-order-main) ()))))

(local
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

   (in-theory (disable rp-trans))))

(progn
  (create-regular-eval-lemma -- 1 mult-formula-checks)
  (create-regular-eval-lemma times 2 mult-formula-checks)
  (create-regular-eval-lemma binary-append 2 mult-formula-checks)
  (create-regular-eval-lemma binary-and 2 mult-formula-checks)
  (create-regular-eval-lemma and-list 2 mult-formula-checks)
  (create-regular-eval-lemma and-times-list 3 mult-formula-checks))

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

;; (define negated-termsp ((term1 rp-termp)
;;                         (term2 rp-termp))
;;   (b* (((mv neg1 term1)
;;         (case-match term1 (('-- a) (mv t a)) (& (mv nil term1))))
;;        ((mv neg2 term2)
;;         (case-match term2 (('-- a) (mv t a)) (& (mv nil term2))))
;;        (equalsp
;;         (rp-equal term1 term2)))
;;     (and (not (equal neg1 neg2))
;;          equalsp)))

;; (defthm sum-of-negated-terms
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state)
;;                 (negated-termsp x y))
;;            (and (equal (sum (rp-evlt x a) (rp-evlt y a))
;;                        0)
;;                 (equal (sum (rp-evlt x a) (rp-evlt y a) z)
;;                        (ifix z))))
;;   :hints (("Goal"
;;            :in-theory (e/d* (negated-termsp
;;                              (:REWRITE REGULAR-RP-EVL-OF_--_WHEN_MULT-FORMULA-CHECKS)
;;                              sum
;;                              --)
;;                             (rp-equal-cnt
;;                              ex-from-rp
;;                              rp-equal
;;                              UNICITY-OF-0
;;                              rp-evl-of-rp-equal
;;                              +-is-SUM))
;;            :use ((:instance rp-evlt-of-rp-equal
;;                             (term1 x)
;;                             (term2 (cadr y)))
;;                  (:instance rp-evlt-of-rp-equal
;;                             (term1 y)
;;                             (term2 (cadr x)))))))

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

#|(defret s-order-and-negated-termsp-redef-1
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
EX-FROM-RP)))))|#

#|(local
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
))|#

#|(local
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
))|#

#|(defret s-order-and-negated-termsp-redef-2
(implies equalsp
(rp-equal term1 term2))
:fn s-order-and-negated-termsp
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
not-include-rp
include-fnc
ex-from-rp
)))))|#

(local
 (defthm pp-list-order-aux-equalsp-redef
   (equal (mv-nth 1 (pp-list-order-aux x y))
          (rp-equal-subterms x y))
   :hints (("goal"
            :expand ((pp-list-order-aux x x)
                     (pp-list-order-aux x y))
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
 (defthm pp-list-order-equalsp-redef-lemma-1
   (implies (not (equal (len x) (len y)))
            (not (rp-equal-subterms x y)))
   :hints (("Goal"
            :induct (two-cdrs x y)
            :in-theory (e/d (rp-equal-subterms) ())))))

;; (local
;;  (defthm pp-list-order-equalsp-redef-lemma-1.1
;;    (implies (NOT (EQUAL (LOGAPP (MV-NTH 1 (AND-LIST-HASH-AUX (CDR X)))
;;                                 (MV-NTH 0 (AND-LIST-HASH-AUX (CDR X)))
;;                                 (SUM 5 (CADR (CADDR (CAR X)))))
;;                         (LOGAPP (MV-NTH 1 (AND-LIST-HASH-AUX (CDR X)))
;;                                 (MV-NTH 0 (AND-LIST-HASH-AUX (CDR X)))
;;                                 0)))

;; (local
;;  (defthm pp-list-order-equalsp-redef-lemma-1.5
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
;;  (defthm pp-list-order-equalsp-redef-lemma-2
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

(defthm len-compare-redef
  (equal (len-compare x y)
         (> (len x) (len y)))
  :hints (("Goal"
           :induct (len-compare x y)
           :expand ((LEN X))
           :in-theory (e/d (len-compare
                            LEN)
                           (+-is-SUM)))))

(local
 (defthm pp-list-order-equalsp-redef
   (implies (and (booleanp x1) (booleanp y1))
            (equal (mv-nth 1 (pp-list-order x y x1 y1))
                   (rp-equal-subterms x y)))
   :hints (("goal"
            :in-theory (e/d (pp-list-order
                             rp-equal-subterms)
                            ())))))

(local
 (defthm rp-trans-when-list
   (implies (and (equal (car lst) 'list)
                 (consp lst))
            (equal (rp-trans lst)
                   (trans-list (rp-trans-lst (cdr lst)))))
   :hints (("goal"
            :expand (rp-trans lst)
            :in-theory (e/d () ())))
   :rule-classes :rewrite))

(defthmd rp-evlt-of-ex-from-rp-reverse
  (implies (and (syntaxp (or (atom term)
                             (and (not (equal (car term) 'ex-from-rp))
                                  (not (equal (car term) 'quote))))))
           (EQUAL (RP-EVL (RP-TRANS TERM) A)
                  (RP-EVL (RP-TRANS (EX-FROM-RP TERM)) A))))

(local
 (defthm and-list-of-single-argument
   (equal (and-list hash (list single-e))
          (bit-fix single-e))
   :hints (("Goal"
            :in-theory (e/d (and-list
                             AND$) ())))))

(local
 (defthm when-ex-from-rp-is-quoted
   (implies (equal (car x) 'quote)
            (and (equal (car (ex-from-rp x)) 'quote)))
   :rule-classes :forward-chaining))

(local
 (defthm rp-evlt-of-quoted
   (implies (equal (car x) 'quote)
            (equal (rp-evlt x a)
                   (cadr x)))))

(local
 (defthm and-list-equiv-when-ifix-are-equiv
   (implies (equal (ifix x)
                   (ifix y))
            (equal (equal (and-list x a)
                          (and-list y a))
                   t))
   :hints (("Goal"
            :in-theory (e/d (and-list) ())))))

(defthmd pp-order-equalsp-implies
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
           :use ((:instance rp-evlt-of-rp-equal
                            (term1 x)
                            (term2 y)))
           :in-theory (e/d* (pp-order
                             (:REWRITE
                              REGULAR-RP-EVL-OF_AND-LIST_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_AND-times-LIST_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
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

#|(local
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
:use ((:instance pp-order-equalsp-implies
(x (cadr x))
(y y))
(:instance pp-order-equalsp-implies
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
rp-equal))))))|#

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

(local
 (defthm rp-evl-to-of-create-list-instance
   (equal (sum-list (rp-evlt (create-list-instance lst) a))
          (sum-list (rp-evlt-lst lst a)))
   :hints (("Goal"
            :in-theory (e/d (create-list-instance
                             sum-list
;binary-sum
                             )
                            (SUM-OF-IFIX))))))

(defthm create-times-instance-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (equal (ifix (rp-evlt (create-times-instance coef term) a))
                       (times coef (rp-evlt term a)))
                (implies (integerp (rp-evlt term a))
                         (equal (rp-evlt (create-times-instance coef term) a)
                                (times coef (rp-evlt term a))))
                (equal (ifix (rp-evlt (ex-from-rp (create-times-instance coef term)) a))
                       (times coef (rp-evlt term a)))
                (implies (integerp (rp-evlt term a))
                         (equal (rp-evlt (ex-from-rp (create-times-instance coef term)) a)
                                (times coef (rp-evlt term a))))

                (equal (sum (rp-evlt (ex-from-rp (create-times-instance coef term)) a) other)
                       (sum (times coef (rp-evlt term a)) other))
                (equal (sum other (rp-evlt (ex-from-rp (create-times-instance coef term)) a))
                       (sum (times coef (rp-evlt term a)) other))
                (equal (sum (rp-evlt (create-times-instance coef term) a) other)
                       (sum (times coef (rp-evlt term a)) other))
                (equal (sum other (rp-evlt (create-times-instance coef term) a))
                       (sum (times coef (rp-evlt term a)) other))
                ))
  :hints (("goal"
           :in-theory (e/d (times create-times-instance) ()))))

(defthm sum-list-eval-of-cons-with-times
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (sum-list-eval (cons-with-times coef term lst) a)
                  (sum (times coef (rp-evlt term a))
                       (sum-list-eval lst a))))
  :hints (("Goal"
           :in-theory (e/d (times
                            CONS-WITH-TIMES)
                           ()))))

(defthm times-of-summed-coef
  (equal (times (sum a b) term)
         (sum (times a term)
              (times b term)))
  :hints (("Goal"
           :in-theory (e/d (sum times)
                           (+-is-SUM)))))

(defret get-pp-and-coef-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (times coef (rp-evlt res-term a))
                  (ifix (rp-evlt term a))))
  :fn get-pp-and-coef
  :hints (("Goal"
           :in-theory (e/d* (regular-rp-evl-of_times_when_mult-formula-checks
                             times sum
                             get-pp-and-coef)
                            (+-is-sum)))))

(defret get-pp-and-coef-correct-2
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (equal (rp-evlt (mv-nth 1 (get-pp-and-coef term1)) a)
                       (rp-evlt (mv-nth 1 (get-pp-and-coef term2)) a)))
           (equal (times (mv-nth 0 (get-pp-and-coef term1))
                         (rp-evlt (mv-nth 1 (get-pp-and-coef term2))
                                  a))
                  (ifix (rp-evlt term1 a))))
  :fn get-pp-and-coef
  :hints (("Goal"
           :in-theory (e/d* (regular-rp-evl-of_times_when_mult-formula-checks
                             times sum
                             get-pp-and-coef)
                            (+-is-sum)))))

(defret get-pp-and-coef-correct-when-coef-is-0
  (implies (and (equal coef 0)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (rp-evlt term a) 0))
  :fn get-pp-and-coef
  :hints (("Goal"
           :in-theory (e/d (times
                            regular-rp-evl-of_times_when_mult-formula-checks
                            get-pp-and-coef)
                           ()))))

(defret get-pp-and-coef-correct-when-res-term-is-0
  (implies (and (or (equal res-term ''0)
                    (equal (ex-from-rp res-term) ''0))
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (rp-evlt term a) 0))
  :fn get-pp-and-coef
  :hints (("Goal"
           :in-theory (e/d (times
                            regular-rp-evl-of_times_when_mult-formula-checks
                            get-pp-and-coef)
                           ()))))

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
             :in-theory (e/d (or* pp-order-equalsp-implies
                                  pp-sum-merge-aux)
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
             :in-theory (e/d (or* S-ORDER-MAIN s-sum-merge-aux)
                             (rp-termp)))))

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

(local
 (defthm is-equals-of-others
   (implies (not (equal (car term) 'equals))
            (not (is-equals term )))
   :hints (("Goal"
            :in-theory (e/d (is-equals) ())))))

(defthm valid-sc-of-create-list-instance
  (equal (valid-sc (create-list-instance lst) a)
         (valid-sc-subterms lst a))
  :hints (("Goal"
           :expand (VALID-SC (CONS 'LIST LST) A)
           :in-theory (e/d (create-list-instance
                            IS-IF
                            IS-rp)
                           ()))))

(defthm valid-sc-create-times-instance
  (implies (and (valid-sc term a))
           (valid-sc (create-times-instance coef term)
                     a))
  :hints (("Goal"
           :in-theory (e/d (create-times-instance) ()))))

(defret valid-sc-subterms-cons-with-times
  (implies (and (valid-sc term a)
                (valid-sc-subterms rest a))
           (valid-sc-subterms res-lst a))
  :fn cons-with-times
  :hints (("Goal"
           :in-theory (e/d (CONS-WITH-TIMES) ()))))

(defret valid-sc-get-pp-and-coef
  (implies (valid-sc term a)
           (valid-sc res-term a))
  :fn get-pp-and-coef
  :hints (("goal"
           :in-theory (e/d (get-pp-and-coef) ()))))

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
  :hints (("goal"
           :do-not-induct t
           :expand ((rp-equal (ex-from-rp term1) term2)
                    (rp-equal term1 (ex-from-rp term2)))
           :in-theory (e/d () (rp-equal-is-symmetric)))))

(local
 (in-theory (disable evenp)))

(local
 (defret m2-of-odd-coeffed-term
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state)
                 (not (evenp coef)))
            (and (equal (m2 (sum (rp-evlt term a) other))
                        (m2 (sum (rp-evlt res-term a) other)))
                 (equal (m2 (sum (rp-evlt (ex-from-rp term) a) other))
                        (m2 (sum (rp-evlt res-term a) other)))))
   :fn get-pp-and-coef
   :hints (("goal"
            :do-not-induct t
            :in-theory (e/d (regular-rp-evl-of_times_when_mult-formula-checks
                             get-pp-and-coef
                             ifix)
                            (acl2::evenp-and-oddp-as-logcar))))))

(local
 (defret m2-of-even-coeffed-term
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state)
                 (evenp coef))
            (and (equal (m2 (sum (rp-evlt term a) other))
                        (m2 other))
                 (equal (m2 (sum (rp-evlt (ex-from-rp term) a) other))
                        (m2 other))))
   :fn get-pp-and-coef
   :hints (("goal"
            :do-not-induct t
            :in-theory (e/d (regular-rp-evl-of_times_when_mult-formula-checks
                             get-pp-and-coef
                             ifix)
                            (acl2::evenp-and-oddp-as-logcar))))))

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

(defthm rp-evlt-of-ex-from-rp-when-times
  (implies (and (case-match term (('times & &) t))
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (rp-evlt (ex-from-rp term) a)
                  (times (rp-evlt (cadr term) a)
                         (rp-evlt (caddr term) a)))))

(local
 (defthmd sum-of-non-integerp
   (implies (not (integerp x))
            (equal (sum other x)
                   (ifix other)))
   :hints (("Goal"
            :in-theory (e/d (sum ifix) (+-is-sum))))))

(local
 (defthm dummy-sum-lemma-with-4-and-2
   (equal (equal (sum x y z a) (sum k a))
          (equal (sum x y z) (ifix k)))))

(defthmd c-fix-arg-aux-correct-lemma
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (b* (((mv coughed result)
                 (c-fix-arg-aux pp-lst)))
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
           :induct (c-fix-arg-aux pp-lst)
           :do-not '(generalize)
           :in-theory (e/d* (;;CREATE-TIMES-INSTANCE
                             EVENP

                             GET-PP-AND-COEF
                             sum-of-non-integerp
                             ifix times
                             c-fix-arg-aux
                             times2
                             rp-evlt-of-ex-from-rp-reverse
                             sum-comm-1-loop-stopper
                             sum-comm-2-loop-stopper
                             regular-rp-evl-of_times_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_times_when_mult-formula-checks
                             ;;sum-of-repeated-to-times2
                             )
                            (INCLUDE-FNC

                             rp-evlt-of-ex-from-rp
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
                 (c-fix-arg-aux pp-lst)))
             (equal
              (sum (sum-list-eval coughed a)
                   (sum-list-eval coughed a)
                   (sum-list-eval result a)
                   rest)
              (sum (sum-list-eval pp-lst a) rest))))
  :hints (("Goal"
           :use ((:instance c-fix-arg-aux-correct-lemma))
           :in-theory (e/d (times2) (c-fix-arg-aux-correct-lemma)))))

(defthmd c-fix-arg-aux-correct-singled-out
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (b* (((mv coughed result)
                 (c-fix-arg-aux pp-lst)))
             (equal
              (sum-list-eval result a)
              (sum (sum-list-eval pp-lst a)
                   (-- (sum-list-eval coughed a))
                   (-- (sum-list-eval coughed a))))))
  :hints (("Goal"
           :use ((:instance c-fix-arg-aux-correct
                            (rest 0)))
           :in-theory (e/d () (c-fix-arg-aux-correct)))))

(defthm c-fix-arg-aux-with-cond-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (b* (((mv coughed result)
                 (c-fix-arg-aux-with-cond pp-lst cond)))
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
                            (pp-lst (cdr pp))))
           :in-theory (e/d ( c-fix-pp-args)
                           (C-FIX-ARG-AUX-CORRECT-SINGLED-OUT
                            c-fix-arg-aux-correct-lemma)))))

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
                            (pp-lst (cdr pp))))
           :in-theory (e/d (c-fix-pp-args)
                           (C-FIX-ARG-AUX-CORRECT-SINGLED-OUT
                            c-fix-arg-aux-correct)))))

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
                            (pp-lst (cdr pp))))
           :in-theory (e/d (c-fix-s-args)
                           (C-FIX-ARG-AUX-CORRECT-SINGLED-OUT
                            c-fix-arg-aux-correct-lemma)))))

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
                            (pp-lst (cdr pp))))
           :in-theory (e/d (c-fix-s-args)
                           (C-FIX-ARG-AUX-CORRECT-SINGLED-OUT
                            c-fix-arg-aux-correct)))))

(defthm c-fix-arg-aux-valid-sc-subterms
  (implies (and (valid-sc-subterms pp-lst a)
                ;;(rp-term-listp pp-lst)
                )
           (b* (((mv coughed result)
                 (c-fix-arg-aux pp-lst)))
             (and (valid-sc-subterms coughed a)
                  (valid-sc-subterms result a))))
  :hints (("Goal"
           :do-not-induct t
           :induct (c-fix-arg-aux pp-lst)
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
                 (c-fix-arg-aux-with-cond pp-lst cond)))
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

(local
 (defthm dummy-m2-lemma4
   (implies (equal (m2 x1) (m2 (sum x2 x3)))
            (equal (equal (m2 (sum a x1))
                          (m2 (sum x2 b x3)))
                   (equal (m2 a) (m2 b))))
   :hints (("Goal"
            :in-theory (e/d (m2-to-m2-chain)
                            ())))))

(local
 (defthm dummy-m2-lemma5
   (implies (equal (m2 x1) (m2 (sum x2 x3)))
            (equal (equal (m2 x1)
                          (m2 (sum x2 b x3)))
                   (equal 0 (m2 b))))
   :hints (("Goal"
            :in-theory (e/d ()
                            ())))))

(local
 (defthm dummy-m2-lemma6
   (implies (equal (m2 x1) (m2 (sum x2 x3)))
            (equal (equal (m2 x1)
                          (m2 (sum a x2 b x3)))
                   (equal 0 (m2 (sum a b)))))
   :hints (("Goal"
            :use ((:instance dummy-m2-lemma5
                             (b (m2-chain a b))))
            :in-theory (e/d (m2-to-m2-chain)
                            (dummy-m2-lemma5))))))

(defretd m2-of-term-when-GET-PP-AND-COEF
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (implies (evenp coef)
                         (and (equal (m2 (rp-evlt term a))
                                     0)))
                (implies (not (evenp coef))
                         (equal (m2 (rp-evlt res-term a))
                                (m2 (rp-evlt term a))))))
  :fn GET-PP-AND-COEF
  :hints (("Goal"
           :in-theory (e/d (get-pp-and-coef
                            IFIX
                            regular-rp-evl-of_times_when_mult-formula-checks_with-ex-from-rp
                            regular-rp-evl-of_times_when_mult-formula-checks)
                           ()))))

(defthm evenp-of-sum-of-evenps
  (implies (and (evenp x)
                (evenp y))
           (evenp (sum x y)))
  :hints (("goal"
           :in-theory (e/d (sum ifix evenp) (+-is-sum)))))

(defthm when-m2-of-an-m2-arg-is-zero
  (implies (equal (m2 a) 0)
           (and (equal (m2 (sum x a))
                       (m2 x)))))


(defret sum-merge-lst-for-s-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (equal (m2 (sum-list-eval merged-s-lst a))
                       (m2 (sum (sum-list-eval s1-lst a)
                                (sum-list-eval s2-lst a))))
                (equal (m2 (sum (sum-list-eval merged-s-lst a) other))
                       (m2 (sum (sum-list-eval s1-lst a)
                                (sum-list-eval s2-lst a)
                                other)))
                (equal (m2 (sum other (sum-list-eval merged-s-lst a)))
                       (m2 (sum (sum-list-eval s1-lst a)
                                (sum-list-eval s2-lst a)
                                other)))))
  :fn sum-merge-lst-for-s
  :hints (("Goal"
           :do-not-induct t
           :induct (sum-merge-lst-for-s s1-lst s2-lst)
           :in-theory (e/d* (;;S-ORDER-MAIN
                             ;;rp-evlt-of-ex-from-rp-reverse
                             ;;GET-PP-AND-COEF
                             ;;m2-of-term-when-GET-PP-AND-COEF
                             or*
                             sum-merge-lst-for-s
                             dummy-m2-lemma2
                             ;;EX-FROM---
                             regular-rp-evl-of_times_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_times_when_mult-formula-checks)
                            (;;M2-OF-ODD-COEFFED-TERM
                             ;;rp-evlt-of-ex-from-rp
                             rp-trans
                             RP-EQUAL-IMPLIES-EQUAL-RP-EVLT-1
                             rp-equal
                             rp-evlt-of-rp-equal
                             INCLUDE-FNC
                             RP-EQUAL-IS-AN-EQUIVALENCE)))
          (and stable-under-simplificationp
               '(:use ((:instance rp-evlt-of-rp-equal
                                  (term1 (MV-NTH 1 (GET-PP-AND-COEF (CAR S1-LST))))
                                  (term2 (MV-NTH 1 (GET-PP-AND-COEF (CAR S2-LST)))))
                       (:instance m2-of-term-when-get-pp-and-coef
                                  (term (CAR S2-LST)))
                       (:instance m2-of-term-when-get-pp-and-coef
                                  (term (CAR S1-LST))))))))

(defret sum-merge-lst-for-s-valid-sc
  (implies (and (valid-sc-subterms s1-lst a)
                (valid-sc-subterms s2-lst a))
           (valid-sc-subterms merged-s-lst a))
  :fn sum-merge-lst-for-s
  :hints (("Goal"
           :do-not-induct t
           :induct (sum-merge-lst-for-s s1-lst s2-lst)
           :in-theory (e/d* (sum-merge-lst-for-s
                             is-rp is-if)
                            (rp-trans
                             INCLUDE-FNC)))))

(local
 (defthm dummy-m2-lemma8
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
                                other)))
                (equal (m2 (sum other (sum-list-eval merged-pp-lst a)))
                       (m2 (sum (sum-list-eval pp1-lst a)
                                (sum-list-eval pp2-lst a)
                                other)))))
  :fn pp-sum-merge-lst-for-s
  :hints (("Goal"
           :do-not-induct t
           :induct (pp-sum-merge-lst-for-s pp1-lst pp2-lst)
           :in-theory (e/d* (pp-order-equalsp-implies
                             pp-sum-merge-lst-for-s
                             dummy-m2-lemma2
                             regular-rp-evl-of_times_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_times_when_mult-formula-checks)
                            (rp-trans
                             EX-FROM-SYNP-LEMMA1
                             RP-TRANS-WHEN-LIST
                             DEFAULT-CDR
                             ;;SUM-LIST-EVAL
                             SUM-OF-NEGATED-ELEMENTS
                             RP-EQUAL
                             cons-equal
                             ex-from-rp
                             INCLUDE-FNC)))
          (and stable-under-simplificationp
               '(:use ((:instance rp-evlt-of-rp-equal
                                  (term1 (MV-NTH 1 (GET-PP-AND-COEF (CAR pp1-LST))))
                                  (term2 (MV-NTH 1 (GET-PP-AND-COEF (CAR pp2-LST)))))
                       (:instance m2-of-term-when-get-pp-and-coef
                                  (term (CAR pp2-LST)))
                       (:instance m2-of-term-when-get-pp-and-coef
                                  (term (CAR pp1-LST))))))))

(defret pp-sum-merge-lst-for-s-valid-sc
  (implies (and (valid-sc-subterms pp1-lst a)
                (valid-sc-subterms pp2-lst a))
           (valid-sc-subterms merged-pp-lst a))
  :fn pp-sum-merge-lst-for-s
  :hints (("Goal"
           :do-not-induct t
           :induct (pp-sum-merge-lst-for-s pp1-lst pp2-lst)
           :in-theory (e/d* (pp-sum-merge-lst-for-s
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

(defthm pp-sum-sort-lst-correct-alt
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (sum-list (rp-evlt-lst (pp-sum-sort-lst pp-lst) a))
                  (sum-list (rp-evlt-lst pp-lst a))))
  :hints (("Goal"
           :use ((:instance pp-sum-sort-lst-correct))
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

#|(local
 (defthm --of-sum
   (equal (-- (sum a b))
          (sum (-- a)
               (-- b)))
   :hints (("Goal"
            :in-theory (e/d (-- sum)
                            (+-is-SUM))))))|#


(local
 (defthmd -of-sum
   (equal (- (sum x y))
          (sum (- x) (- y)))
   :hints (("Goal"
            :in-theory (e/d (ifix sum) (+-is-SUM))))))

(defthm sum-of-neg-non-integer
  (implies (not (integerp x))
           (and (equal (sum (- x) other)
                       (sum other))
                (equal (sum other (- x))
                       (sum other))))
  :hints (("Goal"
           :in-theory (e/d (sum ifix) (+-is-SUM)))))

(defthm  sum-list-eval-of-negate-lst
  (implies (and (mult-formula-checks state)
                (rp-evl-meta-extract-global-facts))
           (equal (sum-list-eval (negate-lst lst enabled) a)
                  (if enabled
                      (times -1 (sum-list-eval lst a))
                    (sum-list-eval lst a))))
  :hints (("Goal"
           :induct (negate-lst-aux lst)
           :do-not-induct t
           :in-theory (e/d (;;GET-PP-AND-COEF
                            ;;times
                            ifix
                            -of-sum
                            NEGATE-LST
                            regular-rp-evl-of_--_when_mult-formula-checks
                            regular-rp-evl-of_--_when_mult-formula-checks_with-ex-from-rp
                            negate-lst-aux)
                           ()))))
