; RP-REWRITER

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
(include-book "../extract-formula")

(include-book "proof-functions")
(local (include-book "proof-function-lemmas"))
(local (include-book "aux-function-lemmas"))
(local (include-book "rp-equal-lemmas"))

(local
 ;;LOCAL FUNCITONS FOR LOCAL LEMMAS
 (encapsulate
   nil
   (defmacro valid-rulep-with-a (rule a)
     `(valid-rulep-sk-body ,rule ,a))

   (defun valid-rulesp-with-a (rules a)
     (if (atom rules)
         t
       (and (rule-syntaxp (car rules))
            (valid-rulep-with-a (car rules) a)
            (valid-rulesp-with-a (cdr rules) a))))

   (defthm correctness-of-formulas-to-rules
     (implies (eval-and-all formulas a)
              (valid-rulesp-with-a (formulas-to-rules rune rule-new-synp formulas) a))
     :hints (("Goal"
              :in-theory (e/d (formulas-to-rules
                               valid-rulesp-with-a
                               )
                              (rule-syntaxp)))))

   (defun-sk eval-and-all-sk ( formulas)
     (forall a
             (eval-and-all formulas a)))

   (defun valid-rulesp-induct (x)
     (if (atom x)
         nil
       (cons (car x) (valid-rulesp-induct (cdr x)))))

   (defun-sk valid-formula-sk (formula)
     (forall a
             (rp-evl formula a)))

   (defun-sk valid-rulesp-sk (rules)
     (forall a
             (valid-rulesp-with-a rules a)))))

(encapsulate
  nil

  (local
   (defthm rp-evl-lst-not-to-equal-nil-list
     (equal (eval-and-all (not-to-equal-nil-list new-terms) a)
            (eval-and-all new-terms a))
     :hints (("Goal"
              :in-theory (e/d (not-to-equal-nil-list) ())))))

  (local
   (defthm rp-evl-lst-of-if-to-and-list
     (implies (rp-evl term a)
              (eval-and-all (if-to-and-list term) a))
     :hints (("Goal"
              :in-theory (e/d (if-to-and-list) ())))))

  (local
   (defthm consp-if-to-and-list
     (implies t;term
              (consp (if-to-and-list term)))
     :hints (("Goal"
              :in-theory (e/d (if-to-and-list) ())))))

  (local
   (defthm consp-not-to-equal-nil-list
     (implies (consp x)
              (consp (not-to-equal-nil-list x)))
     :hints (("Goal"
              :in-theory (e/d (not-to-equal-nil-list) ())))))

  (local
   (defthm make-rule-better-aux1-lemma1
     (implies (and (eval-and-all qs a))
              (eval-and-all (make-rule-better-aux1 p qs) a))))

  (local
   (defthm make-rule-better-aux1-lemma2
     (implies (and (not (rp-evl p a))
                   (consp qs))
              (eval-and-all (make-rule-better-aux1 p qs) a))))

  (defthm
    rp-evl-of-beta-search-reduce
    (implies
     (pseudo-termp term)
     (equal (rp-evl (beta-search-reduce term limit) a)
            (rp-evl term a)))
    :hints (("Goal"
             :use ((:functional-instance
                    eval-of-beta-search-reduce
                    (acl2::beta-eval rp-evl)
                    (acl2::beta-eval-list rp-evl-lst)))
             :in-theory (e/d (rp-evl-of-fncall-args) ()))))

  (defthm correctness-of-make-formula-better
    (implies (and (pseudo-termp formula)
                  (rp-evl formula a))
             (eval-and-all (make-formula-better formula) a))
    :hints (("Goal"
             :use ((:instance rp-evl-of-beta-search-reduce
                              (term formula)
                              (limit *big-number*)))
             :in-theory (e/d ()
                             (beta-search-reduce
                              rp-evl-of-beta-search-reduce))))
    :otf-flg t))

(local
 (encapsulate
   nil
   (local
    (defthm lemma201
      (IMPLIES (AND (CONSP RULES)
                    (NOT (RULE-SYNTAXP (CAR RULES))))
               (NOT (VALID-RULESP-SK RULES)))
      :hints (("Goal"
               :in-theory (e/d (VALID-RULESP-SK) (RULE-SYNTAXP))))))

   (local
    (defthm lemma202
      (IMPLIES (NOT (CONSP RULES))
               (VALID-RULESP-SK RULES))))

   (local
    (defthm lemma203
      (IMPLIES (AND (CONSP RULES)
                    (NOT (VALID-RULEP-SK (CAR RULES))))
               (NOT (VALID-RULESP-SK RULES)))
      :hints (("Goal"
               :use ((:instance VALID-RULESP-SK-necc
                                (a (VALID-RULEP-SK-WITNESS (CAR RULES)))))
               :in-theory (e/d (VALID-RULEP-SK ) (
                                                  VALID-RULESP-SK
                                                  VALID-RULEP-SK-body
                                                  VALID-RULEP-SK-necc))))))

   (local
    (defthm lemma204
      (IMPLIES (AND (CONSP RULES)
                    (NOT (VALID-RULESP-SK (CDR RULES))))
               (NOT (VALID-RULESP-SK RULES)))
      :hints (("Goal"
               :expand (VALID-RULESP-SK (CDR RULES))
               :use ((:instance VALID-RULESP-SK-necc
                                (a (VALID-RULEsP-SK-WITNESS (CDR RULES)))))
               :in-theory (e/d ( )
                               (VALID-RULESP-SK

                                VALID-RULESP-SK-necc
                                rule-syntaxp
                                VALID-RULEP-SK-body
                                VALID-RULEP-SK-necc))))))

   (local
    (defthm lemma205
      (IMPLIES (AND (CONSP RULES)
                    (RULE-SYNTAXP (CAR RULES))
                    (VALID-RULEP-SK (CAR RULES))
                    (VALID-RULESP (CDR RULES))
                    (VALID-RULESP-SK (CDR RULES)))
               (VALID-RULESP-SK RULES))
      :hints (("Goal"
               :expand ((VALID-RULESP-SK rules)
                        )
               :use ((:instance VALID-RULESP-SK-necc
                                (a (VALID-RULEsP-SK-WITNESS rules))
                                (rules (cdr rules)))
                     (:instance VALID-RULEP-SK-necc
                                (a (VALID-RULEsP-SK-WITNESS rules))
                                (rule (car rules))))
               :in-theory (e/d ( )
                               (VALID-RULESP-SK
                                VALID-RULEP-SK

                                VALID-RULESP-SK-necc
                                rule-syntaxp
                                VALID-RULEP-SK-body
                                VALID-RULEP-SK-necc))))))

   (defthmd valid-rulesp-alt-def
     (iff (valid-rulesp rules)
          (valid-rulesp-sk rules))
     :hints (("Goal"
              :use ()
              :in-theory (e/d (valid-rulesp)
                              (rp-lhs
                               (:ELIM CAR-CDR-ELIM)
                               valid-rulep-sk
                               valid-rulep-sk-body
                               valid-rulesp-sk
                               valid-rulep-sk-necc
                               rp-rhs
                               RP-IFF-FLAG
                               rp-hyp
                               rule-syntaxp)))))))

(encapsulate
  nil

  (local
   (defthm correctness-of-formulas-to-rules2
     (implies (eval-and-all-sk formulas)
              (valid-rulesp-with-a (formulas-to-rules rune rule-new-synp formulas) a))
     :hints (("Goal"
              :use ((:instance correctness-of-formulas-to-rules)
                    (:instance EVAL-AND-ALL-SK-NECC))
              :in-theory (e/d (valid-rulesp
                               valid-rulesp-with-a)
                              (rule-syntaxp
                               formulas-to-rules
                               correctness-of-formulas-to-rules
                               eval-and-all-sk
                               ))))))

  (local
   (defthm lemma10
     (implies (eval-and-all-sk formulas)
              (eval-and-all-sk (cdr formulas)))
     :otf-flg t
     :hints (("Goal"
              :expand ((EVAL-AND-ALL-SK NIL)
                       (eval-and-all-sk (cdr formulas)))
              :use ((:instance eval-and-all-sk-necc
                               (a (EVAL-AND-ALL-SK-WITNESS (CDR FORMULAS)))))
              :in-theory (e/d () (eval-and-all-sk-necc
                                  eval-and-all-sk))))))

  (local
   (defthm correctness-of-formulas-to-rules3
     (implies (eval-and-all-sk formulas)
              (valid-rulesp (formulas-to-rules rune rule-new-synp formulas)))
     :otf-flg t
     :hints (("Goal"
              :induct  (valid-rulesp-induct formulas)
              :in-theory (e/d (valid-rulesp
                               valid-rulesp-alt-def
                               valid-rulesp-with-a)
                              (rule-syntaxp
                               formulas-to-rules
                               correctness-of-formulas-to-rules
                               eval-and-all-sk))))))

  (defthm custom-rewrite-with-meta-extract-is-correct
    (implies (and ;(custom-rewrite-with-meta-extract rule-name state)
              (rp-evl-meta-extract-global-facts :state state))
             (valid-rulesp (custom-rewrite-with-meta-extract rule-name rule-new-synp state)))
    :hints (("goal"
;:cases ((custom-rewrite-with-meta-extract rule-name state))
             :in-theory (e/d (valid-rulep-sk-necc
                              rp-evl-meta-extract-formula)
                             (formulas-to-rules
                              valid-rulesp
                              valid-rulesp-alt-def
                              make-formula-better
                              meta-extract-formula
                              get-rune-name
                              rule-syntaxp)))))

  (in-theory (disable custom-rewrite-with-meta-extract)))

(encapsulate
  nil

  (local
   (use-measure-lemmas t))

  (make-flag attach-sc :defthm-macro-name defthm-attach-sc)

  (defthm-attach-sc
    (defthm rp-evl-of-attach-sc
      (equal (rp-evl (attach-sc term sc-type sc-term) a)
             (rp-evl term a))
      :flag attach-sc)
    (defthm rp-evl-lst-of-attach-sc-lst
      (equal (rp-evl-lst (attach-sc-lst lst sc-type sc-term) a)
             (rp-evl-lst lst a))
      :flag attach-sc-lst)
    :otf-flg t
    :hints (("Goal"
             :in-theory (e/d (rp-evl-of-fncall-args) ()))))

  (local
   (defthm is-rp-is-if-lemma1
     (implies (is-rp x)
              (not (is-if x)))
     :hints (("Goal"
              :in-theory (e/d (is-if is-rp) ())))))

  (local
   (defthm lemma1
     (IMPLIES (AND
               (NOT (CONSP SC-TERM))
               (IS-RP (LIST 'RP
                            (LIST 'QUOTE SC-TYPE)
                            SC-TERM))
               (RP-EVL (LIST SC-TYPE SC-TERM) A))
              (VALID-SC (LIST 'RP (LIST 'QUOTE SC-TYPE) SC-TERM)
                        A))
     :hints (("Goal"
              :in-theory (e/d (IS-RP-IMPLIES-FC
                               ;; rp-evl-constraint-0
                               CONTEXT-FROM-RP
                               eval-and-all
                               ex-from-rp
                               is-rp
                               is-if)
                              (VALID-SC-EX-FROM-RP-2))))))

  (local
   (defthm is-if-lemma1
     (not (is-if (cons 'rp rest)))
     :hints (("Goal"
              :in-theory (e/d (is-if) ())))))

  (local
   (defthm is-rp-lemma2
     (implies (IS-RP (LIST 'RP
                           (LIST 'QUOTE SC-TYPE)
                           term1))
              (IS-RP (LIST 'RP
                           (LIST 'QUOTE SC-TYPE)
                           term2)))
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))

  (local
   (defthm ex-from-rp-lemma100
     (implies (and (rp-syntaxp term)
                   (not (is-rp term)))
              (equal (ex-from-rp (cons (car term) rest))
                     (cons (car term) rest)))
     :hints (("Goal"
              :in-theory (e/d (ex-from-rp
                               is-rp) ())))))

  (local
   (defthm context-from-rp-lemma1
     (implies (and (rp-syntaxp term)
                   (not (is-rp term)))
              (equal (context-from-rp (cons (car term) rest) context)
                     context))
     :hints (("Goal"
              :in-theory (e/d (context-from-rp
                               is-rp) ())))))
  (local
   (defthm lemma10
     (implies (and (rp-syntaxp term)
                   (not (is-rp term)))
              (not (equal (car term) 'rp)))))

  (local
   (defthm lemma11
     (and (implies (not (is-if term))
                   (not (IS-IF (CONS (CAR TERM)
                                     (ATTACH-SC-LST (CDR TERM)
                                                    SC-TYPE SC-TERM)))))
          (implies (and (not (is-rp term))
                        (rp-syntaxp term))
                   (not (IS-rp (CONS (CAR TERM)
                                     (ATTACH-SC-LST (CDR TERM)
                                                    SC-TYPE SC-TERM))))))
     :hints (("Goal"
              :expand ((ATTACH-SC-LST (CDR TERM)
                                      SC-TYPE SC-TERM)
                       (ATTACH-SC-LST (CDDR TERM)
                                      SC-TYPE SC-TERM)
                       (ATTACH-SC-LST (CDDDDR TERM)
                                      SC-TYPE SC-TERM)
                       (ATTACH-SC-LST (CDDdR TERM)
                                      SC-TYPE SC-TERM))
              :in-theory (e/d (is-if is-rp) ())))))

  (local
   (defthm lemma12
     (implies (IS-RP (LIST 'RP
                           (LIST 'QUOTE SC-TYPE)
                           SC-TERM))
              (AND (SYMBOLP SC-TYPE)
                   (NOT (BOOLEANP SC-TYPE))
                   (NOT (EQUAL SC-TYPE 'QUOTE))
                   (NOT (EQUAL SC-TYPE 'RP))))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))

  (local
   (defthm lemma13
     (implies (and (eval-and-all (context-from-rp term nil)
                                 a)
                   (is-rp term))
              (eval-and-all (context-from-rp (caddr term) nil)
                            a))
     :hints (("goal"
              :in-theory (e/d (is-rp
                               context-from-rp)
                              (ex-from-rp-lemma1))))))

  (local
   (defthm lemma14
     (implies (and (valid-sc term a)
                   (consp term)
                   (not (eq (car term) 'quote))
                   (not (is-if term)))
              (valid-sc-subterms (cdr term) a))
     :hints (("goal"
              :expand ((valid-sc term a)
                       (ex-from-rp term))
              :in-theory (e/d (is-rp)
                              (EX-FROM-RP-LEMMA1))))))

  (local
   (defthm lemma15
     (implies (and (RP-SYNTAXP TERM)
                   (NOT (EQUAL (CAR TERM) 'QUOTE)))
              (RP-SYNTAXP-LST (CDR TERM)))
     :hints (("Goal"
              :cases ((is-rp term))
              :in-theory (e/d (is-rp) ())))))

  (local
   (defthm lemma16
     (implies (valid-sc term a)
              (VALID-SC (EX-FROM-RP TERM) A))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :in-theory (e/d (VALID-SC-EX-FROM-RP-2) ())))))

  (local
   (defthm lemma17
     (implies (and (eval-and-all (context-from-rp term nil) a)
                   (rp-syntaxp term)
                   (not (is-rp sc-term))
                   (is-rp (LIST 'RP (LIST 'QUOTE SC-TYPE) SC-TERM))
                   (rp-evl `(,sc-type ,sc-term) a))
              (eval-and-all (context-from-rp (attach-sc term sc-type sc-term)
                                             nil)
                            a))
     :hints (("Goal"
              :expand ((ATTACH-SC SC-TERM SC-TYPE SC-TERM)
                       (ATTACH-SC TERM SC-TYPE SC-TERM)

                       )
              :cases ((equal term sc-term)
                      (is-rp term)
                      (consp term))
              :in-theory (e/d (eval-and-all
                               rp-evl-of-fncall-args
                               is-rp-implies
                               is-rp-implies-fc
                               attach-sc
                               context-from-rp)
                              (
                               EX-FROM-RP-LEMMA1
                               include-fnc))))))

  (local
   (defthm lemma18
     (IMPLIES (AND (ACL2::FLAG-IS 'ATTACH-SC)
                   (CONSP TERM)
                   (case-split (is-rp term))
                   (NOT (EQUAL (CAR TERM) 'QUOTE))
                   (NOT (EQUAL TERM SC-TERM))
                   (VALID-SC-SUBTERMS (ATTACH-SC-LST (CDR TERM)
                                                     SC-TYPE SC-TERM)
                                      A)
                   (VALID-SC TERM A)
                   (not (is-rp sc-term))
                   (RP-SYNTAXP TERM)
;   (NOT (EQUAL (CAR TERM) 'IF))
;  (NOT (INCLUDE-FNC-SUBTERMS (CDR TERM) 'IF))
                   (IS-RP (LIST 'RP
                                (LIST 'QUOTE SC-TYPE)
                                SC-TERM))
                   (RP-EVL (LIST SC-TYPE SC-TERM) A))
              (VALID-SC (CONS (CAR TERM)
                              (ATTACH-SC-LST (CDR TERM)
                                             SC-TYPE SC-TERM))
                        A))
;:otf-flg t
     :hints (("Goal"
              :expand ((VALID-SC TERM A)
                       (ATTACH-SC-LST (CDDR TERM)
                                      SC-TYPE SC-TERM)
                       (ATTACH-SC-LST (CDR TERM)
                                      SC-TYPE SC-TERM)
                       (EX-FROM-RP (LIST 'RP
                                         (CADR TERM)
                                         (ATTACH-SC (CADDR TERM)
                                                    SC-TYPE SC-TERM)))
                       (VALID-SC (LIST 'RP
                                       (CADR TERM)
                                       (ATTACH-SC (CADDR TERM)
                                                  SC-TYPE SC-TERM))
                                 A))
              :in-theory (e/d (IS-RP-IMPLIES-FC
                               is-if
                               is-rp
                               EVAL-AND-ALL
                               rp-evl-of-fncall-args
                               RP-EVL-lst-of-cons
                               CONTEXT-FROM-RP)
                              (VALID-SC-EX-FROM-RP-2
                               EX-FROM-RP-LEMMA1
                               VALID-SC))))))

  (local
   (defthm lemma19
     (IMPLIES (AND
               (CONSP SC-TERM)
               (NOT (EQUAL (CAR SC-TERM) 'QUOTE))
               (VALID-SC-SUBTERMS (ATTACH-SC-LST (CDR SC-TERM)
                                                 SC-TYPE SC-TERM)
                                  A)
               (VALID-SC SC-TERM A)
               (RP-SYNTAXP SC-TERM)
;   (NOT (EQUAL (CAR SC-TERM) 'IF))
;   (NOT (INCLUDE-FNC-SUBTERMS (CDR SC-TERM)
;                             'IF))
               (case-split (is-rp sc-term))
               (not (is-rp sc-term))
               (IS-RP (LIST 'RP
                            (LIST 'QUOTE SC-TYPE)
                            SC-TERM))
               (RP-EVL (LIST SC-TYPE SC-TERM) A))
              (VALID-SC (LIST 'RP
                              (LIST 'QUOTE SC-TYPE)
                              (CONS (CAR SC-TERM)
                                    (ATTACH-SC-LST (CDR SC-TERM)
                                                   SC-TYPE SC-TERM)))
                        A))
     :hints (("Goal"
              :expand ((VALID-SC (LIST 'RP
                                       (LIST 'QUOTE SC-TYPE)
                                       (LIST 'RP
                                             (CADR SC-TERM)
                                             (ATTACH-SC (CADDR SC-TERM)
                                                        SC-TYPE SC-TERM)))
                                 A)

                       (ATTACH-SC-LST (CDR SC-TERM)
                                      SC-TYPE SC-TERM)
                       (VALID-SC (LIST 'RP
                                       (CADR SC-TERM)
                                       (ATTACH-SC (CADDR SC-TERM)
                                                  SC-TYPE SC-TERM))
                                 A)
                       (VALID-SC SC-TERM A)
                       (EX-FROM-RP (LIST 'RP
                                         (LIST 'QUOTE SC-TYPE)
                                         (LIST 'RP
                                               (CADR SC-TERM)
                                               (ATTACH-SC (CADDR SC-TERM)
                                                          SC-TYPE SC-TERM))))
                       (EX-FROM-RP (LIST 'RP
                                         (CADR SC-TERM)
                                         (ATTACH-SC (CADDR SC-TERM)
                                                    SC-TYPE SC-TERM))))
              :in-theory (e/d (IS-RP-IMPLIES-FC
                               is-if

                               EVAL-AND-ALL
                               rp-evl-of-fncall-args
                               RP-EVL-lst-of-cons
                               CONTEXT-FROM-RP)
                              (VALID-SC-EX-FROM-RP-2
                               EX-FROM-RP-LEMMA1
                               is-rp
                               VALID-SC))))))

  (local
   (defthm lemma20
     (IMPLIES (AND
               (CONSP SC-TERM)
               (NOT (EQUAL (CAR SC-TERM) 'QUOTE))
               (VALID-SC-SUBTERMS (ATTACH-SC-LST (CDR SC-TERM)
                                                 SC-TYPE SC-TERM)
                                  A)
               (VALID-SC SC-TERM A)
               (RP-SYNTAXP SC-TERM)
               (NOT (EQUAL (CAR SC-TERM) 'IF))
; (NOT (INCLUDE-FNC-SUBTERMS (CDR SC-TERM)
;                           'IF))
               (not (is-rp sc-term))
               (IS-RP (LIST 'RP
                            (LIST 'QUOTE SC-TYPE)
                            SC-TERM))
               (RP-EVL (LIST SC-TYPE SC-TERM) A))
              (VALID-SC (LIST 'RP
                              (LIST 'QUOTE SC-TYPE)
                              (CONS (CAR SC-TERM)
                                    (ATTACH-SC-LST (CDR SC-TERM)
                                                   SC-TYPE SC-TERM)))
                        A))
     :hints (("Goal"
              :expand ((VALID-SC (LIST 'RP
                                       (LIST 'QUOTE SC-TYPE)
                                       (CONS (CAR SC-TERM)
                                             (ATTACH-SC-LST (CDR SC-TERM)
                                                            SC-TYPE SC-TERM)))
                                 A)
                       (VALID-SC (CONS (CAR SC-TERM)
                                       (ATTACH-SC-LST (CDR SC-TERM)
                                                      SC-TYPE SC-TERM))
                                 A)
                       (EX-FROM-RP (LIST 'RP
                                         (LIST 'QUOTE SC-TYPE)
                                         (CONS (CAR SC-TERM)
                                               (ATTACH-SC-LST (CDR SC-TERM)
                                                              SC-TYPE SC-TERM)))))
              :in-theory (e/d (IS-RP-IMPLIES-FC
                               is-if

                               EVAL-AND-ALL
                               rp-evl-of-fncall-args
                               RP-EVL-lst-of-cons
                               CONTEXT-FROM-RP)
                              (VALID-SC-EX-FROM-RP-2
                               EX-FROM-RP-LEMMA1
                               is-rp
                               VALID-SC))))))

  (local
   (defthm lemma21
     (IMPLIES (AND (CONSP SC-TERM)
                   ;;(EQUAL (CAR SC-TERM) 'IF)
                   (VALID-SC SC-TERM A)
                   (RP-SYNTAXP SC-TERM)
                   (IS-RP (LIST 'RP
                                (LIST 'QUOTE SC-TYPE)
                                SC-TERM))
                   (NOT (IS-RP SC-TERM))
                   (RP-EVL (LIST SC-TYPE SC-TERM) A))
              (VALID-SC (LIST 'RP (LIST 'QUOTE SC-TYPE) SC-TERM)
                        A))
     :otf-flg t
     :hints (("Goal"
              :expand ((VALID-SC (LIST 'RP (LIST 'QUOTE SC-TYPE) SC-TERM)
                                 A))
              :in-theory (e/d (CONTEXT-FROM-RP
                               EX-FROM-RP
                               )
                              (is-rp IS-IF-LEMMA1
                                     IS-RP-LEMMA2
                                     VALID-SC-EX-FROM-RP-2
                                     ))))))

  (defthm-attach-sc
    (defthm valid-sc-attach-sc
      (implies (and (valid-sc term a)
                    (rp-syntaxp term)
;          (not (include-fnc term 'if)) ;; RHS should not have any if
                    (is-rp (LIST 'RP (LIST 'QUOTE SC-TYPE) SC-TERM))
                    (not (is-rp sc-term))
                    (rp-evl `(,sc-type ,sc-term) a))
               (valid-sc (attach-sc term sc-type sc-term) a))
      :flag attach-sc)

    (defthm valid-sc-subterms-attach-sc-lst
      (implies (and (valid-sc-subterms lst a)
                    (rp-syntaxp-lst lst)
;         (not (include-fnc-subterms lst 'if))
                    (is-rp (LIST 'RP (LIST 'QUOTE SC-TYPE) SC-TERM))
                    (not (is-rp sc-term))
                    (rp-evl `(,sc-type ,sc-term) a))
               (valid-sc-subterms (attach-sc-lst lst sc-type sc-term) a))
      :flag attach-sc-lst)
    :hints (("Goal"
             ;;:cases ((Is-rp term))
             :in-theory (e/d (IS-RP-IMPLIES-FC
                              is-if
                              ;;rp-evl-constraint-0
                              EVAL-AND-ALL
                              CONTEXT-FROM-RP)
                             (VALID-SC-EX-FROM-RP-2
                              RP-EVL-lst-of-cons))))))

(defthm-attach-sc
  (defthm not-include-ATTACH-SC
    (implies (and (not (include-fnc term fn))
                  (not (equal fn 'rp)))
             (not (include-fnc (attach-sc term sc-type sc-term)
                               fn)))
    :flag attach-sc)
  (defthm not-include-ATTACH-SC-lst
    (implies (and (not (include-fnc-subterms lst fn))
                  (not (equal fn 'rp)))
             (not (include-fnc-subterms
                   (attach-sc-lst lst sc-type sc-term) fn)))
    :flag attach-sc-lst))

(defthm-attach-sc
  (defthm rp-syntaxp-attach-sc
    (implies (and (rp-syntaxp term)
                  (is-rp (LIST 'RP (LIST 'QUOTE SC-TYPE) SC-TERM)))
             (rp-syntaxp (attach-sc term sc-type sc-term)))
    :flag attach-sc)
  (defthm rp-syntaxp-lst-attach-sc-lst
    (implies (and (rp-syntaxp-lst lst)
                  (is-rp (LIST 'RP (LIST 'QUOTE SC-TYPE) SC-TERM)))
             (rp-syntaxp-lst (attach-sc-lst lst sc-type sc-term)))
    :flag attach-sc-lst)
  :hints (("Goal"
           :expand  ((ATTACH-SC-LST (CDR TERM)
                                    SC-TYPE SC-TERM)
                     (ATTACH-SC SC-TERM SC-TYPE SC-TERM)
                     (ATTACH-SC TERM SC-TYPE SC-TERM)
                     (ATTACH-SC-LST (CDR SC-TERM)
                                    SC-TYPE SC-TERM)
                     (ATTACH-SC-LST (CDDR SC-TERM)
                                    SC-TYPE SC-TERM)
                     (ATTACH-SC-LST (CDDR TERM)
                                    SC-TYPE SC-TERM))
           :in-theory (e/d (is-rp) ()))))

(defthm-attach-sc
  (defthm pseudo-termp2-attach-sc
    (implies (pseudo-termp2 term)
             (pseudo-termp2 (attach-sc term sc-type sc-term)))
    :flag attach-sc)
  (defthm pseudo-term-listp2-attach-sc-lst
    (implies (pseudo-term-listp2 lst)
             (pseudo-term-listp2 (attach-sc-lst lst sc-type sc-term)))
    :flag attach-sc-lst))

(make-flag get-vars1 :defthm-macro-name defthm-get-vars)

(defthm-get-vars
  (defthm get-vars1-attach-sc
    (equal (get-vars1 (attach-sc q sc-type sc-term) acc)
           (get-vars1 q acc))
    :flag get-vars1)
  (defthm get-vars1-attach-sc-lst
    (equal (get-vars-subterms (attach-sc-lst subterms sc-type sc-term) acc)
           (get-vars-subterms subterms acc))
    :flag get-vars-subterms))

(encapsulate
  nil

  (defthm rp-evl-of-attach-sc-list-to-rhs
    (equal (rp-evl (attach-sc-list-to-rhs rhs sc-list) a)
           (rp-evl rhs a)))

  (local
   (defthm lemma1
     (implies (not (include-fnc-subterms sc-list 'rp))
              (not (include-fnc-subterms (cdr sc-list) 'RP)))
     :rule-classes :forward-chaining))

  (local
   (defthm lemma2
     (implies (eval-and-all sc-list a)
              (eval-and-all (cdr sc-list) a))
     :rule-classes :forward-chaining))

  (local
   (defthm lemma3
     (implies (and (NOT (INCLUDE-FNC-SUBTERMS SC-LIST 'RP))
                   (IS-RP (LIST 'RP
                                (LIST 'QUOTE (CAR (CAR SC-LIST)))
                                (CADR (CAR SC-LIST)))))
              (NOT (IS-RP (CADR (CAR SC-LIST)))))
     :hints (("Goal"
              :Expand ((INCLUDE-FNC-SUBTERMS SC-LIST 'RP))
              :in-theory (e/d (is-rp) ())))))

  (local
   (defthm lemma4
     (implies (AND (CONSP (CAR SC-LIST))
                   (EVAL-AND-ALL SC-LIST A)
                   (CONSP (CDR (CAR SC-LIST)))
                   (EQ (CDDR (CAR SC-LIST)) NIL))
              (RP-EVL (LIST (CAR (CAR SC-LIST))
                            (CADR (CAR SC-LIST)))
                      A))))

  (defthm valid-sc-of-attach-sc-list-to-rhs
    (implies (and (not (include-fnc-subterms sc-list 'rp))
                  (eval-and-all sc-list a)
                  (rp-syntaxp rhs)
;(not (include-fnc rhs 'if))
                  (valid-sc rhs a))
             (valid-sc (attach-sc-list-to-rhs rhs sc-list) a)))

  (defthm not-include-fnc-attach-sc-list-to-rhs
    (implies (and (not (include-fnc rhs fn))
                  (not (equal fn 'rp)))
             (not (include-fnc (attach-sc-list-to-rhs rhs sc-list)
                               fn))))

  (defthm rp-syntaxp-attach-sc-list-to-rhs
    (implies (rp-syntaxp rhs)
             (rp-syntaxp (attach-sc-list-to-rhs rhs sc-list))))

  (defthm pseudo-termp2-attach-sc-list-to-rhs
    (implies (pseudo-termp2 rhs)
             (pseudo-termp2 (attach-sc-list-to-rhs rhs sc-list))))

  (defthm get-vars1-attach-sc-list-to-rhs
    (equal (get-vars1 (attach-sc-list-to-rhs rhs sc-list) acc)
           (get-vars1 rhs acc))))

(encapsulate
  nil
  (defthm not-include-fnc-subterms-if-to-and-list
    (implies (not (include-fnc term fn))
             (not (include-fnc-subterms (IF-TO-AND-LIST term) fn)))
    :hints (("Goal"
             :in-theory (e/d (if-to-and-list) ()))))

  (defthm eval-and-all-if-to-and-list
    (iff (eval-and-all (if-to-and-list term) a)
         (rp-evl term a))
    :hints (("Goal"
             :in-theory (e/d (if-to-and-list) ()))))

  (defthm eval-and-all-if-to-and-list2
    (implies (rp-evl term a)
             (eval-and-all (if-to-and-list term) a))
    :hints (("Goal"
             :in-theory (e/d (if-to-and-list) ())))))

(local
 (encapsulate
   nil

   (defthm rule-sytanxp-attach-sc-to-rule
     (implies (rule-syntaxp rule)
              (rule-syntaxp (attach-sc-to-rule rule sc-formula)))
     :hints (("Goal"
              :in-theory (e/d () (get-vars1
                                  PSEUDO-TERM-LISTP2
                                  IS-RP-PSEUDO-TERMP
                                  PSEUDO-TERM-LISTP2-IS-TRUE-LISTP
                                  PSEUDO-TERMP2-IMPLIES-CDR-LISTP
                                  PSEUDO-TERMP2-SHOULD-TERM-BE-IN-CONS-LHS
                                  DEFAULT-CAR
                                  NOT-INCLUDE-RP
                                  DEFAULT-CDR
                                  TRUE-LISTP
                                  IS-IF-PSEUDO-TERMP2)))))

   (local
    (defthm rule-syntaxp-implies-m
      (implies (rule-syntaxp rule)
               (AND (WEAK-CUSTOM-REWRITE-RULE-P RULE)
                    (PSEUDO-TERMP2 (RP-HYPm RULE))
                    (PSEUDO-TERMP2 (RP-LHSm RULE))
                    (PSEUDO-TERMP2 (RP-RHSm RULE))
                    (NOT (INCLUDE-FNC (RP-LHSm RULE) 'RP))
                    (NOT (INCLUDE-FNC (RP-HYPm RULE) 'RP))
                    (RP-SYNTAXP (RP-RHSm RULE))
                    (NOT (INCLUDE-FNC (RP-RHSm RULE) 'FALIST))
                    (NOT (INCLUDE-FNC (RP-HYPm RULE) 'FALIST))
                    (NOT (INCLUDE-FNC (RP-LHSm RULE) 'IF))
                    (NOT (INCLUDE-FNC (RP-LHSm RULE) 'SYNP))
                    (NO-FREE-VARIABLEP RULE)))
      :rule-classes :forward-chaining
      :hints (("Goal"
               :in-theory (e/d (rule-syntaxp) ())))))

   (local
    (defthm rp-evl-and-eval-and-all
      (implies (and (subsetp x y)
                    (eval-and-all y a))
               (eval-and-all x a))))

   (local
    (defthm rp-evl-and-subset-if-to-and-lists
      (implies (and (subsetp (if-to-and-list x)
                             (if-to-and-list y))
                    (rp-evl y a))
               (rp-evl x a))
      :hints (("Goal"
               :use ((:instance rp-evl-and-eval-and-all
                                (x (if-to-and-list x))
                                (y (if-to-and-list y))))
               :in-theory (e/d ()
                               (rp-evl-and-eval-and-all))))))

   (defthm valid-rulep-attach-sc-to-rule-lemma1
     (implies (and (valid-rulep-with-a rule a)
                   (rule-syntaxp rule)
                   (not (include-fnc sc-formula 'rp))
                   (rp-evl sc-formula a))
              (valid-rulep-with-a (attach-sc-to-rule rule sc-formula) a))
     :hints (("Goal"
              :in-theory (e/d (IF-TO-AND-LIST
                               rule-syntaxp-implies-m)
                              (rule-syntaxp
                               (:REWRITE DEFAULT-CDR)
                               (:REWRITE EX-FROM-SYNP-LEMMA1)
                               IS-SYNP
                               (:DEFINITION RP-EQUAL)
                               (:REWRITE RP-EQUAL-IMPLIES-RP-EQUAL2)
                               (:TYPE-PRESCRIPTION INCLUDE-FNC)
                               EX-FROM-RP
                               (:REWRITE RP-EQUAL-IMPLIES-RP-EQUAL2)
                               (:DEFINITION PSEUDO-TERMP2)
                               (:DEFINITION EVAL-AND-ALL)
                               get-vars1)))))))

(local
 (defthm valid-rulep-attach-sc-to-rule
   (implies (and (valid-rulep rule)
                 (rule-syntaxp rule)
                 (not (include-fnc sc-formula 'rp))
                 (valid-formula-sk sc-formula))
            (valid-rulep (attach-sc-to-rule rule sc-formula)))
   :hints (("goal"
            :do-not-induct t
            :use ((:instance valid-rulep-sk-necc
                             (a (valid-rulep-sk-witness (attach-sc-to-rule rule
                                                                           sc-formula))))
                  (:instance valid-formula-sk-necc
                             (a (valid-rulep-sk-witness (attach-sc-to-rule rule
                                                                           sc-formula)))
                             (formula sc-formula)))
            :expand ((valid-rulep-sk (attach-sc-to-rule rule sc-formula)))
            :in-theory (e/d (valid-rulep)
                            (rule-syntaxp
                             valid-formula-sk-necc
                             valid-rulep-sk-necc
                             valid-formula-sk
                             valid-rulep-sk
                             attach-sc-to-rule
                             valid-rulep-sk-body))))))
(local
 (encapsulate
   nil

   (local
    (defthm rule-syntaxp-update-rule-with-sc-aux
      (implies (and (rule-syntaxp rule))
               (rule-syntaxp (update-rule-with-sc-aux rule sc-rule-names state)))
      :hints (("Goal"
               :in-theory (e/d (update-rule-with-sc-aux)
                               (INCLUDE-FNC
                                rule-syntaxp))))))

   (local
    (defthm valid-formula-sk-of-meta-extract-formula
      (implies (rp-evl-meta-extract-global-facts :state state)
               (valid-formula-sk (meta-extract-formula name state)))))

   #|(skip-proofs (local ;; this is true and can be proved easily
   (defthm valid-formula-sk-beta-search-reduce
   (implies (and (pseudo-termp formula)
   (valid-formula-sk formula))
   (valid-formula-sk (beta-search-reduce formula limit)))
   :hints (("Goal"
   :in-theory (e/d (valid-formula-sk-necc) (valid-formula-sk)))))))||#

   (local
    (defthm valid-rulep-update-rule-with-sc-aux
      (implies (and (rule-syntaxp rule)
                    (rp-evl-meta-extract-global-facts :state state)
                    (valid-rulep rule))
               (valid-rulep (update-rule-with-sc-aux rule sc-rule-names state)))
      :hints (("Goal"
               :in-theory (e/d () (valid-rulep
                                   attach-sc-to-rule
                                   rule-syntaxp))))))

   (defthm valid-rulep-update-rule-with-sc
     (implies (and (rule-syntaxp rule)
                   (rp-evl-meta-extract-global-facts :state state)
                   (valid-rulep rule))
              (valid-rulep (update-rule-with-sc rule sc-alist state)))
     :hints (("Goal"
              :in-theory (e/d () (valid-rulep
                                  update-rule-with-sc-aux
                                  attach-sc-to-rule
                                  rule-syntaxp)))))))

(defthm valid-rulep-update-rules-with-sc
  (implies (and (valid-rulesp rules)
                (rp-evl-meta-extract-global-facts :state state))
           (valid-rulesp (update-rules-with-sc rules sc-alist state)))
  :hints (("Goal"
           ;; :use ((:instance valid-rulep-update-rule-with-sc
           ;;                  (rule (car rules))))
           :in-theory (e/d ()
                           (update-rule-with-sc
                            ;;(:e tau-system)
                            valid-rulep-update-rule-with-sc
                            valid-rulep-sk
                            valid-rulep-sk-body
                            rule-syntaxp)))))

(local
 (defthm append-valid-rulesp
   (implies (and (valid-rulesp rules1)
                 (valid-rulesp rules2))
            (valid-rulesp (append rules1 rules2)))
   :hints (("Goal"
            :in-theory (e/d ()
                            (rule-syntaxp
                             valid-rulep))))))

(defthm valid-rulesp-get-rules
  (implies (rp-evl-meta-extract-global-facts :state state)
           (valid-rulesp (get-rule-list runes sc-alist new-synps state)))
  :hints (("Goal"
           :in-theory (e/d ()
                           (rule-syntaxp
                            check-if-def-rule-should-be-saved
                            custom-rewrite-with-meta-extract
                            update-rules-with-sc)))))

#|(defun add-to-fast-alist (key val alist)
  (b* ((entry (hons-get key alist))
       ((when (atom entry))
        (hons-acons key (cons val nil) alist)))
    (hons-acons key (cons val (cdr entry)) alist)))||#

#|(defun rule-list-to-alist-aux (rules)
  (if (atom rules)
      nil
    (b* ((rule (car rules))
         (rune (rp-rune rule))
         (rule-name (case-match rune ((& name . &) name) (& rune)))
         (rest (rule-list-to-alist-aux (cdr rules))))
      (add-to-fast-alist rule-name rule rest))))||#

(defthm valid-rules-alistp-add-rule-to-alist
  (implies (and (valid-rules-alistp alist)
                (valid-rulep rule))
           (valid-rules-alistp (add-rule-to-alist alist rule)))
  :hints (("Goal"
           :in-theory (e/d ()
                           (rule-syntaxp
                            valid-rulep)))))

(defthm to-fasts-alist-def
  (equal (to-fast-alist alist)
         alist))

(defthm valid-rules-alistp-rule-list-to-alist
  (implies (valid-rulesp rules)
           (valid-rules-alistp (rule-list-to-alist rules)))
  :hints (("Goal"
           :in-theory (e/d (rule-list-to-alist)
                           (add-rule-to-alist
                            valid-rulep)))))

(defthm valid-rules-alistp-get-rules
  (implies (rp-evl-meta-extract-global-facts :state state)
           (valid-rules-alistp (get-rules runes state :new-synps new-synps)))
  :hints (("Goal"
           :in-theory (e/d (get-rules)
                           (to-fast-alist
                            rule-list-to-alist
                            get-rule-list
                            table-alist)))))
(defthm SYMBOL-ALISTP-GET-ENABLED-EXEC-RULES
  (symbol-alistp (GET-ENABLED-EXEC-RULES runes)))
