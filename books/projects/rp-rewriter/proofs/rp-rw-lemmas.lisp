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

(include-book "../rp-rewriter")
(include-book "match-lhs-lemmas")
(include-book "rp-equal-lemmas")
(include-book "apply-bindings-lemmas")
(include-book "apply-meta-lemmas")
(include-book "ex-counterpart-lemmas")
(include-book "rp-state-functions-lemmas")

(local
 (in-theory
  (disable
   (:rewrite atom-rp-termp-is-symbolp)
   hons-get
   rp-stat-add-to-rules-used
   rp-ex-counterpart
   (:definition len)
   (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
   (:DEFINITION ACL2::APPLY$-BADGEP)
   (:definition rp-exc-all)
   (:definition rp-check-context)
   (:definition rp-ev-fncall)
   (:definition rp-apply-bindings)
   valid-rulep
   (:META ACL2::APPLY$-PRIM-META-FN-CORRECT)
   valid-rulesp
   valid-rules-alistp
   rp-rw-rule-aux
   is-rp

   is-synp
   ex-from-rp
   rp-equal2
   EX-FROM-SYNP-LEMMA1
   rp-equal
   ex-from-rp-lemma1
   (:definition unquote-all)
   (:definition remove-rp-from-bindings)
   (:definition rp-extract-context)
   (:definition rp-get-dont-rw)
   (:definition rp-ex-counterpart)
   dumb-negate-lit2
   ex-from-rp
   (:definition rp-rw-relieve-synp)
   (:definition quote-listp))))

(set-state-ok t)
(with-output
  :off :all
  :on error
  :gag-mode nil
  (make-flag rp-rw :defthm-macro-name defthm-rp-rw
             :hints
             (("Goal"
               :in-theory
               (disable QUOTEP
                        (:DEFINITION RP-CHECK-CONTEXT)
                        (:DEFINITION LEN)

                        (:REWRITE DEFAULT-<-1)
                        (:REWRITE DEFAULT-<-2)

                        (:DEFINITION RP-RW-RELIEVE-SYNP)
                        (:TYPE-PRESCRIPTION quote-listp)
                        (:TYPE-PRESCRIPTION IS-IF$inline)
                        (:DEFINITION RP-RW-RELIEVE-SYNP)
                        (:DEFINITION RP-EXC-ALL)
                        (:TYPE-PRESCRIPTION O<)
                        (:TYPE-PRESCRIPTION QUOTEP)
                        (:TYPE-PRESCRIPTION RETURN-LAST)

                        (:REWRITE DEFAULT-+-2)
                        (:REWRITE DEFAULT-+-1)
                        (:DEFINITION RETURN-LAST)
                        (:TYPE-PRESCRIPTION RP-RW-RELIEVE-SYNP)
                        (:TYPE-PRESCRIPTION NONNIL-P)
                        (:DEFINITION HONS-ASSOC-EQUAL)
                        (:DEFINITION RP-APPLY-BINDINGS)
                        (:DEFINITION REMOVE-RP-FROM-BINDINGS)
                        EX-FROM-RP
                        #|RESOLVE-ASSOC-EQ-VALS||#
                        quote-listp
                        IS-NONNIL-FIX
                        nonnil-fix
                        dont-rw-if-fix

                        RP-EX-COUNTERPART
                        rp-rw-rule-aux
                        UPDATE-NTH)))))

(local
 (in-theory (disable context-syntaxp)))

(local
 (defthmd context-syntaxp-def
   (equal (context-syntaxp context)
          (AND (RP-TERM-LISTP CONTEXT)))
   :hints (("Goal"
            :in-theory (e/d (context-syntaxp) ())))))

(defthm return-val-of-rp-extract-context
  (implies (and (rp-termp term))
           (context-syntaxp (rp-extract-context term)))
  :hints (("Goal" :in-theory (enable rp-extract-context
                                     append
                                     is-falist
                                     rp-term-listp
                                     context-syntaxp-def
                                     ))))

(defthm extract-context-is-valid-sc
  (implies (and (valid-sc term a)
                (rp-evlt term a))
           (valid-sc-subterms (RP-EXTRACT-CONTEXT term) a))
  :hints (("Goal"
           :in-theory (e/d (rp-extract-context
                            is-if
                            valid-sc-subterms
                            valid-sc)
                           ((:DEFINITION RP-TERMP)
                            (:DEFINITION RP-TERM-LISTP)
                            (:REWRITE NOT-INCLUDE-RP))))))

(defthm rp-termp-rp-check-context
  (implies (and (context-syntaxp context)
                (rp-termp term))
           (RP-TERMP (RP-CHECK-CONTEXT TERM CONTEXT IFF-FLG)))
  :hints (("Goal" :in-theory (e/d
                              (context-syntaxp
                               rp-termp
                               rp-term-listp
                               rp-check-context)
                              ((:REWRITE RP-EQUAL-IS-SYMMETRIC)
                               (:DEFINITION TRUE-LISTP)
                               )))))

(defthm remove-rp-from-bindings-is-bindings
  (implies (bindings-alistp bindings)
           (bindings-alistp (remove-rp-from-bindings bindings)))
  :hints (("Goal"
           :in-theory (enable remove-rp-from-bindings))))

(defthm RP-GET-RULES-FOR-TERM-returns-rule-list-syntaxp
  (implies (rules-alistp rules-alist)
           (rule-list-syntaxp (rp-get-rules-for-term fn rules-alist)))
  :hints (("Goal" :in-theory (e/d (hons-get HONS-ASSOC-EQUAL
                                            rules-alistp)
                                  ((:REWRITE ACL2::PLAIN-UQI-TRUE-LIST-LISTP)
                                   (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                                   (:DEFINITION TRUE-LISTP)
                                   (:DEFINITION ALWAYS$)
                                   (:DEFINITION MEMBER-EQUAL)
                                   (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                                   (:DEFINITION RP-TERMP)
                                   (:REWRITE
                                    ACL2::TRUE-LIST-LISTP-IMPLIES-ALWAYS$-TRUE-LISTP)
                                   (:DEFINITION TRUE-LIST-LISTP)
                                   (:REWRITE ACL2::APPLY$-SYMBOL-ARITY-1)
                                   (:DEFINITION FALIST-CONSISTENT)
                                   (:REWRITE ACL2::APPLY$-PRIMITIVE)
                                   (:META ACL2::APPLY$-PRIM-META-FN-CORRECT))))))

(defthm rp-term-listp-rp-extract-context
  (implies (rp-termp term)
           (RP-TERM-LISTP (RP-EXTRACT-CONTEXT term)))
  :hints (("Goal" :in-theory (enable rp-extract-context rp-term-listp
                                     rp-termp))))

(defthm rp-rule-is-applicable-not-iff
  ;; when a valid rule is applied on a term with good bindings,
  ;; the rhs of applied rule should be the same as the term.
  (implies (and (rp-evlt (rp-apply-bindings (rp-hyp rule) bindings) a)
                (rp-termp term)
                (good-bindingsp rule term bindings a)
                (bindings-alistp bindings)
                (valid-rulep rule)
                (alistp a)
                (rp-rule-rwp rule)
                (rp-termp (rp-rhs rule))
                (not (rp-iff-flag rule)))
           (and (equal (rp-evlt (rp-apply-bindings (rp-rhs rule) bindings) a)
                       (rp-evlt term a))
                (equal (rp-evl (rp-apply-bindings (rp-rhs rule)
                                                  (rp-trans-bindings bindings))
                               a)
                       (rp-evlt term a))))
  :hints (("goal"
           :use ((:instance valid-rulep-sk-necc
                            (a (bind-bindings (rp-trans-bindings bindings) a)))
                 (:instance rp-evl-of-rp-equal2
                            (term1 (rp-apply-bindings (rp-lhs rule) bindings))
                            (term2 term)
                            (a a)))
           :in-theory (e/d (valid-rulep
                            valid-rulesp
                            valid-rules-alistp
                            rule-syntaxp)
                           (rp-evl-of-rp-equal
                            (:REWRITE RP-APPLY-BINDINGS-EQUIV-NOT-IFF)
                            (:DEFINITION BIND-BINDINGS-AUX)
                            (:REWRITE VALID-RULEP-IMPLIES-VALID-SC)
                            (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS)
                            valid-rulep-sk-necc
                            ;;rp-equal-of-two-2
                            rp-equal-is-symmetric
                            pseudo-termp  rp-lhs rp-rhs rp-termp
                            rp-hyp)))))

(defthm rp-rule-is-applicable-iff
  ;; when a valid rule is applied on a term with good bindings,
  ;; the rhs of applied rule should be the same as the term.
  (implies (and (rp-evlt (rp-apply-bindings (rp-hyp rule) bindings) a)
                (rp-termp term)
                (good-bindingsp rule term bindings a)
                (bindings-alistp bindings)
                (valid-rulep rule)
                (alistp a)
                (rp-rule-rwp rule)
                (rp-termp (rp-rhs rule)))
           (and (iff (rp-evlt (rp-apply-bindings (rp-rhs rule) bindings) a)
                     (rp-evlt term a))
                (iff (rp-evl (rp-apply-bindings (rp-rhs rule)
                                                (rp-trans-bindings bindings))
                             a)
                     (rp-evlt term a))))
  :hints (("goal"
           :use ((:instance valid-rulep-sk-necc
                            (a (bind-bindings (rp-trans-bindings bindings) a)))
                 (:instance rp-evl-of-rp-equal2
                            (term1 (rp-apply-bindings (rp-lhs rule) bindings))
                            (term2 term)
                            (a a)))
           :in-theory (e/d (valid-rulep
                            valid-rulesp
                            valid-rules-alistp
                            rule-syntaxp
                            rule-syntaxp-implies
                            rule-syntaxp-implies-2)
                           (rp-evl-of-rp-equal
                            rp-evl-of-rp-equal2
                            (:TYPE-PRESCRIPTION IS-RP$INLINE)
                            (:DEFINITION RP-TRANS-BINDINGS)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:DEFINITION IS-FALIST)
                            (:DEFINITION TRANS-LIST)
                            (:REWRITE RP-EVL-OF-LAMBDA)
                            (:REWRITE ACL2::FN-CHECK-DEF-NOT-QUOTE)
                            RP-EQUAL2-IS-symmetric
                            rp-rule-is-applicable-not-iff
                            (:REWRITE RP-APPLY-BINDINGS-EQUIV-NOT-IFF)
                            (:DEFINITION BIND-BINDINGS-AUX)
                            (:REWRITE VALID-RULEP-IMPLIES-VALID-SC)
                            (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS)
                            (:DEFINITION EVAL-AND-ALL)
                            (:REWRITE VALID-SC-CONS)
                            (:DEFINITION SUBSETP-EQUAL)
                            (:REWRITE NOT-INCLUDE-RP)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE RP-EVL-OF-VARIABLE)
                            (:REWRITE RP-EVL-OF-UNARY-/-CALL)
                            (:REWRITE RP-EVL-OF-UNARY---CALL)
                            (:REWRITE RP-EVL-OF-TYPESPEC-CHECK-CALL)
                            (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                            (:TYPE-PRESCRIPTION BIND-BINDINGS-AUX)
                            (:TYPE-PRESCRIPTION RP-TERMP)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC)
                            (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                            valid-rulep-sk-necc
                            ;;rp-equal-of-two-2
                            rp-equal-is-symmetric
                            pseudo-termp  rp-lhs rp-rhs rp-termp
                            rp-hyp)))))

(make-flag rp-get-dont-rw :defthm-macro-name defthm-rp-get-dont-rw)

(defthm-rp-get-dont-rw
  (defthm dont-rw-syntaxp-rp-get-dont-rw
    (dont-rw-syntaxp (rp-get-dont-rw term))
    :flag rp-get-dont-rw)

  (defthm dont-rw-syntaxp-rp-get-dont-rw-subterms
    (dont-rw-syntaxp (rp-get-dont-rw-subterm subterm))
    :flag rp-get-dont-rw-subterm)
  :hints (("Goal"
           :in-theory (e/d (DONT-RW-SYNTAXP
                            DONT-RW-SYNTAXP-AUX
                            RP-GET-DONT-RW-SUBTERM
                            rp-get-dont-rw) ()))))

(with-output
  :off (warning event  prove  observation)
  :gag-mode :goals
  :on error
  (defthm dont-rw-syntaxp-rp-rw-rule
    (implies (equal flag 'rp-rw-rule)
             (dont-rw-syntaxp
              (mv-nth 2 (rp-rw-rule term dont-rw rules-for-term context iff-flg
                                    outside-in-flg limit rp-state state))))
    :hints (("goal"
             :induct (flag-rp-rw flag rules-for-term
                                 outside-in-flg term iff-flg subterms
                                 dont-rw context hyp-flg limit rp-state state)
             :in-theory (e/d (rp-rw-rule
                              (:induction rp-rw-rule))
                             (remove-rp-from-bindings
                              rp-rw-relieve-synp
                              rp-rw-rule-aux
                              rp-apply-bindings))))))

(defthm rp-get-rules-for-term-returns-valid-rulesp
  (implies (valid-rules-alistp rules-alist)
           (valid-rulesp (rp-get-rules-for-term fn-name rules-alist)))
  :hints (("Goal" :in-theory (enable valid-rulesp
                                     hons-get
                                     hons-assoc-equal
                                     valid-rules-alistp))))

(local
 (defthmd rp-check-context-is-correct-iff-lemma
   (implies (case-match x (('equal & &) t))
            (equal (RP-TRANS x)
                   `(equal ,(rp-trans (cadr x))
                           ,(rp-trans (caddr x)))))))

(local
 (defthmd rp-check-context-is-correct-iff-lemma-2
   (implies (case-match x (('not &) t))
            (equal (RP-TRANS x)
                   `(not ,(rp-trans (cadr x)))))))

(local
 (defthmd rp-check-context-is-correct-iff-lemma-3
   (implies (case-match x (('if & ''nil ''t) t))
            (equal (RP-TRANS x)
                   `(if ,(rp-trans (cadr x)) 'nil 't)))))

(defthm rp-check-context-is-correct-iff
  (implies
   (and  (context-syntaxp context)
         iff-flg
         (eval-and-all context a))
   (iff (rp-evlt (rp-check-context term context iff-flg) a)
        (rp-evlt term a)))
  :hints ( ("Subgoal *1/3"
            :use ((:instance rp-evlt-of-rp-equal
                             (term1 (car context))
                             (term2 term))))
           ("Subgoal *1/2"
            :use ((:instance rp-evlt-of-rp-equal ;
                             (term2 (CADR (CAR CONTEXT))) ;
                             (term1 term))))
           ("goal"
            :in-theory (e/d (rp-check-context
                             context-syntaxp
                             rp-check-context-is-correct-iff-lemma
                             rp-check-context-is-correct-iff-lemma-2
                             rp-check-context-is-correct-iff-lemma-3
                             rp-termp
                             eval-and-all
                             is-falist)
                            (rp-term-listp-is-true-listp
                             rp-evl-of-rp-equal
                             rp-trans
                             rp-trans-lst
                             (:rewrite ex-from-synp-lemma1)
                             #|rp-trans-of-rp-equal||#
                             (:rewrite evl-of-extract-from-rp-2)
                             (:rewrite acl2::fn-check-def-not-quote)

                             (:rewrite
                              rp-termp-should-term-be-in-cons-lhs)
                             (:type-prescription booleanp)
                             (:rewrite rp-equal2-bindings-1to1-consp)
                             ;;all-falist-consistent-lst
                             falist-consistent
                             is-falist
                             rp-evlt-of-rp-equal
                             ;;rp-equal-is-symmetric
                             rp-termp-implies-subterms)))))

(defthm rp-check-context-is-correct
  (implies
   (and
    (context-syntaxp context)
    (eval-and-all context a))
   (equal (rp-evlt (rp-check-context term context nil) a)
          (rp-evlt term a)))
  :hints (("Goal"
           :in-theory (e/d (rp-check-context
                            CONTEXT-SYNTAXP
                            rp-termp
                            eval-and-all
                            IS-FALIST)
                           (RP-TERM-LISTP-IS-TRUE-LISTP

                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:REWRITE RP-EQUAL2-BINDINGS-1TO1-CONSP)
                            falist-consistent

                            RP-TERMP-IMPLIES-SUBTERMS)))))

(defthm VALID-SC-BINDINGS-REMOVE-RP-FROM-BINDINGS
  (implies (valid-sc-bindings bindings a)
           (valid-sc-bindings (REMOVE-RP-FROM-BINDINGS bindings) a))
  :hints (("Goal"
           :in-theory (e/d (valid-sc-bindings
                            remove-rp-from-bindings) ()))))

(encapsulate
  nil

  (local
   (in-theory (enable is-rp-implies-fc)))

  (local
   (defthm lemma1-lemma0
     (IMPLIES (AND (IS-RP TERM)
                   (EVAL-AND-ALL (CONTEXT-FROM-RP TERM NIL)
                                 A)
                   (RP-TERM-LISTP (CDR TERM))
                   (rp-termp TERM))
              (RP-EVLt (LIST (CADR (CADR TERM)) TERM)
                       A))
     :hints (("Goal"
              :expand ((CONTEXT-FROM-RP TERM NIL))
              :in-theory (e/d (EVAL-AND-ALL
                               is-rp
                               rp-evl-of-fncall-args)
                              (EX-FROM-RP-LEMMA1))))))

  (local
   (defthm lemma1-lemma1
     (IMPLIES (AND (IS-RP TERM)
                   (not (equal fnc 'quote))
                   (RP-EVLt (LIST FNC (CADDR TERM)) A)
                   (RP-TERMP (CADDR TERM))
                   (rp-termp (CADDR TERM)))
              (RP-EVLt (LIST FNC TERM) A))
     :hints (("Goal"
              :expand ((CONTEXT-FROM-RP TERM NIL))
              :in-theory (e/d (EVAL-AND-ALL
                               is-rp
                               rp-evl-of-fncall-args)
                              (EX-FROM-RP-LEMMA1))))))

  (local
   (defthm lemma1
     (implies (and (EVAL-AND-ALL (CONTEXT-FROM-RP term NIL) A)
                   (rp-termp term)
                   (not (equal fnc 'quote))
                   (rp-termp term)
                   (check-if-relieved-with-rp-aux fnc term))
              (rp-evlt `(,fnc ,term) a))
     :otf-flg t
     :hints (("Goal"
              :induct (check-if-relieved-with-rp-aux fnc term)
              :in-theory (e/d (check-if-relieved-with-rp-aux
                               eval-and-all
                               context-from-rp
                               quotep)
                              (ex-from-rp-lemma1
                               rp-trans))))))

  (defthm check-if-relieved-with-rp-is-correct
    (implies (and (check-if-relieved-with-rp term)
                  (valid-sc term a)
                  (rp-termp term))
             (rp-evlt term a))
    :hints (("Goal"

             :in-theory (e/d (check-if-relieved-with-rp
                              is-if
                              is-rp
                              check-if-relieved-with-rp-aux)
                             (rp-trans))))))

(local
 (in-theory
  (disable
   ;;rp-meta-valid-syntax-listp

   ;;valid-rp-meta-rule-listp

   rp-statep

   (:type-prescription rule-list-syntaxp)
   (:definition strip-cars)
   (:definition rp-rw-subterms)

   (:type-prescription context-syntaxp)
   (:rewrite default-<-1)
   (:type-prescription alistp)
   (:type-prescription true-list-listp)
   (:type-prescription eqlable-alistp)

   (:rewrite rp-term-listp-is-true-listp)

   (:definition assoc-equal)

   (:rewrite acl2::zp-open)

   (:type-prescription is-rp$inline)

   (:rewrite acl2::append-when-not-consp)
   (:rewrite acl2::append-atom-under-list-equiv)

   (:type-prescription is-if$inline)
   (:type-prescription rules-alistp)
   (:type-prescription rp-term-listp)
   (:type-prescription quote-listp)
   (:type-prescription quotep)

   (:type-prescription rp-termp)
   (:definition falist-consistent)
   (:definition no-free-variablep)
   (:type-prescription rule-list-list-syntaxp)
   (:definition rule-list-syntaxp)
   rule-syntaxp
   (:definition rule-list-list-syntaxp)
   (:rewrite rp-equal2-bindings-1to1-consp)
   (:definition get-vars)
   (:definition true-listp)
   (:definition include-fnc)
   (:definition subsetp-equal)
   (:rewrite
    rp-termp-should-term-be-in-cons-lhs)
   (:definition hons-assoc-equal)
   (:definition symbol-listp)
   (:definition symbol-alistp)
   #|(:definition RP-RW-APPLY-FALIST-META)||#
   (:definition is-falist)
   (:definition strip-cdrs)

   (:type-prescription is-falist)

   (:definition alistp)
   (:definition symbol-alistp)
   #|(:type-prescription rp-rw-apply-falist-meta)||#
   (:definition hons-get)
   (:definition rules-alistp)
   (:type-prescription falist-consistent)
   (:type-prescription true-listp)
   (:type-prescription zp)
   (:type-prescription hons-assoc-equal)
   (:type-prescription rp-rw-rule)
   (:type-prescription rp-ex-counterpart)
   (:REWRITE DEFAULT-+-2)
   (:REWRITE DEFAULT-+-1)
   (:TYPE-PRESCRIPTION RP-EXTRACT-CONTEXT)
   (:DEFINITION BINARY-APPEND)
   (:TYPE-PRESCRIPTION acl2::TRUE-LISTP-APPEND)
   ;(:TYPE-PRESCRIPTION RP-META-VALID-SYNTAX-LISTP)
   (:REWRITE ACL2::CONSP-OF-APPEND)
   (:REWRITE ACL2::CAR-OF-APPEND)
   (:TYPE-PRESCRIPTION BINARY-APPEND)
   (:FORWARD-CHAINING
    SYMBOL-ALISTP-FORWARD-TO-EQLABLE-ALISTP)
   (:FORWARD-CHAINING
    EQLABLE-ALISTP-FORWARD-TO-ALISTP)
   (:FORWARD-CHAINING
    ALISTP-FORWARD-TO-TRUE-LISTP)
   (:TYPE-PRESCRIPTION RP-RW-RELIEVE-SYNP)
   dumb-negate-lit2
   rp-rw-if
   rp-rw-rule
   rp-rw
   iff
   is-falist
   IS-HONSED-ASSOC-EQ-VALUES
   #|RP-RW-APPLY-FALIST-META||#
   nonnil-p
   EX-AND-EVAL-SC
   EX-AND-EVAL-SC-SUBTERMS
   (:type-prescription symbol-alistp)
   rp-trans
   rp-trans-lst)))

(encapsulate
  nil

  (local
   (in-theory (disable ACL2::CDR-OF-APPEND-WHEN-CONSP
                       RP-EQUAL
                       VALID-RULES-ALISTP-IMPLIES-RULES-ALISTP
                       RP-TERM-LISTP-APPEND
                       RP-EXTRACT-CONTEXT
                       RP-RW-RULE-AUX
                       IS-RP-PSEUDO-TERMP
                       IS-IF-RP-TERMP
                       IS-IF-RP-TERMP)))

  (with-output
    :off (warning event  prove  observation)
    :gag-mode nil
    :on error

    (defthm-rp-rw
      (defthm rp-rw-returns-valid-rp-statp
        (implies (rp-statep rp-state)
                 (rp-statep
                  (mv-nth 1 (rp-rw term dont-rw context iff-flg hyp-flg limit rp-state state))))
        :flag rp-rw)
      (defthm rp-rw-rule-retuns-valid-rp-statp
        (implies (rp-statep rp-state)
                 (rp-statep
                  (mv-nth 3 (rp-rw-rule term dont-rw rules-for-term context iff-flg outside-in-flg limit rp-state state))))
        :flag rp-rw-rule)

      (defthm rp-rw-if-retuns-valid-rp-statp
        (implies (rp-statep rp-state)
                 (rp-statep
                  (mv-nth 1 (rp-rw-if term dont-rw context iff-flg hyp-flg limit
                                      rp-state state))))
        :flag rp-rw-if)

      (defthm rp-rw-subterms-retuns-valid-rp-statp
        (implies (rp-statep rp-state)
                 (rp-statep
                  (mv-nth 1 (rp-rw-subterms subterms dont-rw context hyp-flg limit
                                            rp-state state))))
        :flag rp-rw-subterms)

      :hints (("goal"
               :expand ((rp-rw-rule term dont-rw rules-for-term
                                    context iff-flg outside-in-flg limit
                                    rp-state state)
                        (RP-RW-IF TERM DONT-RW CONTEXT
                                  IFF-FLG NIL LIMIT RP-STATE STATE)
                        (RP-RW-IF TERM DONT-RW
                                  CONTEXT IFF-FLG hyp-flg LIMIT RP-STATE STATE)
                        (rp-rw term dont-rw context iff-flg hyp-flg limit rp-state
                               state)
                        (RP-RW TERM DONT-RW
                               CONTEXT NIL hyp-flg LIMIT RP-STATE STATE)
                        (rp-rw-subterms subterms dont-rw context hyp-flg limit
                                        rp-state state))
               :in-theory (e/d (RP-STAT-ADD-TO-RULES-USED)
                               (;;update-rules-used
                                SHOW-USED-RULES-FLG
                                UPDATE-NTH
                                RP-STAT-ADD-TO-RULES-USED)))))))

(encapsulate
  nil

  (local
   (in-theory (disable ACL2::CDR-OF-APPEND-WHEN-CONSP
                       RP-EQUAL
                       VALID-RULES-ALISTP-IMPLIES-RULES-ALISTP
                       RP-TERM-LISTP-APPEND
                       RP-EXTRACT-CONTEXT
                       RP-RW-RULE-AUX
                       IS-RP-PSEUDO-TERMP
                       IS-IF-RP-TERMP
                       IS-IF-RP-TERMP)))

  (with-output
    :off (warning event  prove  observation)
    :gag-mode nil
    :on error

    (defthm-rp-rw
      (defthm rp-rw-returns-valid-valid-rp-state-syntaxp
        (implies (valid-rp-state-syntaxp rp-state)
                 (valid-rp-state-syntaxp
                  (mv-nth 1 (rp-rw term dont-rw context iff-flg hyp-flg limit rp-state state))))
        :flag rp-rw)
      (defthm rp-rw-rule-retuns-valid-valid-rp-state-syntaxp
        (implies (valid-rp-state-syntaxp rp-state)
                 (valid-rp-state-syntaxp
                  (mv-nth 3 (rp-rw-rule term dont-rw rules-for-term context iff-flg outside-in-flg limit rp-state state))))
        :flag rp-rw-rule)

      (defthm rp-rw-if-retuns-valid-valid-rp-state-syntaxp
        (implies (valid-rp-state-syntaxp rp-state)
                 (valid-rp-state-syntaxp
                  (mv-nth 1 (rp-rw-if term dont-rw context iff-flg hyp-flg limit
                                      rp-state state))))
        :flag rp-rw-if)

      (defthm rp-rw-subterms-retuns-valid-valid-rp-state-syntaxp
        (implies (valid-rp-state-syntaxp rp-state)
                 (valid-rp-state-syntaxp
                  (mv-nth 1 (rp-rw-subterms subterms dont-rw context hyp-flg limit
                                            rp-state state))))
        :flag rp-rw-subterms)

      :hints (("goal"
               :expand ((rp-rw-rule term dont-rw rules-for-term
                                    context iff-flg outside-in-flg limit
                                    rp-state state)
                        (RP-RW-IF TERM DONT-RW CONTEXT
                                  IFF-FLG NIL LIMIT RP-STATE STATE)
                        (RP-RW-IF TERM DONT-RW
                                  CONTEXT IFF-FLG hyp-flg LIMIT RP-STATE STATE)
                        (rp-rw term dont-rw context iff-flg hyp-flg limit rp-state
                               state)
                        (RP-RW TERM DONT-RW
                               CONTEXT NIL hyp-flg LIMIT RP-STATE STATE)
                        (rp-rw-subterms subterms dont-rw context hyp-flg limit
                                        rp-state state))
               :in-theory (e/d (RP-STAT-ADD-TO-RULES-USED)
                               (;;update-rules-used
                                SHOW-USED-RULES-FLG
                                UPDATE-NTH
                                RP-STAT-ADD-TO-RULES-USED)))))))

(encapsulate
  nil

  (local
   (in-theory (disable ACL2::CDR-OF-APPEND-WHEN-CONSP
                       RP-EQUAL
                       VALID-RULES-ALISTP-IMPLIES-RULES-ALISTP
                       RP-TERM-LISTP-APPEND
                       RP-EXTRACT-CONTEXT
                       RP-RW-RULE-AUX
                       IS-RP-PSEUDO-TERMP
                       IS-IF-RP-TERMP
                       IS-IF-RP-TERMP)))

  (with-output
    :off (warning event  prove  observation)
    :gag-mode nil
    :on error

    (defthm-rp-rw
      (defthm rp-rw-returns-valid-rp-statep
        (implies (and (valid-rp-statep rp-state)
                      (rp-statep rp-state))
                 (valid-rp-statep
                  (mv-nth 1 (rp-rw term dont-rw context iff-flg hyp-flg limit rp-state state))))
        :flag rp-rw)
      (defthm rp-rw-rule-retuns-valid-rp-statep
        (implies (and (valid-rp-statep rp-state)
                      (rp-statep rp-state))
                 (valid-rp-statep
                  (mv-nth 3 (rp-rw-rule term dont-rw rules-for-term context iff-flg outside-in-flg limit rp-state state))))
        :flag rp-rw-rule)

      (defthm rp-rw-if-retuns-valid-rp-statep
        (implies (and (valid-rp-statep rp-state)
                      (rp-statep rp-state))
                 (valid-rp-statep
                  (mv-nth 1 (rp-rw-if term dont-rw context iff-flg  hyp-flg limit
                                      rp-state state))))
        :flag rp-rw-if)

      (defthm rp-rw-subterms-retuns-valid-d-rp-statep
        (implies (and (valid-rp-statep rp-state)
                      (rp-statep rp-state))
                 (valid-rp-statep
                  (mv-nth 1 (rp-rw-subterms subterms dont-rw context hyp-flg limit
                                            rp-state state))))
        :flag rp-rw-subterms)

      :hints (("goal"
               :expand ((rp-rw-rule term dont-rw rules-for-term
                                    context iff-flg outside-in-flg limit
                                    rp-state state)
                        (RP-RW-IF TERM DONT-RW CONTEXT
                                  IFF-FLG NIL LIMIT RP-STATE STATE)
                        (RP-RW-IF TERM DONT-RW
                                  CONTEXT IFF-FLG hyp-flg LIMIT RP-STATE STATE)
                        (rp-rw term dont-rw context iff-flg hyp-flg limit rp-state
                               state)
                        (RP-RW TERM DONT-RW
                               CONTEXT NIL hyp-flg LIMIT RP-STATE STATE)
                        (rp-rw-subterms subterms dont-rw context hyp-flg limit
                                        rp-state state))
               :in-theory (e/d (RP-STAT-ADD-TO-RULES-USED)
                               (;;update-rules-used
                                SHOW-USED-RULES-FLG
                                UPDATE-NTH
                                VALID-RP-STATEP
                                RP-STAT-ADD-TO-RULES-USED)))))))

(DEFTHM
  RULE-SYNTAXP-IMPLIES-3
  (IMPLIES (AND (RULE-SYNTAXP RULE :WARNING nil)
                (NOT (RP-RULE-METAP RULE)))
           (AND (WEAK-CUSTOM-REWRITE-RULE-P RULE)
                (RP-TERMP (RP-HYP RULE))
                (RP-TERMP (RP-LHS RULE))
                (RP-TERMP (RP-RHS RULE))
                (NOT (INCLUDE-FNC (RP-LHS RULE) 'RP))
                (NOT (INCLUDE-FNC (RP-HYP RULE) 'RP))
                (NOT (INCLUDE-FNC (RP-RHS RULE) 'FALIST))
                (NOT (INCLUDE-FNC (RP-HYP RULE) 'FALIST))
                ;;(NOT (INCLUDE-FNC (RP-LHS RULE) 'IF))
                (NOT (INCLUDE-FNC (RP-LHS RULE) 'SYNP))
                #|(NO-FREE-VARIABLEP RULE)|#
                (NOT (INCLUDE-FNC (RP-LHS RULE) 'LIST))
                (NOT (INCLUDE-FNC (RP-HYP RULE) 'LIST))
                (NOT (INCLUDE-FNC (RP-RHS RULE) 'LIST))))
  :RULE-CLASSES (:REWRITE :FORWARD-CHAINING)
  :HINTS (("Goal" :IN-THEORY (ENABLE RULE-SYNTAXP))))

(defthm valid-rp-state-syntaxp-when-rules-are-retrieved
  (implies (and (valid-rp-state-syntaxp rp-state)
                (symbolp key))
           (and (rule-list-syntaxp (rules-alist-outside-in-get key rp-state))
                (rule-list-syntaxp (rules-alist-inside-out-get key rp-state))))
  :hints (("Goal"
           :use ((:instance VALID-RP-STATE-SYNTAXP-AUX-necc))
           :in-theory (e/d (valid-rp-state-syntaxp)
                           (rp-statep
                            VALID-RP-STATE-SYNTAXP-AUX)))))

(defthm rp-termp-implies-symbol-car-term
  (implies (rp-termp term)
           (symbolp (car term)))
  :hints (("Goal"
           :in-theory (e/d () ()))))

(encapsulate
  nil

  (local
   (in-theory (disable ACL2::CDR-OF-APPEND-WHEN-CONSP
                       RP-EQUAL
                       VALID-RULES-ALISTP-IMPLIES-RULES-ALISTP
                       RP-TERM-LISTP-APPEND
                       RP-EXTRACT-CONTEXT
                       RP-RW-RULE-AUX
                       IS-RP-PSEUDO-TERMP
                       IS-IF-RP-TERMP
                       IS-IF-RP-TERMP)))

  (local
   (in-theory (enable ;rp-rw
               ;;rp-rw-rule
               context-syntaxp
               rule-syntaxp-implies
               quotep)))

  (local
   (defthm lemma1
     (implies (and (consp term))
              (CONSP (MV-NTH 0
                             (RP-EX-COUNTERPART term
                                                rp-state STATE))))
     :hints (("Goal" :in-theory (enable rp-ex-counterpart)))))

  (local
   (defthm lemma2
     (implies (and (rp-term-listp subterms))
              (rp-termp (cons 'hide subterms)))
     :hints (("Goal"
              :in-theory (enable rp-term-listp rp-termp true-listp)
              :expand (rp-termp (cons 'hide subterms))))))

  (local
   (defthm lemma7
     (not (is-falist (cons 'if rest)))
     :hints (("Goal" :in-theory (enable is-falist)))))

  (local
   (defthm lemma8
     (not (is-falist (cons 'not rest)))
     :hints (("Goal" :in-theory (enable is-falist)))))

  (defthm rp-termp-is-if-lemma
    (implies (and (is-if term)
                  (rp-termp term))
             (and (rp-termp (cadr term))
                  (rp-termp (caddr term))
                  (rp-termp (cadddr term))))
    :hints (("goal"
             :in-theory (e/d (is-if) ()))))

  (local
   (in-theory (disable
               (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
               (:REWRITE ACL2::FN-CHECK-DEF-NOT-QUOTE)
               (:REWRITE NOT-INCLUDE-RP)
               #|||#

               )))

  (defthm rp-termp-with-if
    (equal (rp-termp (cons 'if rest))
           (rp-term-listp rest))
    :hints (("Goal"
             :in-theory (e/d (rp-term-listp
                              rp-termp
                              falist-consistent
                              is-rp) ()))))

  (defthm is-rp-rp-rw-subterms
    (implies (is-rp (cons 'rp subterms))
             (is-rp (cons 'rp (mv-nth 0 (rp-rw-subterms SUBTERMS DONT-RW
                                                        CONTEXT hyp-flg LIMIT
                                                        rp-state STATE)))))
    :hints (("Goal"
             :do-not-induct t
             :expand ((rp-rw-subterms SUBTERMS DONT-RW CONTEXT hyp-flg LIMIT
                                      rp-state
                                      STATE)
                      (RP-RW-SUBTERMS (CDR SUBTERMS)
                                      (dont-rw-cdr DONT-RW)
                                      CONTEXT hyp-flg (+ -1 LIMIT)
                                      RP-STATE STATE)
                      (RP-RW-SUBTERMS (CDR SUBTERMS)
                                      NIL CONTEXT hyp-flg (+ -1 LIMIT)
                                      RP-STATE STATE)
                      (RP-RW (CAR SUBTERMS)
                             (dont-rw-car DONT-RW)
                             CONTEXT hyp-flg (+ -1 LIMIT)
                             NIL RP-STATE STATE)
                      (RP-RW (CAR SUBTERMS)
                             NIL CONTEXT hyp-flg (+ -1 LIMIT)
                             NIL RP-STATE STATE))
             :in-theory (e/d (is-rp
                              RP-RW-SUBTERMS
                              RP-RW) ()))))

  (defthm RP-EX-COUNTERPART-is-term-when-is-if
    (implies (is-if (MV-NTH 0 (RP-EX-COUNTERPART term
                                                 RP-STATE STATE)))
             (is-if term))
    :rule-classes :forward-chaining
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (RP-EX-COUNTERPART
                              is-if
                              RP-RW) ()))))

  (defthm RP-EX-COUNTERPART-is-term-not-quotep
    (implies (not (equal (car (MV-NTH 0 (RP-EX-COUNTERPART term
                                                           RP-STATE STATE)))
                         'quote))
             (equal (MV-NTH 0 (RP-EX-COUNTERPART term
                                                 RP-STATE
                                                 STATE))
                    term))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (RP-EX-COUNTERPART
                              RP-RW) ()))))

  (defthm RP-EX-COUNTERPART-is-term-not-quotep-1
    (implies (and (equal (car (MV-NTH 0 (RP-EX-COUNTERPART term
                                                           RP-STATE STATE)))
                         x)
                  x
                  (not (equal x 'quote)))
             (equal (car term)
                    x))
    :rule-classes :forward-chaining
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (RP-EX-COUNTERPART
                              RP-RW) ()))))

  (defthm rp-termp-and-is-rp-lemma
    (implies (and (rp-termp x)
                  (equal (car x) 'rp))
             (is-rp (cons 'rp (cdr x))))
    :hints (("Goal"
             :in-theory (e/d (is-rp rp-termp) ()))))

  (with-output
    :off (warning event  prove  observation)
    :gag-mode :goals
    :on error
    (defthm-rp-rw
      (defthm rp-termp-rp-rw
        (implies (and (RP-TERMP TERM)
                      (CONTEXT-SYNTAXP CONTEXT)
                      (valid-rp-state-syntaxp rp-state))
                 (let ((res (mv-nth 0
                                    (rp-rw term dont-rw context iff-flg hyp-flg limit rp-state state))))
                   (and (rp-termp res)

                        )))
        :flag rp-rw)

      (defthm rp-termp-rp-rw-rule
        (implies (and (RP-TERMP TERM)
                      (RULE-LIST-SYNTAXP RULES-FOR-TERM)
                      (CONTEXT-SYNTAXP CONTEXT)
                      (valid-rp-state-syntaxp rp-state)
                      )
                 (let ((res (mv-nth 1
                                    (rp-rw-rule TERM dont-rw RULES-FOR-TERM
                                                CONTEXT IFF-FLG outside-in-flg
                                                LIMIT rp-state STATE))))
                   (and (rp-termp res)

                        )))
        :flag rp-rw-rule)

      (defthm rp-termp-rp-rw-if
        (implies (and (rp-termp term)

                      (context-syntaxp context)

                      (valid-rp-state-syntaxp rp-state))
                 (let ((res (mv-nth 0
                                    (rp-rw-if term dont-rw context  iff-flg
                                              hyp-flg limit rp-state state))))
                   (and (rp-termp res)

                        )))
        :flag rp-rw-if)

      (defthm rp-termp-rp-rw-subterms
        (implies (and (RP-TERM-LISTP SUBTERMS)
                      (context-syntaxp context)
                      (valid-rp-state-syntaxp rp-state))
                 (let ((res (mv-nth 0 (rp-rw-subterms SUBTERMS DONT-RW CONTEXT hyp-flg LIMIT
                                                      rp-state STATE))))
                   (and (rp-term-listp res)

                        )))
        :flag rp-rw-subterms)

      :hints (("Goal"
               :in-theory (e/d (RP-TERM-LISTP-APPEND
                                is-if-implies)
                               (rp-termp
                                is-rp
                                rp-rule-metap))
               :expand
               ((RP-RW-IF TERM DONT-RW CONTEXT
                          IFF-FLG NIL LIMIT RP-STATE STATE)
                (rp-rw-subterms nil dont-rw context hyp-flg limit
                                rp-state state)
                (rp-rw-if term dont-rw context
                          iff-flg hyp-flg limit rp-state state)
                (rp-rw-subterms subterms dont-rw context hyp-flg limit
                                rp-state state)
                (rp-rw term dont-rw context
                       nil hyp-flg limit rp-state state)
                (rp-rw-rule term dont-rw
                            rules-for-term context iff-flg outside-in-flg  limit rp-state state)
                (rp-rw-rule term dont-rw nil context iff-flg  outside-in-flg limit rp-state state)
                (rp-rw term t context iff-flg hyp-flg limit rp-state state)
                (rp-rw term dont-rw context  iff-flg hyp-flg limit rp-state state)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm rp-evl-of-extract-context
  (iff (eval-and-all (rp-extract-context term) a)
       (rp-evlt term a))
  :hints (("Goal"
           :induct (rp-extract-context term)
           :do-not-induct t
           :in-theory (e/d (rp-extract-context
                            eval-and-all
                            rp-trans
                            rp-trans-lst
                            is-falist)
                           ()))))

(local
 (defthm hide-x-is-x
   (equal (hide x) x)
   :hints (("Goal"
            :expand (hide x)))))

(defthm rp-evl-of-dumb-negate-lit2
  (implies (rp-termp x)
           (iff (rp-evlt (dumb-negate-lit2 x) a)
                (not (rp-evlt x a))))
  :hints (("Goal"
           :in-theory (e/d (dumb-negate-lit2
                            not
                            rp-trans-lst
                            rp-trans
                            is-falist)
                           ()))))

(local
 (in-theory (disable acl2::cdr-of-append-when-consp
                     rp-equal
                     valid-rules-alistp-implies-rules-alistp
                     rp-term-listp-append
                     rp-extract-context
                     rp-rw-rule-aux
                     is-rp-pseudo-termp
                     is-if-rp-termp
                     is-if-rp-termp)))

(local
 (defthm lemma2
   (implies (consp TERM)
            (consp (mv-nth 0 (RP-EX-COUNTERPART term rp-state STATE))))
   :hints (("Goal"
            :in-theory (e/d (rp-ex-counterpart) ())))))

(local
 (defthm lemma4-v1
   (implies (and (consp term)
                 (not (quotep term))
                 (equal (rp-evl-lst (cdr term) a)
                        (rp-evl-lst subterms2 a)))
            (equal (rp-evl (cons (car term) subterms2) a)
                   (rp-evl term a)))
   :hints (("Goal"
            :in-theory (e/d (rp-evl-of-fncall-args
                             rp-trans
                             rp-trans-lst)
                            ())))))

(local
 (defthmd lemma4-lemma
   (iff (RP-EVL-LST (RP-TRANS-LST SUBTERMS) A)
        (consp subterms))
   :hints (("Goal"
            :induct (len subterms)
            :do-not-induct t
            :in-theory (e/d () ())))))

(local
 (defthm lemma4
   (implies (and (consp term)
                 (not (quotep term))
                 (equal (rp-evlt-lst (cdr term) a)
                        (rp-evlt-lst subterms2 a)))
            (equal (rp-evlt (cons (car term) subterms2) a)
                   (rp-evlt term a)))
   :otf-flg t
   :hints (("Goal"
            :cases ((is-falist term))
            :in-theory (e/d (rp-evl-of-fncall-args
                             rp-trans
                             is-falist
                             rp-trans-lst
                             lemma4-lemma)
                            (trans-list
                             ))))))

(local
 (defthm lemma5
   (implies (is-falist term)
            (not (rp-termp (cadddr term))))
   :hints (("Goal"
            :in-theory (e/d (is-falist) ())))))

(local
 (defthm lemma6
   (implies (nonnil-p term)
            (rp-evl term a))
   :hints (("Goal"
            :in-theory (e/d (nonnil-p) ())))))

(local
 (defthm lemma6-v2
   (implies (nonnil-p term)
            (rp-evlt term a))
   :hints (("Goal"
            :in-theory (e/d (nonnil-p
                             rp-trans
                             is-falist)
                            ())))))

(local
 (in-theory (enable
             rp-term-listp-append
             rule-syntaxp-implies)))

(defthm valid-sc-dumb-negate-lit2
  (implies (valid-sc term a)
           (valid-sc (dumb-negate-lit2 term) a))
  :hints (("Goal"
           :expand ((VALID-SC (LIST 'NOT TERM) A))
           :in-theory (e/d (valid-sc
                            is-rp
                            is-if
                            dumb-negate-lit2)
                           ()))))

(encapsulate
  nil

  (local

   (defthm lemma1
     (implies (and (consp context)
                   (consp (car context))
                   (equal (car (car context)) 'equal)
                   (consp (cdr (car context)))
                   (consp (cddr (car context)))
                   (not (cdddr (car context)))
                   (valid-sc (cadr (car context)) a)
                   (valid-sc-subterms context a))
              (valid-sc (caddr (car context)) a))
     :hints (("goal"
              :expand ((valid-sc-subterms context a)
                       (valid-sc (car context) a))
              :in-theory (e/d (is-if is-rp) ())))))

  (local
   (defthm l-lemma2
     (implies (and (consp context)
                   (consp (car context))
                   (equal (car (car context)) 'equal)
                   (consp (cdr (car context)))
                   (consp (cddr (car context)))
                   (not (cdddr (car context)))
                   (rp-equal term (cadr (car context)))
                   (valid-sc term a)
                   (valid-sc-subterms context a))
              (valid-sc (caddr (car context)) a))
     :hints (("goal"
              :expand ((valid-sc-subterms context a)
                       (valid-sc (car context) a))
              :in-theory (e/d (is-if is-rp) ())))))

  (defthm valid-sc-rp-check-context
    (implies (and (valid-sc term a)
                  (valid-sc-subterms context a))
             (valid-sc (rp-check-context term context iff-flg) a))
    :hints (("goal"
             :expand ()
             :in-theory (e/d (rp-check-context) ()))))

  (defthm valid-sc-dumb-negate-lit2
    (implies (valid-sc term a)
             (valid-sc (dumb-negate-lit2 term) a))
    :hints (("goal"
             :expand ((valid-sc (list 'not term) a))
             :in-theory (e/d (valid-sc
                              is-rp
                              is-if
                              dumb-negate-lit2)
                             ())))))

(local
 (defthm lemma0
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
 (defthm lemma1
   (implies (and (valid-sc term a)
                 (consp term)
                 (not (eq (car term) 'quote))
                 (not (is-if term)))
            (valid-sc-subterms (cdr term) a))
   :hints (("goal"
            :expand ((valid-sc term a)
                     (ex-from-rp term))
            :in-theory (e/d (is-rp) ())))))

(encapsulate
  nil
  (local
   (defthm i-lemma1
     (implies (and (equal (car term) 'rp)
                   (rp-termp term))
              (case-match term
                (('rp ('quote type) &)
                 (and (symbolp type)
                      (not (booleanp type))
                      (not (equal type 'quote))
                      (not (equal type 'falist))
                      (not (equal type 'rp))))
                (& nil)))
     :hints (("goal"
              :in-theory (e/d (is-rp) ())))
     :rule-classes :forward-chaining))

  (local
   (defthm i-lemma2
     (implies
      (and (equal (car term) 'rp)
           (rp-termp term))
      (equal (mv-nth 0 (rp-rw (cadr term)
                              dont-rw
                              context
                              iff-flg hyp-flg limit rp-state state))
             (cadr term)))
     :hints (("goal"
              :expand (rp-rw (cadr term)
                             dont-rw
                             context
                             iff-flg hyp-flg limit rp-state state)
              :in-theory (e/d () ())))))

  (defthm eval-and-all-context-from-when-valid-sc
    (implies (valid-sc term a)
             (eval-and-all (context-from-rp term nil) a))
    :hints (("goal"
             :cases ((is-rp term))
             :in-theory (e/d (context-from-rp
                              is-rp
                              is-if
                              valid-sc)
                             (ex-from-rp-lemma1
                              valid-sc-subterms)))))

  (local
   (defthmd i-lemma3-lemma1
     (implies (IS-RP (LIST 'RP CADR-TERM x))
              (IS-RP (LIST 'RP CADR-TERM y)))
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))

  (local
   (defthmd i-lemma3-lemma2
     (implies (IS-RP (LIST 'RP CADR-TERM '(NIL)))
              (not (EQUAL (CADR CADR-TERM) 'QUOTE)))
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))

  (local
   (defthmd i-lemma3-lemma3
     (IMPLIES (AND (NOT (IS-RP (LIST 'RP CADR-TERM RP-RW-CADDR-TERM)))
                   (EQUAL (RP-EVL (RP-TRANS RP-RW-CADDR-TERM) A)
                          (RP-EVL (RP-TRANS CADDR-TERM) A))
                   (VALID-SC RP-RW-CADDR-TERM A)
                   (VALID-SC (LIST 'RP CADR-TERM CADDR-TERM)
                             A))
              (VALID-SC (LIST 'RP CADR-TERM RP-RW-CADDR-TERM)
                        A))
     :hints (("Goal"
              :expand ((VALID-SC (LIST 'RP CADR-TERM RP-RW-CADDR-TERM)
                                 A)
                       (VALID-SC (LIST 'RP CADR-TERM CADDR-TERM)
                                 A))
              :in-theory (e/d (is-if
                               i-lemma3-lemma1
                               i-lemma3-lemma2) ())))))

  (local
   (defthm i-lemma3
     (implies (and (equal (rp-evlt rp-rw-caddr-term a)
                          (rp-evlt caddr-term a))
                   (valid-sc rp-rw-caddr-term a)
                   (valid-sc term a)

                   (equal term (list 'rp cadr-term caddr-term)))
              (valid-sc (list 'rp cadr-term rp-rw-caddr-term) a))
     :otf-flg t
     :hints (("goal"
              :do-not-induct t
              :cases ((is-rp (list 'rp cadr-term rp-rw-caddr-term)))
              :use (
                    (:instance valid-sc-single-step
                               (term (list 'rp cadr-term rp-rw-caddr-term))))
              :expand ((ex-from-rp (list 'rp cadr-term caddr-term))
                       (RP-TRANS (LIST (CADR CADR-TERM)
                                       RP-RW-CADDR-TERM))
                       (:free (CADDR-TERM)
                              (RP-TRANS (LIST 'LIST CADDR-TERM)))
                       (RP-TRANS (LIST (CADR CADR-TERM)
                                       (EX-FROM-RP RP-RW-CADDR-TERM)))
                       (RP-TRANS (LIST (CADR CADR-TERM)
                                       (EX-FROM-RP CADDR-TERM)))
                       (RP-TRANS-LST (LIST CADDR-TERM))
                       (RP-TRANS (LIST (CADR CADR-TERM) CADDR-TERM))
                       (RP-TRANS-LST (LIST RP-RW-CADDR-TERM))
                       (:free (x) (RP-TRANS (LIST 'QUOTE x)))
                       (RP-TRANS-LST (LIST (EX-FROM-RP RP-RW-CADDR-TERM))))
              :in-theory (e/d (i-lemma3-lemma1
                               i-lemma3-lemma2
                               i-lemma3-lemma3
                               rp-evl-of-fncall-args
                               is-falist
                               valid-sc-single-step
                               )
                              (evl-of-extract-from-rp
                               valid-sc-ex-from-rp-2
                               valid-sc))))))

  (local
   (defthmd ilemma4-1
     (implies (and (is-rp term)
                   (valid-sc term a))
              (valid-sc (caddr term) a))
     :hints (("Goal"
              :in-theory (e/d (valid-sc-single-step) ())))))

  (local
   (defthm ilemma4
     (implies (and (valid-sc term a)
                   (eval-and-all context a))
              (eval-and-all (CONTEXT-FROM-RP term context) a))
     :otf-flg t
     :hints (("Goal"
              :induct (context-from-rp term context)
              :do-not-induct t
              :in-theory (e/d (context-from-rp
                               valid-sc
                               ilemma4-1
                               is-rp
                               is-if)
                              (valid-sc-ex-from-rp-2
                               rp-evlt-cons))))))

  (defthm valid-sc-cons-car-term-and-rp-rw-subterms
    (implies
     (and
      (valid-sc term a)
      (consp term)
      (rp-termp term)
      (equal (rp-evlt-lst
              (mv-nth 0 (rp-rw-subterms (cdr term) dont-rw context hyp-flg limit
                                        rp-state state))
              a)
             (rp-evlt-lst (cdr term) a))
      (valid-sc-subterms
       (mv-nth 0 (rp-rw-subterms (cdr term) dont-rw context hyp-flg limit
                                 rp-state state))
       a))
     (valid-sc
      (cons (car term)
            (mv-nth  0 (rp-rw-subterms (cdr term) dont-rw context hyp-flg limit
                                       rp-state state)))
      a))
    :otf-flg t
    :hints (("goal"
             :do-not-induct t
             :expand ((valid-sc term a)
                      (:free (x y) (RP-TRANS-LST (cons x y)))
                      (:free (x y) (valid-sc (cons x y) a))
                      (:free (x y) (EX-FROM-RP (list 'rp x y)))
                      (RP-RW-SUBTERMS (CDDR TERM)
                                      NIL CONTEXT hyp-flg (+ -1 LIMIT)
                                      (MV-NTH 1
                                              (RP-RW (CADR TERM)
                                                     NIL CONTEXT
                                                     NIL hyp-flg (+ -1 LIMIT) rp-state STATE))
                                      STATE)
                      (rp-rw-subterms (cddr term)
                                      (dont-rw-cdr dont-rw)
                                      context hyp-flg (+ -1 limit)

                                      (mv-nth 1
                                              (rp-rw (cadr term)
                                                     (dont-rw-car dont-rw)
                                                     context
                                                     nil hyp-flg (+ -1 limit) rp-state state))
                                      state)
                      (rp-rw-subterms (cdr term)
                                      dont-rw context hyp-flg limit
                                      rp-state state))
             :in-theory (e/d (is-rp
                              is-if
                              is-falist
                              ;;dont-rw-CaR dont-rw-cdr
                              context-from-rp
                              RP-TRANS-LST
                              rp-evl-of-fncall-args
                              rp-trans
                              rp-rw
                              rp-rw-subterms)
                             (rp-rw
                              valid-sc
                              (:REWRITE ACL2::O-P-O-INFP-CAR)
                              (:REWRITE
                               EVAL-AND-ALL-CONTEXT-FROM-WHEN-VALID-SC)
                              (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                              (:REWRITE RP-TERMP-IS-IF-LEMMA)
                              (:REWRITE VALID-SC-CADR)
                              (:TYPE-PRESCRIPTION INCLUDE-FNC)
                              (:REWRITE EVAL-AND-ALL-CONTEXT-FROM-RP)
                              (:TYPE-PRESCRIPTION VALID-SC)
                              (:REWRITE LEMMA0)
                              (:REWRITE NOT-INCLUDE-RP)
                              (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                              (:REWRITE RP-TERMP-CADDR)
                              (:REWRITE VALID-SC-OF-EX-FROM-RP)
                              (:REWRITE LEMMA4-V1)
                              (:REWRITE RP-TERMP-CADR)
                              (:REWRITE ACL2::SYMBOL-LISTP-IMPLIES-SYMBOLP)
                              VALID-SC-EX-FROM-RP-2
                              ex-from-rp-lemma1))))))

(local
 (defthm lemma106
   (is-if (list 'if x y z))
   :hints (("goal"
            :in-theory (e/d (is-if) ())))))

(local
 (defthm lemma108
   (implies (and
             (valid-sc term a)
             (not (rp-evlt (cadr term) a))
             (is-if term))
            (valid-sc (cadddr term) a))
   :hints (("goal"
            :in-theory (e/d (valid-sc
                             is-if)
                            ())))))

(local
 (defthm lemma109
   (implies (and
             (valid-sc term a)
             (rp-evlt (cadr term) a)
             (is-if term))
            (valid-sc (caddr term) a))
   :hints (("goal"
            :in-theory (e/d (valid-sc
                             is-if)
                            ())))))

(defthm is-if-implies
  (implies (is-if term)
           (case-match term (('if & & &) t)
             (& nil)))
  :rule-classes :forward-chaining
  :hints (("goal"
           :in-theory (e/d (is-if) ()))))

(local
 (in-theory (disable rp-apply-bindings-to-evl
                     rp-apply-bindings-subterms-to-evl-lst)))

(local
 (in-theory
  (disable

   (:rewrite rp-termp-implies-cdr-listp)

   (:type-prescription include-fnc-subterms)
   (:type-prescription include-fnc)
   (:rewrite rp-evl-of-rp-equal)
   )))

(local
 (in-theory
  (e/d (context-syntaxp
        is-if-implies
        valid-rules-alistp-implies-rules-alistp)
       (iff))))

(local
 (defthm rp-evl-of-nil
   (equal (rp-evlt ''nil a)
          nil)))

(local
 (defthm if-is-not-falist
   (not (is-falist (cons 'if x)))
   :hints (("Goal"
            :in-theory (e/d (is-falist) ())))))

(local
 (defthm is-if-and-rp-trans
   (implies (and (is-if term)
                 (syntaxp (atom term)))
            (equal (RP-TRANS TERM)
                   `(if ,(rp-trans (cadr term))
                        ,(rp-trans (caddr term))
                      ,(rp-trans (cadddr term)))))

   :hints (("Goal"
            :expand ((RP-TRANS TERM)
                     (RP-TRANS-LST (CDR TERM))
                     (RP-TRANS-LST (CDDR TERM))
                     (RP-TRANS-LST (CDDDR TERM)))
            :in-theory (e/d (is-falist
                             is-if) ())))))

(local
 (defthm rp-eVL-OF-NIL-2
   (EQUAL (RP-EVL ''NIL A)
          NIL)))

(local
 (in-theory (disable RP-RULE-METAP$INLINE)))

(defthm RULE-SYNTAXP-IMPLIES-rp-termp-rp-hyp
  (implies (and (RULE-SYNTAXP rule)
                (rp-rule-rwp rule))
           (rp-termp (rp-rhs rule)))
  :hints (("Goal"
           :in-theory (e/d (RULE-SYNTAXP) ()))))

(defthm valid-rp-statep-when-rules-are-retrieved
  (implies (and (valid-rp-statep rp-state)
                (symbolp key))
           (and (valid-rulesp (rules-alist-outside-in-get key rp-state))
                (valid-rulesp (rules-alist-inside-out-get key rp-state))))
  :hints (("Goal"
           :use ((:instance VALID-RP-STATEp-necc))
           :in-theory (e/d ()
                           (rp-statep
                            VALID-RP-STATEp)))))

(local
 (in-theory (disable valid-rp-statep)))

(local
 (defthm rp-term-listp-cdr
   (implies (rp-term-listp lst)
            (rp-term-listp (cdr lst)))))

(local
 (defthm valid-rp-statep-implies-valid-rp-state-syntaxp
   (implies (and (rp-statep rp-state)
                 (valid-rp-statep rp-state))
            (valid-rp-state-syntaxp rp-state))
   :otf-flg nil
   :hints (("Goal"
            :use ((:instance valid-rp-statep-necc
                             (key (valid-rp-state-syntaxp-aux-witness RP-STATE))))
            :in-theory (e/d (VALID-RP-STATE-SYNTAXP)
                            ())))))

(with-output
  :off (warning event  prove  observation)
  :gag-mode :goals
  :on error
  (defthm-rp-rw
    (defthm rp-evl-and-side-cond-consistent-of-rp-rw
      (implies (and (rp-termp term)
                    (RP-STATEP RP-STATE)
                    (alistp a)

                    (rp-evl-meta-extract-global-facts :state state)
                    (eval-and-all context a)

                    (valid-sc term a)
                    (context-syntaxp context)
                    (valid-sc-subterms context a)

                    (rp-formula-checks state)

                    (valid-rp-statep rp-state))
               (let ((res
                      (mv-nth 0
                              (rp-rw term dont-rw context  iff-flg hyp-flg limit rp-state state))))
                 (and (valid-sc res a)
                      (implies iff-flg
                               (iff (rp-evlt res a) (rp-evlt term a)))
                      (implies (not iff-flg)
                               (equal (rp-evlt res a) (rp-evlt term a))))))
      :flag rp-rw)

    (defthm rp-evl-and-side-cond-consistent-rp-rw-rule
      (implies (and (rp-termp term)
                    (RP-STATEP RP-STATE)
                    (alistp a)

                    (rp-evl-meta-extract-global-facts :state state)
                    (valid-rulesp rules-for-term)
                    (context-syntaxp context)

                    (valid-sc-subterms context a)

                    (rp-formula-checks state)

                    (eval-and-all context a)
                    (valid-sc term a)
                    (valid-rp-statep rp-state))
               (let ((res
                      (mv-nth 1
                              (rp-rw-rule term dont-rw rules-for-term context
                                          iff-flg outside-in-flg  limit rp-state state))))
                 (and (valid-sc res a)
                      (implies iff-flg
                               (iff (rp-evlt res a) (rp-evlt term a)))
                      (implies (not iff-flg)
                               (equal (rp-evlt res a) (rp-evlt term a))))))
      :flag rp-rw-rule)

    (defthm rp-evl-and-side-cond-consistent-rp-rw-if
      (implies (and (rp-termp term)
                    (RP-STATEP RP-STATE)
                    (alistp a)

                    (rp-evl-meta-extract-global-facts :state state)
                    (context-syntaxp context)

                    (valid-sc-subterms context a)

                    (rp-formula-checks state)

                    (eval-and-all context a)
                    (valid-sc term a)
                    (valid-rp-statep rp-state))
               (let ((res
                      (mv-nth 0
                              (rp-rw-if term dont-rw context iff-flg hyp-flg limit rp-state state))))
                 (and  (valid-sc res a)
                       (implies iff-flg
                                (iff (rp-evlt res a) (rp-evlt term a)))
                       (implies (not iff-flg)
                                (equal (rp-evlt res a) (rp-evlt term a))))))
      :flag rp-rw-if)

    (defthm rp-evl-and-side-cond-consistent-rp-rw-subterms
      (implies (and (rp-term-listp subterms)
                    (RP-STATEP RP-STATE)
                    (alistp a)

                    (rp-evl-meta-extract-global-facts :state state)
                    (context-syntaxp context)
                    (valid-sc-subterms context a)

                    (eval-and-all context a)
                    (valid-rp-statep rp-state)

                    (rp-formula-checks state)

                    (valid-sc-subterms subterms a)
                    )
               (let ((res
                      (mv-nth 0 (rp-rw-subterms subterms dont-rw context hyp-flg limit
                                                rp-state state))))
                 (and (valid-sc-subterms res a)
                      (equal (rp-evlt-lst res a) (rp-evlt-lst subterms a)))))
      :flag rp-rw-subterms)
    :otf-flg nil
    :hints (("goal"
             :induct (FLAG-RP-RW FLAG RULES-FOR-TERM
                                 OUTSIDE-IN-FLG TERM IFF-FLG SUBTERMS
                                 DONT-RW CONTEXT hyp-flg LIMIT RP-STATE STATE)
             :do-not-induct t
             :in-theory (e/d (rp-evl-of-fncall-args
                              rp-rule-rwp
                              rp-term-listp)
                             (rp-evl-of-quote
                              RP-TRANS-LST
                              rp-termp
                              is-rp
                              rp-evl-of-variable
                              (:rewrite acl2::o-p-o-infp-car)
                              (:definition eval-and-all)
                              (:type-prescription valid-sc)
                              (:type-prescription ex-from-synp)
                              (:type-prescription valid-sc-subterms)
                              (:type-prescription is-hide)
                              (:type-prescription o<)
                              (:type-prescription eval-and-all)
                              (:type-prescription valid-rules-alistp)
                              ;(:type-prescription valid-rp-meta-rule-listp)
                              (:type-prescription should-not-rw$inline)
                              (:rewrite valid-sc-cons)
                              (:rewrite not-include-rp-means-valid-sc)
                              (:forward-chaining
                               acl2::|a <= b & ~(a = b)  =>  a < b|)
                              (:type-prescription check-if-relieved-with-rp)
                              (:rewrite not-include-rp)
                              (:rewrite evl-of-extract-from-rp-2)
                              (:rewrite acl2::fn-check-def-not-quote)
                              (:rewrite rp-evl-of-rp-equal-subterms)
                              (:rewrite not-include-rp-means-valid-sc-lst)
                              (:rewrite rp-equal-subterms-is-symmetric)
                              (:rewrite rp-evl-of-rp-equal-loosesubterms)
                              (:type-prescription is-rp-loose$inline)
                              rp-evlt-of-apply-bindings-to-evl
                              (:rewrite
                               rp-ex-counterpart-is-term-not-quotep)
                              rp-trans
                              rp-trans-lst
                              rp-trans-of-rp-apply-bindings
                              (:rewrite rp-evl-of-rp-equal2-subterms)))
             :expand
             (
               (:free (x y z)
                     (valid-sc (list 'if x y z) a))
              (:free (x y)
                     (RP-TRANS-LST (cons x y)))
              (:free (x y z)
                     (RP-TRANS (list 'if x y z)))
              (:free (dont-rw outside-in-flg iff-flg)
                     (rp-rw-rule term dont-rw rules-for-term context
                                 iff-flg outside-in-flg limit
                                 rp-state state))

              (RP-RW-IF TERM DONT-RW CONTEXT
                             IFF-FLG NIL LIMIT RP-STATE STATE)
              (rp-rw-if term dont-rw
                         context nil nil limit rp-state state)
              (rp-rw-if term dont-rw context iff-flg hyp-flg limit rp-state state)
              (rp-rw term dont-rw context
                     iff-flg hyp-flg limit rp-state state)
              (rp-rw term dont-rw context
                     nil hyp-flg limit rp-state state)
              (rp-rw (cadr subterms)
                     (cadr dont-rw)
                     context
                     nil hyp-flg (+ -2 limit) rp-state state)
              (rp-rw term t context
                     iff-flg hyp-flg limit rp-state state)
              (rp-rw-if term dont-rw context
                        nil hyp-flg limit rp-state state)
              (rp-rw-subterms subterms dont-rw context
                              hyp-flg limit  rp-state state)
              (rp-rw-subterms (cdr subterms)
                              (cdr dont-rw)
                              context hyp-flg (+ -1 limit)
                              rp-state state)
              (rp-rw-subterms (cddr subterms)
                              (cddr dont-rw)
                              context hyp-flg (+ -2 limit)
                              rp-state state)
              (rp-rw-subterms nil dont-rw context hyp-flg
                              limit  rp-state state))))))
