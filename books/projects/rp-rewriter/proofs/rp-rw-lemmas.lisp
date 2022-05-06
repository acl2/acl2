; RP-REWRITER

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
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

   ACL2::ALWAYS$-APPEND
   rev
   ALWAYS$
   ACL2::ALWAYS$-P-LST-IMPLIES-P-ELEMENT
   ;; ACL2::PLAIN-UQI-ACL2-NUMBER-LISTP
   ;; ACL2::PLAIN-UQI-INTEGER-LISTP
   ;; ACL2::O-P-O-INFP-CAR
   IS-IF-RP-TERMP
   rp-rw-context-main
   min
   (:rewrite atom-rp-termp-is-symbolp)
   hons-get
   rp-stat-add-to-rules-used
   rp-ex-counterpart
   (:definition len)
   (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
   (:DEFINITION ACL2::APPLY$-BADGEP)
   (:definition rp-exc-all)
   rp-check-context
   (:definition rp-ev-fncall)
   (:definition rp-apply-bindings)
   valid-rulep
   (:META ACL2::APPLY$-PRIM-META-FN-CORRECT)
   valid-rulesp
   valid-rules-alistp
   rp-rw-rule-aux
   is-rp
   rp-rw-and
   update-nth
   member-equal
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
   (:definition quote-listp)

   rw-only-with-context-subterms
   rw-only-with-context-lst$iff-flg=t
   rp-rw-context
   rp-rw-context-loop
   rp-rw-context-main
   RP-RW-IF-BRANCH
   rp-rw-if
   rp-rw
   rp-rw-subterms
   rp-rw-rule)))

(set-state-ok t)

(with-output

  :off (warning event  prove  observation)
  :on error
  :gag-mode :goals
  (make-flag rp-rw :defthm-macro-name defthm-rp-rw
             :hints
             (("Goal"
               :do-not-induct t
               :expand ((:free (x y)
                               (len (cons x y))))
               :in-theory
               (e/d ()
                    (QUOTEP
                     ;; (:FORWARD-CHAINING
                     ;;  ACL2::|a <= b & ~(a = b)  =>  a < b|)
                     ;; (:FORWARD-CHAINING
                     ;;  ACL2::|a <= b & b <= c  =>  a <= c|)
                     (:DEFINITION UPDATE-RW-LIMIT-THROWS-ERROR)
                     (:TYPE-PRESCRIPTION DONT-RW-IF-FIX)
                     ;; (:FORWARD-CHAINING
                     ;;  ACL2::|a <= b & b < c  =>  a < c|)
                     ;; (:FORWARD-CHAINING
                     ;;  ACL2::|a < b & b <= c  =>  a < c|)
                       
                       
                     DUMB-NEGATE-LIT2$INLINE
                     NONNIL-P
                     RP-EQUAL-CNT
                     RP-EXTRACT-CONTEXT
                     quotep
                     min
                     RP-CHECK-CONTEXT
                     len
                     (:REWRITE ACL2::APPEND-WHEN-NOT-CONSP)
                     (:DEFINITION BINARY-APPEND)
                     (:TYPE-PRESCRIPTION RETURN-LAST)
                     (:TYPE-PRESCRIPTION O-P)
                     (:REWRITE DEFAULT-<-1)
                     (:REWRITE DEFAULT-<-2)

                     DUMB-NEGATE-LIT2$INLINE
                     NONNIL-P
                     RP-EQUAL-CNT
                     RP-EXTRACT-CONTEXT
                     quotep
                     min
                     RP-CHECK-CONTEXT
                     len
                     (:REWRITE ACL2::APPEND-WHEN-NOT-CONSP)
                     (:DEFINITION BINARY-APPEND)
                     (:TYPE-PRESCRIPTION RETURN-LAST)
                     (:TYPE-PRESCRIPTION O-P)
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
                     min
                     RP-EX-COUNTERPART
                     rp-rw-rule-aux
                     UPDATE-NTH

                     ))))))


(with-output
  :off (warning event  prove  observation)
  :on error
  :gag-mode :goals
  (make-flag rw-only-with-context
             :defthm-macro-name defthm-rw-only-with-context
             :hints (("Goal"
                      :expand ((ACL2-COUNT LST))
                      :do-not-induct t
                      :in-theory (e/d (len
                                       acl2-count) ())))))

(local
 (in-theory (disable context-syntaxp)))

(defthm create-if-instance-correct
  (implies (or (not negated-test)
               (iff (rp-evlt negated-test a)
                    (not (rp-evlt cond a))))
           (equal (rp-evlt (create-if-instance cond r1 r2 :negated-test negated-test) a)
                  (rp-evlt `(if ,cond ,r1 ,r2) a)))
  :hints (("Goal"
           :in-theory (e/d (create-if-instance) ()))))

(defthm create-if-instance-valid-sc
  (implies (and (valid-sc `(if ,cond ,r1 ,r2) a)
                (or (not negated-test)
                    (iff (rp-evlt negated-test a)
                         (not (rp-evlt cond a)))))
           (valid-sc (create-if-instance cond r1 r2 :negated-test negated-test) a))
  :hints (("Goal"
           :in-theory (e/d (create-if-instance
                            valid-sc
                            is-if
                            is-rp)
                           ()))))

(defthm create-if-instance-rp-termp
  (implies (and (rp-termp cond)
                (rp-termp r1)
                (rp-termp r2))
           (rp-termp (create-if-instance cond r1 r2 :negated-test negated-test)))
  :hints (("Goal"
           :in-theory (e/d (create-if-instance
                            valid-sc
                            is-if
                            is-rp)
                           ()))))


(local
 (defthmd context-syntaxp-def
   (equal (context-syntaxp context)
          (AND (RP-TERM-LISTP CONTEXT)))
   :hints (("Goal"
            :in-theory (e/d (context-syntaxp) ())))))

(defret rp-evlt-of-dumb-negate-lit2
  (implies (rp-termp term)
           (iff (rp-evlt new-term a)
                (not (rp-evlt term a))))
  :fn dumb-negate-lit2
  :hints (("Goal"
           :in-theory (e/d (dumb-negate-lit2
                            not
                            rp-trans-lst
                            rp-trans
                            is-falist)
                           ()))))

(defret rp-evl-of-dumb-negate-lit2
  (implies (rp-termp term)
           (iff (rp-evl new-term a)
                (not (rp-evl term a))))
  :fn dumb-negate-lit2
  :hints (("Goal"
           :in-theory (e/d (dumb-negate-lit2
                            not
                            rp-trans-lst
                            rp-trans
                            is-falist)
                           ()))))

(defret valid-sc-dumb-negate-lit2
  (implies (valid-sc term a)
           (valid-sc new-term a))
  :fn dumb-negate-lit2
  :hints (("Goal"
           :expand ((VALID-SC (LIST 'NOT TERM) A))
           :in-theory (e/d (valid-sc
                            is-rp

                            is-if
                            dumb-negate-lit2)
                           ()))))

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
           (RP-TERMP (mv-nth 0 (rp-check-context term dont-rw context
                                                 :rw-context-flg rw-context-flg))))
  :hints (("Goal" :in-theory (e/d
                              (context-syntaxp
                               rp-termp
                               rp-term-listp
                               rp-check-context)
                              ((:REWRITE RP-EQUAL-IS-SYMMETRIC)
                               (:DEFINITION TRUE-LISTP)
                               NONNIL-P
                               FALIST-CONSISTENT)))))

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
                                  (
;;                                   (:REWRITE ACL2::PLAIN-UQI-TRUE-LIST-LISTP)
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
  (implies (and (eval-and-all (rp-apply-bindings-subterms (rp-hyp rule) bindings) a)
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
  (implies (and (eval-and-all (rp-apply-bindings-subterms (rp-hyp rule) bindings) a)
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
;;                            (:REWRITE ACL2::O-P-O-INFP-CAR)
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

#|(with-output
  :off (warning event  prove  observation)
  :gag-mode :goals
  :on error
  (defthm dont-rw-syntaxp-rp-rw-rule
    (implies (equal flag 'rp-rw-rule)
             (dont-rw-syntaxp
              (mv-nth 2 (rp-rw-rule term dont-rw rules-for-term context iff-flg
                                    outside-in-flg limit rp-state state))))
    :hints (("goal"
             :induct (flag-rp-rw FLAG RULES-FOR-TERM OUTSIDE-IN-FLG TERM-LST
                                 RULE STACK-INDEX VAR-BINDINGS TERM1
                                 TERM2 ENABLED QUICK-ENABLED OLD-CONTEXT NEW-CONTEXT
                                 I TERM IFF-FLG SUBTERMS DONT-RW
                                 CONTEXT HYP-FLG LIMIT RP-STATE STATE)
             :in-theory (e/d (rp-rw-rule
                              (:induction rp-rw-rule))
                             (remove-rp-from-bindings
                              rp-rw-relieve-synp
                              rp-rw-rule-aux
                              rp-apply-bindings))))))|#

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

(defthm is-falist-of-rp
  (not (is-falist (cons 'rp x)))
  :hints (("Goal"
           :in-theory (e/d (is-falist) ()))))

(DEFTHMd
  RP-EVLT-OF-RP-EQUAL-2
  (IMPLIES (AND (RP-EQUAL TERM1 TERM2))
           (EQUAL (RP-EVLT TERM1 A)
                  (RP-EVLT TERM2 A)))
  :HINTS
  (("Goal" :IN-THEORY
    (E/D ( )
         ()))))

(defun rp-check-context-induct (term context)
  (if (atom context)
      t
    (b* ((c (car context)))
      (cond
       ((case-match c ((& m) (rp-equal m term)) (& nil))
        (b* ((new-term `(rp ',(car c) ,term))
             (new-term (if (is-rp new-term) new-term term)))
          (rp-check-context-induct new-term  (cdr context))))
       (t
        (rp-check-context-induct term (cdr context)))))))

#|(defthm rp-check-context-is-correct-iff-lemma-4
  (implies (and (rp-equal term1 term2)
                (syntaxp (< (cons-count term2)
                            (cons-count term1))))
           (equal (rp-evlt (rp-check-context term1 context iff-flg) a)
                  (rp-evlt (rp-check-context term2 context iff-flg) a)))
  :hints (("Goal"
           ;;:induct (rp-check-context-induct term1 context)
           ;;:do-not-induct t
           :expand ((RP-CHECK-CONTEXT TERM1 CONTEXT IFF-FLG)
                    (RP-CHECK-CONTEXT TERM2 CONTEXT IFF-FLG))
           :in-theory (e/d (is-rp) ()))))|#

(local
 (defthm rp-evlt-of-iff
   (implies (case-match term (('iff & &) t))
            (equal (rp-evlt term a)
                   (iff (rp-evlt (cadr term) a)
                        (rp-evlt (caddr term) a))))))


(defthm rp-check-context-is-correct-iff
  (implies
   (and  (context-syntaxp context)
         iff-flg
         (eval-and-all context a))
   (iff (rp-evlt (mv-nth 0 (rp-check-context term dont-rw context
                                             :RW-CONTEXT-FLG RW-CONTEXT-FLG)) a)
        (rp-evlt term a)))
  :hints (("Subgoal *1/3"
           :use ((:instance rp-evlt-of-rp-equal
                            (term1 (car context))
                            (term2 term))))
          #|("Subgoal *1/2"
          :use ((:instance rp-check-context-is-correct-iff-lemma-4 ; ;
          (term2 term) ;
          (context (cdr context)) ;
          (term1 (LIST* 'RP ;
          (LIST 'QUOTE (CAR (CAR CONTEXT))) ;
          '(TERM)))) ;
          ))|#
          ("Subgoal *1/5"
           :use ((:instance rp-evlt-of-rp-equal   ;
                            (term2 (CAR CONTEXT)) ;
                            (term1 term))
                 (:instance rp-evlt-of-rp-equal          ;
                            (term2 (CADR (CAR CONTEXT))) ;
                            (term1 term))))
          ("goal"
           :do-not-induct t
           :induct (rp-check-context term dont-rw context
                                     :RW-CONTEXT-FLG RW-CONTEXT-FLG)
           :expand ((EVAL-AND-ALL CONTEXT A)
                    (rp-check-context term dont-rw context
                                      :RW-CONTEXT-FLG RW-CONTEXT-FLG) ;
                    (:free (x y) (IS-RP (LIST 'RP (cons 'QUOTE x) y))))
           :in-theory (e/d (rp-check-context
                            ;;RP-EVLT-OF-RP-EQUAL-2
                            context-syntaxp
                            rp-check-context-is-correct-iff-lemma
                            rp-check-context-is-correct-iff-lemma-2
                            rp-check-context-is-correct-iff-lemma-3
                            rp-termp
                            eval-and-all
                            is-falist
                            ;;RP-EVL-OF-FNCALL-ARGS
                            )
                           (rp-evlt-of-rp-equal
                            INCLUDE-FNC
                            NONNIL-P
                            ;;RP-TERM-LISTP
                            RP-TERMP
                            rp-term-listp-is-true-listp
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
    (eval-and-all context a)
    (not iff-flg))
   (equal (rp-evlt (mv-nth 0 (rp-check-context term dont-rw context :RW-CONTEXT-FLG RW-CONTEXT-FLG)) a)
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
              :do-not-induct t
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

   UPDATE-RW-LIMIT-THROWS-ERROR
   rw-limit-throws-error
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

(local
 (defthm UPDATE-RW-LIMIT-THROWS-ERROR-rp-statep
   (implies (and (rp-statep rp-state)
                 (booleanp x))
            (rp-statep (update-rw-limit-throws-error x rp-state)))
   :hints (("Goal"
            :in-theory (e/d (rp-statep
                             UPDATE-RW-LIMIT-THROWS-ERROR) ())))))

(local
 (defthm booleanp-rw-limit-throws-error
   (implies (rp-statep rp-state)
            (booleanp (rw-limit-throws-error rp-state)))
   :hints (("Goal"
            :in-theory (e/d (rp-statep
                             rw-limit-throws-error) ())))))




(defthm-rw-only-with-context
  (defthm rp-statep-of-rw-only-with-context
    (and (implies (rp-statep rp-state)
                  (rp-statep (mv-nth 1 (rw-only-with-context term dont-rw context iff-flg limit rp-state
                                                             state))))
         (implies (valid-rp-statep rp-state)
                  (valid-rp-statep (mv-nth 1 (rw-only-with-context term dont-rw context iff-flg limit rp-state
                                                                   state))))
         (implies (valid-rp-state-syntaxp rp-state)
                  (valid-rp-state-syntaxp (mv-nth 1 (rw-only-with-context term dont-rw context iff-flg limit rp-state
                                                                          state)))))
    :flag rw-only-with-context)
  (defthm rp-statep-of-rw-only-with-context-if
    (and (implies (rp-statep rp-state)
                  (rp-statep (mv-nth 1 (rw-only-with-context-if term dont-rw context iff-flg limit rp-state
                                                                state))))
         (implies (valid-rp-statep rp-state)
                  (valid-rp-statep (mv-nth 1 (rw-only-with-context-if term dont-rw context iff-flg limit rp-state
                                                                      state))))
         (implies (valid-rp-state-syntaxp rp-state)
                  (valid-rp-state-syntaxp (mv-nth 1 (rw-only-with-context-if term dont-rw context iff-flg limit rp-state
                                                                             state)))))
    :flag rw-only-with-context-if)
  (defthm rp-statep-of-rw-only-with-context-subterms
    (and (implies (rp-statep rp-state)
                  (rp-statep (mv-nth 1 (rw-only-with-context-subterms lst dont-rw
                                                                      context limit rp-state state))))
         (implies (valid-rp-statep rp-state)
                  (valid-rp-statep (mv-nth 1 (rw-only-with-context-subterms lst
                                                                            dont-rw context limit rp-state state))))
         (implies (valid-rp-state-syntaxp rp-state)
                  (valid-rp-state-syntaxp (mv-nth 1 (rw-only-with-context-subterms lst dont-rw context limit rp-state state)))))
    :flag rw-only-with-context-subterms)
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (rw-only-with-context
                            rw-only-with-context-if
                            rw-only-with-context-subterms)
                           (VALID-RP-STATEP)))))

(defthm rp-statep-of-rw-only-with-context-lst$iff-flg=t
  (and (implies (rp-statep rp-state)
                (rp-statep (mv-nth 1 (rw-only-with-context-lst$iff-flg=t lst dont-rw
                                                                         context limit rp-state state))))
       (implies (valid-rp-statep rp-state)
                (valid-rp-statep (mv-nth 1 (rw-only-with-context-lst$iff-flg=t lst dont-rw
                                                                               context limit rp-state state))))
       (implies (valid-rp-state-syntaxp rp-state)
                (valid-rp-state-syntaxp (mv-nth 1 (rw-only-with-context-lst$iff-flg=t lst dont-rw
                                                                                      context limit rp-state state)))))
  :hints (("Goal"
           :do-not-induct t
           :induct (rw-only-with-context-lst$iff-flg=t lst dont-rw
                                                       context limit rp-state state)
           :in-theory (e/d (rw-only-with-context-lst$iff-flg=t)
                           (VALID-RP-STATEP)))))

(defthm booleanp-of-rw-context-disabled
  (implies (rp-statep rp-state)
           (and (booleanp (rw-context-disabled rp-state))
                (BOOLEANP (NTH *RW-CONTEXT-DISABLED* RP-STATE))))
  :hints (("Goal"
           :in-theory (e/d (rp-statep
                            rw-context-disabled) ()))))

(encapsulate
  nil

  (local
   (in-theory (disable ACL2::CDR-OF-APPEND-WHEN-CONSP
                       RP-EQUAL
                       VALID-RULES-ALISTP-IMPLIES-RULES-ALISTP
                       RP-TERM-LISTP-APPEND
                       RP-EXTRACT-CONTEXT
                       ;;RP-STATE-PRESERVEDP-IMPLIES-RP-STATEP
                       RP-RW-RULE-AUX
                       UPDATE-RW-LIMIT-THROWS-ERROR
                       IS-RP-PSEUDO-TERMP
                       IS-IF-RP-TERMP
                       IS-IF-RP-TERMP)))

  (with-output
    :off (warning event  prove  observation)
    :gag-mode :goals
    :on error

    (defthm-rp-rw
      (defthm rp-rw-rp-statep
        (implies (rp-statep rp-state)
                 (rp-statep
                  (mv-nth 1 (rp-rw term dont-rw context iff-flg limit rp-state state))))
        :flag rp-rw)
      (defthm rp-rw-rule-rp-statep
        (implies (rp-statep rp-state)
                 (rp-statep
                  (mv-nth 3 (rp-rw-rule term dont-rw rules-for-term context iff-flg outside-in-flg limit rp-state state))))
        :flag rp-rw-rule)

      (defthm rp-rw-relieve-hyp-rp-statep
        (implies (rp-statep rp-state)
                 (rp-statep
                  (mv-nth 1 (rp-rw-relieve-hyp term-lst dont-rw context rule stack-index var-bindings limit rp-state state))))
        :flag rp-rw-relieve-hyp)

      (defthm rp-rw-context-rp-statep
        (implies (rp-statep rp-state)
                 (rp-statep
                  (mv-nth 2 (rp-rw-context old-context new-context limit
                                           rp-state state))))
        :flag rp-rw-context)

      (defthm rp-rw-context-loop-rp-statep
        (implies (rp-statep rp-state)
                 (rp-statep
                  (mv-nth 1 (rp-rw-context-loop context limit loop-limit
                                                rp-state state))))
        :flag rp-rw-context-loop)

      (defthm rp-rw-if-rp-statep
        (implies (rp-statep rp-state)
                 (rp-statep
                  (mv-nth 1 (rp-rw-if term dont-rw context iff-flg  limit
                                      rp-state state))))
        :flag rp-rw-if)

      (defthm rp-rw-branch-rp-statep
        (implies (rp-statep rp-state)
                 (rp-statep
                  (mv-nth 2 (rp-rw-if-branch cond-rw then then-dont-rw
                                             context
                                             iff-flg  limit rp-state state))))
        :flag rp-rw-if-branch)

      (defthm rp-rw-and-rp-statep
        (implies (rp-statep rp-state)
                 (rp-statep
                  (mv-nth 1 (rp-rw-and term1 term2 context  limit rp-state state))))
        :flag rp-rw-and)

      (defthm rp-rw-context-main-rp-statep
        (implies (rp-statep rp-state)
                 (rp-statep
                  (mv-nth 1 (rp-rw-context-main term context enabled QUICK-ENABLED limit rp-state state))))
        :flag rp-rw-context-main)

      (defthm rp-rw-subterms-rp-statep
        (implies (rp-statep rp-state)
                 (rp-statep
                  (mv-nth 1 (rp-rw-subterms subterms dont-rw context  limit
                                            rp-state state))))
        :flag rp-rw-subterms)

      :hints (("goal"
               :expand ((RP-RW-CONTEXT-LOOP CONTEXT
                                            LIMIT LOOP-LIMIT RP-STATE STATE)
                        (RP-RW-IF-BRANCH COND-RW THEN THEN-DONT-RW CONTEXT
                                         IFF-FLG  LIMIT RP-STATE STATE)
                        (RP-RW-CONTEXT-MAIN TERM CONTEXT
                                            ENABLED NIL LIMIT RP-STATE STATE)
                        (RP-RW-CONTEXT-MAIN TERM
                                            CONTEXT NIL QUICK-ENABLED LIMIT RP-STATE STATE)
                        (rp-rw-relieve-hyp term-lst dont-rw context rule
                                           stack-index var-bindings limit rp-state state)
                        (rp-rw-context-main term context enabled QUICK-ENABLED limit rp-state state)
                        (rp-rw-and term1 term2 context  limit rp-state
                                   state)
                        (rp-rw-if term dont-rw context
                                  nil  limit rp-state state)
                        (rp-rw-if term dont-rw
                                  context nil  limit rp-state state)
                        (rp-rw-rule term dont-rw rules-for-term
                                    context iff-flg outside-in-flg limit
                                    rp-state state)
                        (RP-RW-IF TERM DONT-RW CONTEXT
                                  IFF-FLG  LIMIT RP-STATE STATE)
                        (RP-RW-IF TERM DONT-RW
                                  CONTEXT IFF-FLG  LIMIT RP-STATE STATE)
                        (rp-rw term dont-rw context iff-flg  limit rp-state
                               state)
                        (RP-RW TERM DONT-RW
                               CONTEXT NIL  LIMIT RP-STATE STATE)
                        (rp-rw-subterms subterms dont-rw context  limit
                                        rp-state state)
                        (rp-rw-context old-context
                                       new-context limit rp-state state))
               :in-theory (e/d (RP-STAT-ADD-TO-RULES-USED)
                               (;;update-rules-used
                                rp-rw-if-branch
                                SHOW-USED-RULES-FLG
                                UPDATE-NTH
                                is-rp
                                RW-LIMIT-THROWS-ERROR
                                RW-CONTEXT-DISABLED
                                RP-STAT-ADD-TO-RULES-USED)))))))

(defthm update-rw-limit-throws-error-valid-rp-state-syntaxp
  (implies (and (valid-rp-state-syntaxp rp-state)
                (booleanp x))
           (valid-rp-state-syntaxp (update-rw-limit-throws-error x rp-state)))
  :hints (("goal"
           :do-not-induct t
           :expand ((valid-rp-state-syntaxp rp-state))
           :in-theory (e/d (rp-statep

                            update-rw-limit-throws-error)
                           (valid-rp-state-syntaxp-aux)))))

(defthm update-rw-limit-throws-error-valid-rp-statep
  (implies (valid-rp-statep rp-state)
           (valid-rp-statep (update-rw-limit-throws-error x rp-state)))
  :hints (("goal"
           :do-not-induct t
           :expand ((valid-rp-statep rp-state))
           :in-theory (e/d (rp-statep
                            update-rw-limit-throws-error)
                           (valid-rp-state-syntaxp-aux)))))

#|(defthmd valid-sc-of-and-pattern
  (implies (valid-sc `(if ,x ,y 'nil) a)
           (valid-sc `(if ,y ,x 'nil) a))
  :hints (("Goal"
           :in-theory (e/d (valid-sc
                            is-rp
                            is-if) ()))))|#

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
    :gag-mode :goals
    :on error

    (defthm-rp-rw
      (defthm rp-rw-returns-valid-valid-rp-state-syntaxp
        (implies (valid-rp-state-syntaxp rp-state)
                 (valid-rp-state-syntaxp
                  (mv-nth 1 (rp-rw term dont-rw context iff-flg  limit rp-state state))))
        :flag rp-rw)
      (defthm rp-rw-rule-retuns-valid-valid-rp-state-syntaxp
        (implies (valid-rp-state-syntaxp rp-state)
                 (valid-rp-state-syntaxp
                  (mv-nth 3 (rp-rw-rule term dont-rw rules-for-term context iff-flg outside-in-flg limit rp-state state))))
        :flag rp-rw-rule)

      (defthm rp-rw-relieve-hyp-retuns-valid-valid-rp-state-syntaxp
        (implies (valid-rp-state-syntaxp rp-state)
                 (valid-rp-state-syntaxp
                  (mv-nth 1 (rp-rw-relieve-hyp term-lst dont-rw context rule stack-index var-bindings limit rp-state state))))
        :flag rp-rw-relieve-hyp)

      (defthm rp-rw-context-main-retuns-valid-valid-rp-state-syntaxp
        (implies (valid-rp-state-syntaxp rp-state)
                 (valid-rp-state-syntaxp
                  (mv-nth 1 (rp-rw-context-main term context enabled QUICK-ENABLED limit rp-state state))))
        :flag rp-rw-context-main)

      (defthm rp-rw-context-retuns-valid-valid-rp-state-syntaxp
        (implies (valid-rp-state-syntaxp rp-state)
                 (valid-rp-state-syntaxp
                  (mv-nth 2 (rp-rw-context old-context new-context limit
                                           rp-state state))))
        :flag rp-rw-context)

      (defthm rp-rw-context-loop-retuns-valid-valid-rp-state-syntaxp
        (implies (valid-rp-state-syntaxp rp-state)
                 (valid-rp-state-syntaxp
                  (mv-nth 1 (rp-rw-context-loop context limit loop-limit
                                                rp-state state))))
        :flag rp-rw-context-loop)

      (defthm rp-rw-if-retuns-valid-valid-rp-state-syntaxp
        (implies (valid-rp-state-syntaxp rp-state)
                 (valid-rp-state-syntaxp
                  (mv-nth 1 (rp-rw-if term dont-rw context iff-flg  limit
                                      rp-state state))))
        :flag rp-rw-if)

      (defthm rp-rw-if-branch-retuns-valid-valid-rp-state-syntaxp
        (implies (valid-rp-state-syntaxp rp-state)
                 (valid-rp-state-syntaxp
                  (mv-nth 2 (rp-rw-if-branch cond-rw then then-dont-rw
                                             context
                                             iff-flg  limit rp-state state))))
        :flag rp-rw-if-branch)

      (defthm rp-rw-and-retuns-valid-valid-rp-state-syntaxp
        (implies (valid-rp-state-syntaxp rp-state)
                 (valid-rp-state-syntaxp
                  (mv-nth 1 (rp-rw-and term1 term2 context  limit rp-state state))))
        :flag rp-rw-and)


      (defthm rp-rw-subterms-retuns-valid-valid-rp-state-syntaxp
        (implies (valid-rp-state-syntaxp rp-state)
                 (valid-rp-state-syntaxp
                  (mv-nth 1 (rp-rw-subterms subterms dont-rw context  limit
                                            rp-state state))))
        :flag rp-rw-subterms)

      :hints (("goal"
               :expand ((rp-rw-if-branch cond-rw then then-dont-rw
                                         context
                                         iff-flg  limit rp-state state)
                        (RP-RW-CONTEXT-LOOP CONTEXT
                                            LIMIT LOOP-LIMIT RP-STATE STATE)
                        (RP-RW-CONTEXT-MAIN TERM
                                            CONTEXT NIL QUICK-ENABLED LIMIT
                                            RP-STATE STATE)
                        (RP-RW-CONTEXT-MAIN TERM CONTEXT ENABLED
                                            QUICK-ENABLED LIMIT RP-STATE STATE)
                        (RP-RW-CONTEXT-MAIN TERM
                                            CONTEXT enabled nil LIMIT RP-STATE STATE)
                        (rp-rw-relieve-hyp term-lst dont-rw context rule
                                           stack-index var-bindings limit rp-state state)
                        (rp-rw-context-main term context  enabled QUICK-ENABLED limit rp-state state)
                        (rp-rw-and term1 term2 context  limit rp-state
                                   state)
                        (rp-rw-context old-context new-context limit
                                       rp-state state)
                        (RP-RW-IF TERM DONT-RW CONTEXT
                                  NIL  LIMIT RP-STATE STATE)
                        (rp-rw-if term dont-rw
                                  context nil  limit rp-state state)
                        (rp-rw-rule term dont-rw rules-for-term
                                    context iff-flg outside-in-flg limit
                                    rp-state state)
                        (RP-RW-IF TERM DONT-RW CONTEXT
                                  IFF-FLG  LIMIT RP-STATE STATE)
                        (RP-RW-IF TERM DONT-RW
                                  CONTEXT IFF-FLG  LIMIT RP-STATE STATE)
                        (rp-rw term dont-rw context iff-flg  limit rp-state
                               state)
                        (RP-RW TERM DONT-RW
                               CONTEXT NIL  LIMIT RP-STATE STATE)
                        (rp-rw-subterms subterms dont-rw context  limit
                                        rp-state state))
               :in-theory (e/d (RP-STAT-ADD-TO-RULES-USED)
                               (;;update-rules-used
                                SHOW-USED-RULES-FLG
                                UPDATE-NTH
                                rp-rw-context-loop
                                (:TYPE-PRESCRIPTION NOT*)
                                (:TYPE-PRESCRIPTION ACL2::BINARY-AND*)
                                (:TYPE-PRESCRIPTION ACL2::BINARY-OR*)
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
    :gag-mode :goals
    :on error

    (defthm-rp-rw
      (defthm valid-rp-statep-of-rp-rw
        (implies (and (valid-rp-statep rp-state)
                      (rp-statep rp-state))
                 (valid-rp-statep
                  (mv-nth 1 (rp-rw term dont-rw context iff-flg  limit rp-state state))))
        :flag rp-rw)
      (defthm valid-rp-statep-of-rp-rw-rule
        (implies (and (valid-rp-statep rp-state)
                      (rp-statep rp-state))
                 (valid-rp-statep
                  (mv-nth 3 (rp-rw-rule term dont-rw rules-for-term context iff-flg outside-in-flg limit rp-state state))))
        :flag rp-rw-rule)

      (defthm valid-rp-statep-of-rp-rw-context
        (implies (and (valid-rp-statep rp-state)
                      (rp-statep rp-state))
                 (valid-rp-statep
                  (mv-nth 2 (rp-rw-context old-context new-context limit
                                           rp-state state))))
        :flag rp-rw-context)

      (defthm valid-rp-statep-of-rp-rw-context-loop
        (implies (and (valid-rp-statep rp-state)
                      (rp-statep rp-state))
                 (valid-rp-statep
                  (mv-nth 1 (rp-rw-context-loop context limit loop-limit
                                                rp-state state))))
        :flag rp-rw-context-loop)

      (defthm valid-rp-statep-of-rp-rw-relieve-hyp
        (implies (and (valid-rp-statep rp-state)
                      (rp-statep rp-state))
                 (valid-rp-statep
                  (mv-nth 1 (rp-rw-relieve-hyp term-lst dont-rw context rule stack-index var-bindings limit rp-state state))))
        :flag rp-rw-relieve-hyp)

      (defthm valid-rp-statep-of-rp-rw-context-main
        (implies (and (valid-rp-statep rp-state)
                      (rp-statep rp-state))
                 (valid-rp-statep
                  (mv-nth 1 (rp-rw-context-main term context enabled
                                                quick-enabled limit rp-state state))))
        :flag rp-rw-context-main)

      (defthm valid-rp-statep-of-rp-rw-if-retuns
        (implies (and (valid-rp-statep rp-state)
                      (rp-statep rp-state))
                 (valid-rp-statep
                  (mv-nth 1 (rp-rw-if term dont-rw context iff-flg   limit
                                      rp-state state))))
        :flag rp-rw-if)

      (defthm valid-rp-statep-of-rp-rw-if-branch-retuns
        (implies (and (valid-rp-statep rp-state)
                      (rp-statep rp-state))
                 (valid-rp-statep
                  (mv-nth 2 (rp-rw-if-branch cond-rw then then-dont-rw
                                             context
                                             iff-flg  limit rp-state state))))
        :flag rp-rw-if-branch)

      (defthm valid-rp-statep-of-rp-rw-and-retuns
        (implies (and (valid-rp-statep rp-state)
                      (rp-statep rp-state))
                 (valid-rp-statep
                  (mv-nth 1 (rp-rw-and term1 term2 context  limit rp-state state))))
        :flag rp-rw-and)

      (defthm valid-rp-statep-of-rp-rw-subterms
        (implies (and (valid-rp-statep rp-state)
                      (rp-statep rp-state))
                 (valid-rp-statep
                  (mv-nth 1 (rp-rw-subterms subterms dont-rw context  limit
                                            rp-state state))))
        :flag rp-rw-subterms)

      :hints (("goal"
               :expand ((RP-RW-CONTEXT-LOOP CONTEXT
                                            LIMIT LOOP-LIMIT RP-STATE STATE)
                        (rp-rw-if-branch cond-rw then then-dont-rw
                                 context
                                 iff-flg  limit rp-state state)
                        (RP-RW-CONTEXT-MAIN TERM
                                            CONTEXT NIL QUICK-ENABLED LIMIT
                                            RP-STATE STATE)
                        (RP-RW-CONTEXT-MAIN TERM
                                            CONTEXT enabled nil LIMIT RP-STATE STATE)
                        (rp-rw-relieve-hyp term-lst dont-rw context rule
                                           stack-index var-bindings limit rp-state state)
                        (rp-rw-context-main term context enabled QUICK-ENABLED limit rp-state state)
                        (rp-rw-and term1 term2 context  limit rp-state
                                   state)
                        (rp-rw-context old-context new-context limit
                                       rp-state state)
                        (rp-rw-if term dont-rw context
                                  nil  limit rp-state state)
                        (rp-rw-if term dont-rw
                                  context nil  limit rp-state state)
                        (rp-rw-rule term dont-rw rules-for-term
                                    context iff-flg outside-in-flg limit
                                    rp-state state)
                        (rp-rw-if term dont-rw context
                                  iff-flg  limit rp-state state)
                        (rp-rw-if term dont-rw
                                  context iff-flg  limit rp-state state)
                        (rp-rw term dont-rw context iff-flg  limit rp-state
                               state)
                        (rp-rw term dont-rw
                               context nil  limit rp-state state)
                        (rp-rw-subterms subterms dont-rw context  limit
                                        rp-state state))
               :in-theory (e/d (rp-stat-add-to-rules-used)
                               (;;update-rules-used
                                show-used-rules-flg
                                update-nth
                                valid-rp-statep
                                rp-stat-add-to-rules-used)))))))

(defthm
  rule-syntaxp-implies-3
  (implies (and (rule-syntaxp rule :warning nil)
                (not (rp-rule-metap rule)))
           (and (weak-custom-rewrite-rule-p rule)
                (rp-term-listp (rp-hyp rule))
                (rp-termp (rp-lhs rule))
                (rp-termp (rp-rhs rule))
                (not (include-fnc (rp-lhs rule) 'rp))
                (not (include-fnc-subterms (rp-hyp rule) 'rp))
                (not (include-fnc (rp-rhs rule) 'falist))
                (not (include-fnc-subterms (rp-hyp rule) 'falist))
                ;;(not (include-fnc (rp-lhs rule) 'if))
                (not (include-fnc (rp-lhs rule) 'synp))
                #|(no-free-variablep rule)|#
                (not (include-fnc (rp-lhs rule) 'list))
                (not (include-fnc-subterms (rp-hyp rule) 'list))
                (not (include-fnc (rp-rhs rule) 'list))))
  :rule-classes (:rewrite :forward-chaining)
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

(defthm rp-term-listp-update-nth
  (implies (and (rp-term-listp lst)
                (rp-termp val)
                (< i (len lst)))
           (RP-TERM-LISTP (UPDATE-NTH I val lst)))
  :hints (("Goal"
           :do-not-induct t
           :induct (UPDATE-NTH I val lst)
           :in-theory (e/d (UPDATE-NTH
                            len
                            car-cons
                            RP-TERM-LISTP)
                           ()))))


;;:i-am-here

(local
 (in-theory (disable CONS-COUNT-COMPARE
                     ;;(:TYPE-PRESCRIPTION EX-FROM-SYNP)
                     ;;(:TYPE-PRESCRIPTION LEN)
                     ;;(:TYPE-PRESCRIPTION VALID-RP-STATE-SYNTAXP)
                     ;;(:TYPE-PRESCRIPTION DONT-RW-IF-FIX)
                     ;;(:TYPE-PRESCRIPTION O<)

                     ;;(:TYPE-PRESCRIPTION ACL2::BINARY-AND*)

                     ;;(:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS)

                     (:REWRITE ACL2::LEN-MEMBER-EQUAL-LOOP$-AS)
                     ;;(:REWRITE ACL2::REV-WHEN-NOT-CONSP)

                     cons-count-compare-aux)))

(defthm is-rp-lemma-for-rw-only-with-context-subterms
  (implies (and (rp-termp term)
                (equal (car term) 'rp))
           (is-rp (list* 'rp
                         (mv-nth 0 (rw-only-with-context-subterms (cdr term)
                                                                  dont-rw
                                                                  context limit
                                                                  rp-state state)))))
  :hints (("Goal"
           :do-not-induct t
           :expand ((rp-termp term)
                    (IS-RP TERM)
                    (rw-only-with-context-subterms (cdr term)
                                                   dont-rw
                                                   context limit
                                                   rp-state state))
           :in-theory (e/d (RW-ONLY-WITH-CONTEXT-SUBTERMS
                            ;;RW-ONLY-WITH-CONTEXT
                            is-rp)
                           ()))))

(defthm-rw-only-with-context
  (defthm rp-termp-of-rw-only-with-context
    (implies (and (context-syntaxp context)
                  (rp-termp term))
             (rp-termp (mv-nth 0 (rw-only-with-context term dont-rw context iff-flg limit rp-state
                                                       state))))
    :flag rw-only-with-context)
  (defthm rp-termp-of-rw-only-with-context-if
    (implies (and (context-syntaxp context)
                  (is-if term)
                  (rp-termp term))
             (rp-termp (mv-nth 0 (rw-only-with-context-if term dont-rw context iff-flg limit rp-state
                                                          state))))
    :flag rw-only-with-context-if)
  (defthm rp-term-listp-of-rw-only-with-context-subterms
    (implies (and (context-syntaxp context)
                  (rp-term-listp lst))
             (rp-term-listp (mv-nth 0 (rw-only-with-context-subterms lst dont-rw
                                                                     context limit rp-state state))))
    :flag rw-only-with-context-subterms)
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (rw-only-with-context
                            rw-only-with-context-if
                            CONTEXT-SYNTAXP
                            rw-only-with-context-subterms)
                           (VALID-RP-STATEP)))))

(defthm rp-term-listp-of-rw-only-with-context-lst$iff-flg=t
  (implies (and (context-syntaxp context)
                (rp-term-listp lst))
           (rp-term-listp (mv-nth 0 (rw-only-with-context-lst$iff-flg=t lst dont-rw
                                                                        context limit rp-state state))))
  :hints (("Goal"
           :in-theory (e/d (rw-only-with-context-lst$iff-flg=t) ()))))

#|(defthm not-of-not*-forward
  (implies (not (not* a))
a)

  :rule-classes :forward-chaining)|#

(defthm rp-term-listp-of-clear-context-for-rw-only-with-context
  (implies (rp-term-listp context)
           (rp-term-listp (clear-context-for-rw-only-with-context context))))

(defthm rp-term-listp-RP-REMOVE-EQUAL
  (implies (rp-term-listp lst)
           (rp-term-listp (RP-REMOVE-EQUAL x lst)))
  :hints (("Goal"
           :in-theory (e/d (RP-REMOVE-EQUAL) ()))))

(encapsulate
  nil

  (local
   (in-theory (disable ACL2::CDR-OF-APPEND-WHEN-CONSP
                       RP-EQUAL
                       CONS-COUNT-COMPARE
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
                                                        CONTEXT  LIMIT
                                                        rp-state STATE)))))
    :hints (("Goal"
             :do-not-induct t
             :expand ((RP-RW-SUBTERMS (CDR SUBTERMS)
                                      (DONT-RW-CDR DONT-RW)
                                      CONTEXT  LIMIT RP-STATE STATE)
                      (rp-rw-subterms SUBTERMS DONT-RW CONTEXT  LIMIT
                                      rp-state
                                      STATE)
                      (RP-RW-SUBTERMS (CDR SUBTERMS)
                                      (dont-rw-cdr DONT-RW)
                                      CONTEXT  (+ -1 LIMIT)
                                      RP-STATE STATE)
                      (RP-RW-SUBTERMS (CDR SUBTERMS)
                                      NIL CONTEXT  (+ -1 LIMIT)
                                      RP-STATE STATE)
                      (RP-RW (CAR SUBTERMS)
                             (dont-rw-car DONT-RW)
                             CONTEXT  (+ -1 LIMIT)
                             NIL RP-STATE STATE)
                      (RP-RW (CAR SUBTERMS)
                             NIL CONTEXT  (+ -1 LIMIT)
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
                                    (rp-rw term dont-rw context iff-flg  limit rp-state state))))
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

      (defthm booleanp-rp-rw-relieve-hyp
        (implies t
                 (let ((res (mv-nth 0
                                    (rp-rw-relieve-hyp term-lst dont-rw context rule stack-index var-bindings limit rp-state state))))
                   (booleanp res )))
        :flag rp-rw-relieve-hyp)

      (defthm rp-termp-rp-rw-if
        (implies (and (rp-termp term)

                      (context-syntaxp context)

                      (valid-rp-state-syntaxp rp-state))
                 (let ((res (mv-nth 0
                                    (rp-rw-if term dont-rw context  iff-flg
                                               limit rp-state state))))
                   (and (rp-termp res)

                        )))
        :flag rp-rw-if)

      (defthm rp-termp-rp-rw-if-branch
        (implies (and (rp-termp then)
                      (rp-termp cond-rw)
                      (context-syntaxp context)
                      (valid-rp-state-syntaxp rp-state))
                 (let ((res (mv-nth 0
                                    (rp-rw-if-branch cond-rw then then-dont-rw
                                                     context
                                                     iff-flg  limit rp-state state))))
                   (rp-termp res)))
        :flag rp-rw-if-branch)

      (defthm rp-termp-rp-rw-and
        (implies (and (rp-termp term1)
                      (rp-termp term2)
                      (context-syntaxp context)
                      (valid-rp-state-syntaxp rp-state))
                 (let ((res (mv-nth 0 (rp-rw-and term1 term2 context  limit rp-state state))))
                   (rp-termp res)))
        :flag rp-rw-and)

      (defthm rp-termp-rp-rw-context
        (implies (and (context-syntaxp old-context)
                      (context-syntaxp new-context)
                      (valid-rp-state-syntaxp rp-state))
                 (let ((res (mv-nth 0 (rp-rw-context old-context new-context limit
                                                     rp-state state))))
                   (and (rp-term-listp res))))
        :flag rp-rw-context)

      (defthm rp-termp-rp-rw-context-loop
        (implies (and (context-syntaxp context)
                      (valid-rp-state-syntaxp rp-state))
                 (let ((res (mv-nth 0 (rp-rw-context-loop context limit loop-limit
                                                          rp-state state))))
                   (and (rp-term-listp res))))
        :flag rp-rw-context-loop)

      (defthm rp-termp-rp-rw-context-main
        (implies (and (context-syntaxp context)
                      (rp-termp term)
                      (valid-rp-state-syntaxp rp-state))
                 (let ((res (mv-nth 0 (rp-rw-context-main term context enabled QUICK-ENABLED limit rp-state state))))
                   (and (rp-term-listp res))))
        :flag rp-rw-context-main)

      (defthm rp-termp-rp-rw-subterms
        (implies (and (RP-TERM-LISTP SUBTERMS)
                      (context-syntaxp context)
                      (valid-rp-state-syntaxp rp-state))
                 (let ((res (mv-nth 0 (rp-rw-subterms SUBTERMS DONT-RW CONTEXT  LIMIT
                                                      rp-state STATE))))
                   (and (rp-term-listp res)

                        )))
        :flag rp-rw-subterms)

      :hints (("Goal"
               :in-theory (e/d (RP-TERM-LISTP-APPEND
                                is-if-implies
                                rp-termp-single-step
                                )
                               (rp-termp

                                ;;(:TYPE-PRESCRIPTION NONNIL-P)
                                ;;(:REWRITE ACL2::REV-WHEN-NOT-CONSP)
                                ;;(:FORWARD-CHAINING RP-TERMP-IMPLIES)

                                #|(:REWRITE
                                UPDATE-RW-LIMIT-THROWS-ERROR-VALID-RP-STATE-SYNTAXP)|#
                                #||#
                                ;;ACL2::AND*-REM-SECOND
                                ;;ACL2::AND*-REM-FIRST
                                ;;ACL2::AND*-NIL-SECOND

                                ;;(:TYPE-PRESCRIPTION ACL2::BINARY-AND*)
                                is-rp
                                rp-rule-metap))
               :expand
               ((RP-RW-CONTEXT-LOOP NIL LIMIT LOOP-LIMIT RP-STATE STATE)
                (RP-RW-IF-BRANCH COND-RW THEN THEN-DONT-RW CONTEXT
                                 IFF-FLG  LIMIT RP-STATE STATE)
                (RP-RW-CONTEXT-LOOP CONTEXT
                                    LIMIT LOOP-LIMIT RP-STATE STATE)
                (RP-RW-CONTEXT-MAIN TERM
                                    CONTEXT NIL QUICK-ENABLED LIMIT RP-STATE STATE)
                (rp-rw-relieve-hyp term-lst dont-rw context rule stack-index var-bindings limit rp-state state)
                (rp-rw-context-main term context enabled QUICK-ENABLED limit
                                    rp-state state)
                (rp-rw-context-main term context enabled nil limit rp-state state)
                (rp-rw-and term1 term2 context  limit rp-state state)
                (RP-RW-CONTEXT NIL
                               NEW-CONTEXT  LIMIT RP-STATE STATE)

                (RP-RW-CONTEXT OLD-CONTEXT
                               NEW-CONTEXT  LIMIT RP-STATE STATE)
                (RP-RW-CONTEXT NIL
                               NEW-CONTEXT  LIMIT RP-STATE STATE)
                (RP-RW-IF TERM DONT-RW CONTEXT
                          NIL  LIMIT RP-STATE STATE)
                (RP-RW-IF TERM DONT-RW
                          CONTEXT NIL  LIMIT RP-STATE STATE)
                (RP-RW-IF TERM DONT-RW CONTEXT
                          IFF-FLG  LIMIT RP-STATE STATE)
                
                (rp-rw-subterms nil dont-rw context  limit
                                rp-state state)
                (rp-rw-if term dont-rw context
                          iff-flg  limit rp-state state)
                (rp-rw-subterms subterms dont-rw context  limit
                                rp-state state)
                (rp-rw term dont-rw context
                       nil  limit rp-state state)
                (rp-rw-rule term dont-rw
                            rules-for-term context iff-flg outside-in-flg  limit rp-state state)
                (rp-rw-rule term dont-rw nil context iff-flg  outside-in-flg limit rp-state state)
                (rp-rw term t context iff-flg  limit rp-state state)
                (rp-rw term dont-rw context  iff-flg  limit rp-state state)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|(defthm rp-evl-of-extract-context
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
                           ()))))|#

(defthm rp-evl-of-extract-context
  (implies (rp-termp term)
           (iff (eval-and-all (rp-extract-context term) a)
                (rp-evlt term a)))
  :otf-flg t
  :hints (("Subgoal *1/3"
           :use ((:instance rp-evlt-of-dumb-negate-lit2
                            (term (cadr term)))))
          ("Goal"
           :induct (rp-extract-context term)
           :expand ((RP-TRANS-LST (CDR TERM)))

           :do-not-induct t
           :in-theory (e/d (rp-extract-context
                            eval-and-all
                            RP-TRANS-LST
                            rp-trans

                            ;;rp-trans-lst
                            is-falist)
                           (rp-evlt-of-dumb-negate-lit2
                            ;;RP-EVL-OF-VARIABLE
                            ;;RP-EVL-OF-QUOTE
                            )))))

(local
 (defthm hide-x-is-x
   (equal (hide x) x)
   :hints (("Goal"
            :expand (hide x)))))

#|(defthm rp-evl-of-dumb-negate-lit2
  (implies (rp-termp x)
           (iff (rp-evlt (dumb-negate-lit2 x) a)
                (not (rp-evlt x a))))
  :hints (("Goal"
           :in-theory (e/d (dumb-negate-lit2
                            not
                            rp-trans-lst
                            rp-trans
                            is-falist)
()))))|#

(local
 (defthm nonnil-p-is-correct
   (implies (nonnil-p term)
            (and (rp-evl term a)
                 (rp-evlt term a)))
   :hints (("Goal"
            :expand ((rp-trans TERM))
            :in-theory (e/d (nonnil-p
                             IS-FALIST
                             rp-trans)
                            ())))))

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

(local
 (defthm valid-sc-iff
   (implies (and (CASE-MATCH TERM (('iff & &) T)))
            (equal (valid-sc term a)
                   (and (valid-sc (cadr term) a)
                        (valid-sc (caddr term) a))))
   :hints (("Goal"
            :in-theory (e/d (is-rp is-if) ())))))

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
                  (eval-and-all context a)
                  (valid-sc-subterms context a))
             (valid-sc (mv-nth 0 (rp-check-context term dont-rw context :RW-CONTEXT-FLG RW-CONTEXT-FLG)) a))
    :hints (("goal"
             :expand ((EVAL-AND-ALL CONTEXT A))
             :do-not-induct t
             :induct (rp-check-context term dont-rw context :RW-CONTEXT-FLG RW-CONTEXT-FLG)
             :in-theory (e/d (rp-check-context
                              is-falist
                              is-rp
                              valid-sc-single-step)
                             ((:DEFINITION RP-TERMP)
                              (:REWRITE VALID-SC-OF-CADR-WHEN-IS-IF)
                              (:DEFINITION RP-TERM-LISTP)
                              (:REWRITE RP-TERMP-IMPLIES-SYMBOL-CAR-TERM)
                              (:DEFINITION EVAL-AND-ALL))))))

  )

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
                              iff-flg  limit rp-state state))
             (cadr term)))
     :hints (("goal"
              :expand (rp-rw (cadr term)
                             dont-rw
                             context
                             iff-flg  limit rp-state state)
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
              (mv-nth 0 (rp-rw-subterms (cdr term) dont-rw context  limit
                                        rp-state state))
              a)
             (rp-evlt-lst (cdr term) a))
      (valid-sc-subterms
       (mv-nth 0 (rp-rw-subterms (cdr term) dont-rw context  limit
                                 rp-state state))
       a))
     (valid-sc
      (cons (car term)
            (mv-nth  0 (rp-rw-subterms (cdr term) dont-rw context  limit
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
                                      NIL CONTEXT  (+ -1 LIMIT)
                                      (MV-NTH 1
                                              (RP-RW (CADR TERM)
                                                     NIL CONTEXT
                                                     NIL  (+ -1 LIMIT) rp-state STATE))
                                      STATE)
                      (rp-rw-subterms (cddr term)
                                      (dont-rw-cdr dont-rw)
                                      context  (+ -1 limit)

                                      (mv-nth 1
                                              (rp-rw (cadr term)
                                                     (dont-rw-car dont-rw)
                                                     context
                                                     nil  (+ -1 limit) rp-state state))
                                      state)
                      (rp-rw-subterms (cdr term)
                                      dont-rw context  limit
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
;;                              (:REWRITE ACL2::O-P-O-INFP-CAR)
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

(local
 (defthmd rp-evlt-of-side-cond-eval-lemma
   (implies (and (is-rp term)
                 ;;(rp-evlt term a)
                 (VALID-SC TERM A)
                 (equal (rp-evlt x a)
                        (rp-evlt (caddr term) a)))
            (RP-EVLT (LIST (CADR (CADR TERM)) x)
                     A))
   :hints (("Goal"
            :in-theory (e/d (rp-trans
                             valid-sc-single-step
                             rp-trans-lst
                             is-rp
                             is-falist
                             rp-evl-of-fncall-args)
                            ())))))

(local
 (defthm is-rp-lemma-1
   (implies (is-rp term)
            (is-rp (list 'rp (cadr term) other)))
   :hints (("Goal"
            :in-theory (e/d (is-rp) ())))))

(local
 (defthm is-rp-lemma-2
   (implies (is-rp term)
            (EQUAL (RP-EVLT TERM A)
                   (RP-EVLT (CADDR TERM) A)))
   :hints (("Goal"
            :in-theory (e/d (is-rp) ())))))

#|(local
 (defthm valid-sc-when-is-if
         (implies (and (or (valid-sc term a)
                           (valid-sc `(if ,(cadr term)
                                          ,(caddr term)
                                        ,(cadddr term))
                                     a))
                       (is-if term)
                       (case-split (not (AND (NOT (RP-EVLT (CADDR TERM) A))
                                             (NOT (RP-EVLT (CADDDR TERM) A))))))
                  (valid-sc (cadr term) a))
         :hints (("Goal"
                  :expand ((valid-sc term a)
                           (valid-sc `(if ,(cadr term)
                                          ,(caddr term)
                                        ,(caddr term))
                                     a))
                  :in-theory (e/d (is-if
                                   is-rp)
                                  (lemma106
                                   RP-TERMP
                                   RP-TERM-LISTP
                                   LEMMA108
                                   (:REWRITE VALID-SC-CONS)))))))|#


(defthm valid-sc-subterms-of-udpate-nth
  (implies (and (valid-sc val a)
                (valid-sc-subterms lst a)
                (< i (len lst)))
           (valid-sc-subterms (update-nth i val lst) a))
  :hints (("Goal"
           :induct (update-nth i val lst)
           :do-not-induct t
           :in-theory (e/d (valid-sc-subterms
                            update-nth
                            len)
                           (valid-sc)))))

(defthm eval-and-all-of-udpate-nth
  (implies (and (rp-evlt val a)
                (eval-and-all lst a)
                (< i (len lst)))
           (eval-and-all (update-nth i val lst) a))
  :hints (("Goal"
           :induct (update-nth i val lst)
           :do-not-induct t
           :in-theory (e/d (valid-sc-subterms
                            update-nth
                            len)
                           (valid-sc)))))

(defthm eval-and-all-implies-rp-evlt-of-car-of-elements
  (implies (and (EVAL-AND-ALL OLD-CONTEXT A)
                (consp old-context))
           (and (RP-EVLT (CAR OLD-CONTEXT) A)
                (EVAL-AND-ALL (CDR OLD-CONTEXT) A)))
  :rule-classes :forward-chaining
  :hints (("Goal"
           :expand (EVAL-AND-ALL OLD-CONTEXT A)
           :in-theory (e/d () ()))))

(defthm dummy-len-equiv
  (implies (consp old-context)
           (EQUAL (LEN (CDR OLD-CONTEXT))
                  (+ -1 (LEN OLD-CONTEXT))))
  :hints (("Goal"
           :in-theory (e/d (len) ()))))



(DEFTHM
  VALID-SC-SUBTERMS-APPEND-2
  (EQUAL (VALID-SC-SUBTERMS (APPEND X Y) A)
         (AND* (VALID-SC-SUBTERMS X A)
               (VALID-SC-SUBTERMS Y A)))
  :HINTS (("Goal" :IN-THEORY (E/D (VALID-SC APPEND) NIL))))

(defthm eval-and-all-append-2
  (equal (eval-and-all (append x y) a)
         (and* (eval-and-all x a)
               (eval-and-all y a)))
  :hints (("Goal"
           :in-theory (e/d (eval-and-all
                            append) ()))))

(defthm member-equal-nil-implies
  (implies (member-equal ''nil lst)
           (not (eval-and-all lst a)))
  :hints (("Goal"
           :in-theory (e/d (member-equal
                            eval-and-all)
                           ()))))

(defthm member-equal-nil-implies-lemma-2
  (and (implies (and (member-equal ''nil (append lst1 lst2))
                     (eval-and-all lst1 a))
                (not (eval-and-all lst2 a)))
       )
  :hints (("Goal"
           :in-theory (e/d (member-equal
                            append
                            eval-and-all)
                           ()))))

(defthm member-equal-nil-implies-lemma-3
  (and (implies (and (member-equal ''nil (append lst1 lst2))
                     (eval-and-all lst2 a))
                (not (eval-and-all lst1 a)))
       )
  :hints (("Goal"
           :in-theory (e/d (member-equal
                            append
                            eval-and-all)
                           ()))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;rw-only-with-context




(defthm not-cdr-valid-sc-subterms-implies
  (implies (and (not (valid-sc-subterms (cdr term) a))
                (valid-sc term a)
                (not (quotep term)))
           (case-match term
             (('if & & &) t)))
  :rule-classes :forward-chaining
  :hints (("Goal"
           :cases ((is-rp term)
                   (is-if term))
           :in-theory (e/d (valid-sc-single-step
                            is-rp) ()))))

(defthm valid-sc-when-cdr-is-valid-sc-subterms
  (implies (and (case-split (not (equal fn 'rp)))
                (valid-sc-subterms lst a))
           (valid-sc (cons fn lst) a))
  :hints (("Goal"
           :cases ((is-rp (cons fn lst)))
           :expand (VALID-SC (CONS FN LST) A)
           :in-theory (e/d (valid-sc-single-step
                            is-rp)
                           ()))))

(defthm rw-only-with-context-subterms-is-rp-lemma
  (implies (rp-termp term)
           (equal (is-rp (cons (car term)
                               (mv-nth 0 (rw-only-with-context-subterms (cdr term) dont-rw
                                                                        context
                                                                        limit
                                                                        rp-state state))))
                  (is-rp term)))
  :hints (("Goal"
           :expand ((RW-ONLY-WITH-CONTEXT-SUBTERMS (CDR TERM)
                                                   DONT-RW CONTEXT LIMIT
                                                   RP-STATE STATE)
                    (RW-ONLY-WITH-CONTEXT (CADR TERM)
                                          (DONT-RW-CAR DONT-RW)
                                          CONTEXT NIL LIMIT RP-STATE STATE))
           :in-theory (e/d (is-rp
                            rp-termp
                            rw-only-with-context-subterms)
                           (RW-ONLY-WITH-CONTEXT)))))

(defthmd is-if-rp-evlt-lemma
  (implies (is-if term)
           (equal (rp-evlt term a)
                  (if (rp-evlt (cadr term) a)
                      (rp-evlt (caddr term) a)
                    (rp-evlt (cadddr term) a)))))

(defthmd rp-evlt-evalling-sc-lemma
  (implies (and (equal (rp-evlt large a) (rp-evlt small a))
                (not (equal sc 'falist))
                (not (equal sc 'quote)))
           (equal (rp-evlt (list sc large) a)
                  (rp-evlt (list sc small) a)))
  :hints (("Goal"
           :in-theory (e/d (rp-evl-of-fncall-args
                            rp-trans
                            is-falist)
                           ()))))

(defthmd rp-evlt-evalling-sc-lemma2
  (implies (and (syntaxp (< (cons-count term)
                            (cons-count term2)))
                (is-rp term)
                (equal (rp-evlt term2 a)
                       (rp-evlt (caddr term) a)))
           (equal (rp-evlt (list (cadr (cadr term)) term2) a)
                  (rp-evlt (list (cadr (cadr term)) (caddr term)) a)))
  :hints (("Goal"
           :use ((:instance rp-evlt-evalling-sc-lemma
                            (large term2)
                            (small (caddr term))
                            (sc (cadr (cadr term)))))
           :expand ((RP-TRANS (LIST (CADR (CADR TERM)) (CADDR TERM))))
           :in-theory (e/d (is-rp
                            is-falist)
                           (rp-evlt-evalling-sc-lemma
                            rp-trans
                            )))))

(defthm rp-evlt-evalling-sc-lemma3
  (implies (and (is-rp term)
                (valid-sc term a)
                (equal (rp-evlt term2 a)
                       (rp-evlt (caddr term) a)))
           (rp-evlt (list (cadr (cadr term)) term2) a))
  :hints (("Goal"
           :use ((:instance rp-evlt-evalling-sc-lemma2))
           :in-theory (e/d (is-rp
                            valid-sc-single-step
                            is-falist)
                           (rp-evlt-evalling-sc-lemma
                            rp-evlt-evalling-sc-lemma2
                            rp-trans
                            )))))

(defthmd rp-evlt-equiv-when-one-is-rp
  (implies (and (is-rp term1)
                (equal (rp-evlt term1 a)
                       (rp-evlt term2 a)))
           (equal (equal (rp-evlt (caddr term1) a)
                         (rp-evlt term2 a))
                  t)))

(defthm rp-check-context-is-correct2
  (implies
   (and
    (context-syntaxp context)
    (eval-and-all context a)
    (not iff-flg)
    (is-rp (mv-nth 0 (rp-check-context term dont-rw context :RW-CONTEXT-FLG RW-CONTEXT-FLG))))
   (equal (rp-evlt (caddr (mv-nth 0 (rp-check-context term dont-rw context :RW-CONTEXT-FLG RW-CONTEXT-FLG))) a)
          (rp-evlt term a)))
  :hints (("Goal"
           :use ((:instance rp-check-context-is-correct))
           :in-theory (e/d ()
                           (RP-TERM-LISTP-IS-TRUE-LISTP
                            rp-check-context-is-correct
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:REWRITE RP-EQUAL2-BINDINGS-1TO1-CONSP)
                            falist-consistent
                            RP-TERMP-IMPLIES-SUBTERMS)))))

(defthm rp-check-context-is-correct2-iff-flg
  (implies
   (and
    (context-syntaxp context)
    (eval-and-all context a)
    iff-flg
    (is-rp (mv-nth 0 (rp-check-context term dont-rw context :RW-CONTEXT-FLG RW-CONTEXT-FLG))))
   (iff (rp-evlt (caddr (mv-nth 0 (rp-check-context term dont-rw context :RW-CONTEXT-FLG RW-CONTEXT-FLG))) a)
        (rp-evlt term a)))
  :hints (("Goal"
           :use ((:instance rp-check-context-is-correct-iff))
           :in-theory (e/d ()
                           (RP-TERM-LISTP-IS-TRUE-LISTP
                            rp-check-context-is-correct
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:REWRITE RP-EQUAL2-BINDINGS-1TO1-CONSP)
                            falist-consistent
                            RP-TERMP-IMPLIES-SUBTERMS)))))

(defthm-rw-only-with-context
  (defthm valid-sc-and-eval-rw-only-with-context
    (implies (and (valid-sc-subterms context a)
                  (context-syntaxp context)
                  (valid-sc term a)
                  (eval-and-all context a)
                  (rp-termp term)
                  (rp-evl-meta-extract-global-facts :state state))
             (let ((res (mv-nth 0 (rw-only-with-context term dont-rw context iff-flg limit rp-state
                                                        state))))
               (and (valid-sc res  a)
                    (implies iff-flg
                             (iff (rp-evlt res a) (rp-evlt term a)))
                    (implies (not iff-flg)
                             (equal (rp-evlt res a) (rp-evlt term a))))))
    :flag rw-only-with-context)
  (defthm valid-sc-and-eval-rw-only-with-context-if
    (implies (and (valid-sc-subterms context a)
                  (context-syntaxp context)
                  (valid-sc term a)
                  (eval-and-all context a)
                  (rp-termp term)
                  (is-if term)
                  (rp-evl-meta-extract-global-facts :state state))
             (let ((res (mv-nth 0 (rw-only-with-context-if term dont-rw context iff-flg limit rp-state
                                                           state))))
               (and (valid-sc res  a)
                    (implies iff-flg
                             (iff (rp-evlt res a) (rp-evlt term a)))
                    (implies (not iff-flg)
                             (equal (rp-evlt res a) (rp-evlt term a))))))
    :flag rw-only-with-context-if)
  (defthm valid-sc-subterms-and-eval-of-rw-only-with-context-subterms
    (implies (and (valid-sc-subterms context a)
                  (context-syntaxp context)
                  (valid-sc-subterms lst a)
                  (eval-and-all context a)
                  (rp-term-listp lst)
                  (rp-evl-meta-extract-global-facts :state state))
             (let ((res (mv-nth 0 (rw-only-with-context-subterms lst dont-rw
                                                                 context
                                                                 limit
                                                                 rp-state state))))
               (and (valid-sc-subterms res a)
                    (equal (rp-evlt-lst res a) (rp-evlt-lst lst a)))))
    :flag rw-only-with-context-subterms)
  :hints (("Subgoal *1/8"
           :use ((:instance is-if-rp-evlt-lemma
                            (term (MV-NTH 0
                                          (RP-CHECK-CONTEXT TERM DONT-RW
                                                            CONTEXT
                                                            :iff-flg nil
                                                            :RW-CONTEXT-FLG RW-CONTEXT-FLG))))
                 (:instance is-if-rp-evlt-lemma
                            (term (MV-NTH 0
                                          (RP-CHECK-CONTEXT TERM DONT-RW CONTEXT :RW-CONTEXT-FLG RW-CONTEXT-FLG))))
                 ))
          ("Goal"
           :do-not-induct t
           :expand ((IS-IF TERM))
           :in-theory (e/d (rw-only-with-context
                            IS-RP-IMPLIES-FC
                            valid-sc-single-step
                            CONTEXT-SYNTAXP
                            rw-only-with-context-subterms
                            is-falist
                            rp-evlt-equiv-when-one-is-rp
                            )
                           (VALID-RP-STATEP
                            NONNIL-P-IS-CORRECT
                            NOT-INCLUDE-RP
                            eval-and-all
                            (:REWRITE LEMMA0)
                            (:REWRITE
                             RP-EX-COUNTERPART-IS-TERM-NOT-QUOTEP)
                            rp-termp
                            IS-IF$INLINE
                            is-rp-lemma-2
                            is-if-implies)))))

(defthm valid-sc-subterms-and-eval-of-rw-only-with-context-lst$iff-flg=t
  (implies (and (valid-sc-subterms context a)
                (context-syntaxp context)
                (valid-sc-subterms lst a)
                (eval-and-all context a)
                (eval-and-all lst a)
                (rp-term-listp lst)
                (rp-evl-meta-extract-global-facts :state state))
           (let ((res (mv-nth 0 (rw-only-with-context-lst$iff-flg=t lst dont-rw
                                                                    context
                                                                    limit
                                                                    rp-state state))))
             (and (valid-sc-subterms res a)
                  (eval-and-all res a))))
  :hints (("subgoal *1/2"
           :use ((:instance valid-sc-and-eval-rw-only-with-context
                            (iff-flg t)
                            (dont-rw (dont-rw-car dont-rw))
                            (term (car lst)))))
          ("goal"
           :in-theory (e/d (rw-only-with-context-lst$iff-flg=t)
                           (rw-only-with-context
                            rw-only-with-context-subterms)))))

(local
 (in-theory (disable rw-only-with-context-lst$iff-flg=t
                     rw-only-with-context
                     rw-only-with-context-subterms
                     rw-only-with-context-if)))

(set-case-split-limitations '(3000 900))

(local
 (defthm IS-DONT-RW-CONTEXT-eval-lemma
   (implies (is-dont-rw-context term)
            (equal (rp-evlt term a)
                   (rp-evlt (cadr term) a)))
   :hints (("Goal"
            :in-theory (e/d (rp-trans
                             DONT-RW-CONTEXT
                             RP-TRANS-LST
                             IS-DONT-RW-CONTEXT
                             is-falist) ())))))

(defthm eval-of-clear-context-for-rw-only-with-context
  (implies (eval-and-all context a)
           (eval-and-all (clear-context-for-rw-only-with-context context) a)))

(defthm valid-sc-of-clear-context-for-rw-only-with-context
  (implies (valid-sc-subterms context a)
           (valid-sc-subterms (clear-context-for-rw-only-with-context context) a)))

(defthm eval-and-all-of-RP-REMOVE-EQUAL
  (implies (eval-and-all lst a)
           (eval-and-all (RP-REMOVE-EQUAL x lst) a))
  :hints (("Goal"
           :in-theory (e/d (RP-REMOVE-EQUAL) ()))))

(defthm  VALID-SC-SUBTERMS-of-RP-REMOVE-EQUAL
  (implies (VALID-SC-SUBTERMS lst a)
           (VALID-SC-SUBTERMS (RP-REMOVE-EQUAL x lst) a))
  :hints (("Goal"
           :in-theory (e/d (RP-REMOVE-EQUAL) ()))))

;; (local
;;  (defthm or*-assoc
;;    (equal (or* (or* a b) c)
;;           (or* a b c))
;;    :hints (("Goal"
;;             :in-theory (e/d (or*) ())))))

;; (local
;;  (defthm not*-of-and*/or*
;;    (and (equal (not* (or* a b))
;;                (and* (not* a) (not* b)))
;;         (equal (not* (and* a b))
;;                (or* (not* a) (not* b))))
;;    :hints (("Goal"
;;             :in-theory (e/d (or* and*) ())))))

#|(Local
 (in-theory (disable BACKCHAINING-RULE
                     RW-CONTEXT-DISABLED
                     (:REWRITE ACL2::AND*-NIL-FIRST)
                     (:REWRITE ACL2::AND*-NIL-SECOND)
                     ;;(:REWRITE ACL2::AND*-REM-FIRST)
                     ;;(:REWRITE ACL2::AND*-REM-SECOND )
                     (:REWRITE ACL2::OR*-NIL-FIRST)
                     (:REWRITE ACL2::OR*-NIL-SECOND)
                     (:REWRITE ACL2::OR*-TRUE-SECOND)
                     (:TYPE-PRESCRIPTION ACL2::BINARY-AND*)
                     ;;(:REWRITE NOT*-OF-AND*/OR*)
                     ;;(:REWRITE OR*-ASSOC)
                     (:EXECUTABLE-COUNTERPART ACL2::BINARY-AND*)
                     (:EXECUTABLE-COUNTERPART ACL2::BINARY-OR*)
                     (:EXECUTABLE-COUNTERPART NOT*)
                     (:REWRITE ACL2::OR*-TRUE-FIRST)
                     ACL2::IFF-IMPLIES-IFF-AND*-2

                     ACL2::IFF-IMPLIES-EQUAL-AND*-1)))|#

(local
 (in-theory (disable
             (:TYPE-PRESCRIPTION BINARY-OR**)
             (:REWRITE NONNIL-P-IS-CORRECT)
             (:TYPE-PRESCRIPTION MEMBER-EQUAL)
             ;; (:REWRITE ACL2::PLAIN-UQI-RATIONAL-LISTP)
             (:TYPE-PRESCRIPTION VALID-RP-STATEP)
             (:REWRITE VALID-SC-CADR)
             ;; (:REWRITE ACL2::PLAIN-UQI-SYMBOL-LISTP)
             (:TYPE-PRESCRIPTION ALWAYS$)
             (:REWRITE RP-EVL-OF-ZP-CALL)
             ;; (:REWRITE ACL2::PLAIN-UQI-TRUE-LIST-LISTP)
             (:TYPE-PRESCRIPTION IS-DONT-RW-CONTEXT)
             (:FORWARD-CHAINING NOT-OF-NOT*-FORWARD)
             (:TYPE-PRESCRIPTION ACL2::BINARY-AND*)
             (:TYPE-PRESCRIPTION BINARY-AND**)
             (:TYPE-PRESCRIPTION NONNIL-P))))

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
                              (rp-rw term dont-rw context
                                     iff-flg limit rp-state state))))
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
                              (rp-rw-if term dont-rw context iff-flg  limit rp-state state))))
                 (and  (valid-sc res a)
                       (implies iff-flg
                                (iff (rp-evlt res a) (rp-evlt term a)))
                       (implies (not iff-flg)
                                (equal (rp-evlt res a) (rp-evlt term a))))))
      :flag rp-rw-if)


    (defthm rp-evl-and-side-cond-consistent-rp-rw-if-branch
      (implies (and (rp-termp then)
                    (rp-termp cond-rw)
                    (RP-STATEP RP-STATE)
                    (alistp a)

                    (rp-evl-meta-extract-global-facts :state state)
                    (context-syntaxp context)

                    (valid-sc-subterms context a)

                    (rp-formula-checks state)

                    (eval-and-all context a)
                    (valid-sc then a)
                    (valid-sc cond-rw a)
                    (valid-rp-statep rp-state))
               (b* (((mv r1 r1-context-has-nil &)
                     (RP-RW-IF-BRANCH COND-RW THEN THEN-DONT-RW CONTEXT
                                      IFF-FLG  LIMIT RP-STATE STATE)))
                 (and  (implies (rp-evlt cond-rw a)
                                (valid-sc r1 a))
                       (implies r1-context-has-nil
                                (not (rp-evlt cond-rw a)))
                       (implies (and iff-flg
                                     (rp-evlt cond-rw a))
                                (iff (rp-evlt r1 a) (rp-evlt then a)))
                       (implies (and (not iff-flg)
                                     (rp-evlt cond-rw a))
                                (equal (rp-evlt r1 a) (rp-evlt then a))))))
      :flag rp-rw-if-branch)

    (defthm rp-evl-and-side-cond-consistent-rp-rw-relieve-hyp
      (implies (and (rp-term-listp term-lst)
                    (RP-STATEP RP-STATE)
                    (alistp a)

                    (rp-evl-meta-extract-global-facts :state state)
                    (context-syntaxp context)

                    (valid-sc-subterms context a)

                    (rp-formula-checks state)

                    (eval-and-all context a)
                    (valid-sc-subterms term-lst a)
                    (valid-rp-statep rp-state)
                    (mv-nth 0 (rp-rw-relieve-hyp term-lst dont-rw context rule stack-index var-bindings limit rp-state state)))
               (eval-and-all term-lst a))
      :flag rp-rw-relieve-hyp)

    (defthm rp-evl-and-side-cond-consistent-rp-rw-and
      (implies (and (rp-termp term1)
                    (rp-termp term2)
                    (RP-STATEP RP-STATE)
                    (alistp a)

                    (rp-evl-meta-extract-global-facts :state state)
                    (context-syntaxp context)

                    (valid-sc-subterms context a)

                    (rp-formula-checks state)

                    (eval-and-all context a)

                    (valid-rp-statep rp-state))
               (let ((res
                      (mv-nth 0 (rp-rw-and term1 term2 context  limit rp-state state))))
                 (and  (implies (and (valid-sc term1 a)
                                     (valid-sc term2 a))
                                (valid-sc res a))
                       ;; below are to serve as some stupid lemmas for the cases
                       ;; observed in subgoals
                       (implies (and (valid-sc term1 a)
                                     (valid-sc term2 a))
                                (iff (rp-evlt res a) (rp-evlt `(if ,term1 ,term2 'nil) a)))
                       (implies (and (not (rp-evlt term1 a))
                                     (valid-sc term1 a))
                                (and (valid-sc res a)
                                     (iff (rp-evlt res a) nil))))))
      :flag rp-rw-and)

    (defthm rp-evl-and-side-cond-consistent-rp-rw-context
      (implies (and (context-syntaxp new-context)
                    (context-syntaxp old-context)
                    (alistp a)
                    (rp-statep rp-state)
                    (valid-rp-statep rp-state)

                    (rp-evl-meta-extract-global-facts :state state)
                    (rp-formula-checks state)

                    (valid-sc-subterms new-context a)
                    (valid-sc-subterms old-context a)

                    (eval-and-all new-context a)
                    (eval-and-all old-context a))
               (let ((res
                      (mv-nth 0 (rp-rw-context old-context new-context limit
                                               rp-state state))))
                 (and (valid-sc-subterms res a)
                      (eval-and-all res a)
                      #|(iff (rp-evlt-lst res a)
                      (rp-evlt-lst old-context a))|#)))
      :flag rp-rw-context)

    (defthm rp-evl-and-side-cond-consistent-rp-rw-context-loop
      (implies (and (context-syntaxp context)

                    (alistp a)
                    (rp-statep rp-state)
                    (valid-rp-statep rp-state)

                    (rp-evl-meta-extract-global-facts :state state)
                    (rp-formula-checks state)

                    (valid-sc-subterms context a)
                    (eval-and-all context a)
                    )
               (let ((res
                      (mv-nth 0 (rp-rw-context-loop context limit loop-limit
                                                    rp-state state))))
                 (and (valid-sc-subterms res a)
                      (eval-and-all res a)
                      #|(iff (rp-evlt-lst res a)
                      (rp-evlt-lst old-context a))|#)))
      :flag rp-rw-context-loop)

    (defthm rp-evl-and-side-cond-consistent-rp-rw-context-main
      (implies (and (context-syntaxp context)
                    (rp-termp term)
                    (alistp a)
                    (rp-statep rp-state)
                    (valid-rp-statep rp-state)

                    (rp-evl-meta-extract-global-facts :state state)
                    (rp-formula-checks state)

                    (valid-sc term a)
                    (valid-sc-subterms context a)

                    (rp-evlt term a)
                    (eval-and-all context a)

                    )
               (let ((res
                      (mv-nth 0 (rp-rw-context-main term context enabled QUICK-ENABLED limit rp-state state))))
                 (and (valid-sc-subterms res a)
                      (eval-and-all res a)
                      #|(iff (rp-evlt-lst res a)
                      (rp-evlt-lst old-context a))|#)))
      :flag rp-rw-context-main)

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
                      (mv-nth 0 (rp-rw-subterms subterms dont-rw context  limit
                                                rp-state state))))
                 (and (valid-sc-subterms res a)
                      (equal (rp-evlt-lst res a) (rp-evlt-lst subterms a)))))
      :flag rp-rw-subterms)
    :otf-flg nil
    :hints (("goal"
             #|:induct (FLAG-RP-RW FLAG RULES-FOR-TERM
             OUTSIDE-IN-FLG TERM IFF-FLG SUBTERMS
             DONT-RW CONTEXT  LIMIT RP-STATE STATE)|#
             :do-not-induct t
             :in-theory (e/d (;;rp-evl-of-fncall-args
                              rp-rule-rwp
                              rp-term-listp
                              ;;valid-sc-single-step
                              valid-sc-single-step-2
                              is-rp-implies-fc
                              rp-evlt-of-side-cond-eval-lemma
                              RP-EQUAL-IMPLIES-EQUAL-RP-EVLT-1

                              )
                             (

                              if*

                              (:TYPE-PRESCRIPTION NOT*)
                              rp-evl-of-quote
                              RP-TRANS-LST
                              rp-termp
                              is-rp
                              rp-evl-of-variable
;;                              (:rewrite acl2::o-p-o-infp-car)
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
;;                              (:forward-chaining
;;                               acl2::|a <= b & ~(a = b)  =>  a < b|)
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
             ((:free (x y)
                     (eval-and-all (cons x y) a))
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
              (RP-RW-IF-BRANCH COND-RW THEN THEN-DONT-RW CONTEXT
                                    NIL  LIMIT RP-STATE STATE)
              (RP-RW-CONTEXT-LOOP NIL LIMIT LOOP-LIMIT RP-STATE STATE)
              (RP-RW-CONTEXT-MAIN TERM CONTEXT
                                  ENABLED NIL LIMIT RP-STATE STATE)

              (rp-rw-relieve-hyp term-lst dont-rw context rule stack-index
                                 var-bindings limit rp-state state)
              (rp-rw-context-main term context enabled QUICK-ENABLED limit
                                  rp-state state)
              (rp-rw-context-main term context nil QUICK-ENABLED limit rp-state
                                  state)
              (RP-RW-IF-BRANCH COND-RW THEN THEN-DONT-RW CONTEXT
                                    IFF-FLG  LIMIT RP-STATE STATE)
              (rp-rw-and term1 term2 context  limit rp-state state)
              (RP-RW-CONTEXT NIL NEW-CONTEXT  LIMIT RP-STATE STATE)
              (RP-RW-CONTEXT NIL NEW-CONTEXT  LIMIT RP-STATE STATE)
              (rp-rw-context old-context new-context  limit
                             rp-state state)
              (RP-RW-CONTEXT CONTEXT CONTEXT (+ -1 LIMIT)
                             RP-STATE STATE)
              (RP-RW-CONTEXT CONTEXT CONTEXT 0 RP-STATE STATE)
              (RP-RW-CONTEXT-LOOP CONTEXT
                                  LIMIT LOOP-LIMIT RP-STATE STATE)
              (RP-RW-IF TERM DONT-RW CONTEXT
                        NIL  LIMIT RP-STATE STATE)
              (RP-RW-IF TERM DONT-RW
                        CONTEXT NIL  LIMIT RP-STATE STATE)
              (RP-RW-IF TERM DONT-RW CONTEXT
                        IFF-FLG  LIMIT RP-STATE STATE)
              (rp-rw-if term dont-rw
                        context nil  limit rp-state state)
              (rp-rw-if term dont-rw context iff-flg  limit rp-state state)
              (rp-rw term dont-rw context
                     iff-flg  limit rp-state state)
              (rp-rw term dont-rw context
                     nil  limit rp-state state)
              (rp-rw (cadr subterms)
                     (cadr dont-rw)
                     context
                     nil  (+ -2 limit) rp-state state)
              (rp-rw term t context
                     iff-flg  limit rp-state state)
              (rp-rw-if term dont-rw context
                        nil  limit rp-state state)
              (rp-rw-subterms subterms dont-rw context
                               limit  rp-state state)
              (rp-rw-subterms (cdr subterms)
                              (cdr dont-rw)
                              context  (+ -1 limit)
                              rp-state state)
              (rp-rw-subterms (cddr subterms)
                              (cddr dont-rw)
                              context  (+ -2 limit)
                              rp-state state)
              (rp-rw-subterms nil dont-rw context 
                              limit  rp-state state))))))
