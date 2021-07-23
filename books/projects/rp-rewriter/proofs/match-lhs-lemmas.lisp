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
(include-book "local-lemmas")
(include-book "proof-functions")
(include-book "rp-equal-lemmas")
(include-book "apply-bindings-lemmas")
(include-book "aux-function-lemmas")

(in-theory (disable default-car
                    (:DEFINITION NOT)
                    default-cdr))

(make-flag rp-match-lhs :defthm-macro-name defthm-rp-match-lhs)

(local
 (in-theory (disable EXTRACT-FROM-RP-WITH-CONTEXT
                     ex-from-rp
                     PUT-TERM-IN-CONS
                     SHOULD-TERM-BE-IN-CONS
                     context-from-rp
                     ex-from-synp)))

(encapsulate
  nil
  (local
   (in-theory (e/d (extract-from-rp-with-context-context)
                   (extract-from-rp-with-context))))
  (defthm-rp-match-lhs
    ;; for guard of rp-rw-rule-aux and rp-rw
    (defthm return-val-of-rp-match-lhs-context
      (implies (and (context-syntaxp context)
                    (rp-termp rule-lhs)
                    (rp-termp term))
               (context-syntaxp (mv-nth 0 (RP-MATCH-LHS term rule-lhs context
                                                        acc-bindings))))
      :flag rp-match-lhs)
    (defthm return-val-of-rp-match-lhs-context-subterms
      (implies (and (context-syntaxp context)
                    (rp-term-listp sublhs)
                    (rp-term-listp subterms))
               (context-syntaxp (mv-nth 0 (rp-match-lhs-subterms subterms sublhs context
                                                                 acc-bindings))))
      :flag rp-match-lhs-subterms)))

(defthm-rp-match-lhs
  (defthm bindings-alistp-rp-match-lhs
    (implies (and (bindings-alistp acc-bindings)
                  (rp-termp rule-lhs)
                  (rp-termp term))
             (bindings-alistp (mv-nth 1 (rp-match-lhs term rule-lhs context
                                                      acc-bindings))))
    :flag rp-match-lhs)
  (defthm bindings-alistp-rp-match-lhs-subterms
    (implies (and (bindings-alistp acc-bindings)
                  (rp-term-listp subterms)
                  (rp-term-listp sublhs))
             (bindings-alistp
              (mv-nth 1 (rp-match-lhs-subterms subterms
                                               sublhs context acc-bindings))))
    :flag rp-match-lhs-subterms))

(defthm-rp-match-lhs
  (defthm alistp-rp-match-lhs
    (implies (and (alistp acc-bindings))
             (alistp (mv-nth 1 (rp-match-lhs term rule-lhs context
                                             acc-bindings))))
    :flag rp-match-lhs)
  (defthm alistp-rp-match-lhs-subterms
    (implies (and (alistp acc-bindings))
             (alistp
              (mv-nth 1 (rp-match-lhs-subterms subterms
                                               sublhs context acc-bindings))))
    :flag rp-match-lhs-subterms))

; Matt K. mod 7/2021: The following lemma is no longer accepted due to a
; strengthening of remove-guard-holders.
#||
(local
 (defthm should-term-be-in-cons-lemma1
   (implies (should-term-be-in-cons rule-lhs term)
            (and (quotep term)
                 (consp term)
                 (consp (unquote term))
                 (case-match rule-lhs (('cons & &) t)
                   (& nil))))
   :hints (("Goal" :in-theory (enable should-term-be-in-cons)))))
||#

; Matt K. mod 7/2021: The following lemma is no longer accepted due to a
; strengthening of remove-guard-holders.
#||
(local
 (defthm is-snyp-props
   (implies (is-synp term)
            (case-match term (('synp & & &) t)
              (& nil)))))
||#

(defmacro bindings-from (x)
  `(mv-nth 1 ,x))

#|(local
 (defthm bindings-from-lemma
   (and (equal (mv-nth 1 (rp-match-lhs-subterms a b c d))
               (bindings-from (rp-match-lhs-subterms a b c d)))
        (equal (mv-nth 1 (rp-match-lhs a b c d))
               (bindings-from (rp-match-lhs a b c d))))
   :hints (("Goal" :in-theory (enable bindings-from)))))||#

(defmacro bindings-valid (x)
  `(mv-nth 2 ,x))

#|(local
 (defthm bindings-valid-lemma
   (and (equal (mv-nth 2 (rp-match-lhs-subterms a b c d))
               (bindings-valid (rp-match-lhs-subterms a b c d)))
        (equal (mv-nth 2 (rp-match-lhs a b c d))
               (bindings-valid (rp-match-lhs a b c d))))
   :hints (("Goal" :in-theory (enable bindings-valid)))))||#

(defmacro rp-context-from (x)
  `(mv-nth 0 ,x))

#|(local
 (defthm rp-context-from-lemma
   (and (equal (mv-nth 0 (rp-match-lhs-subterms a b c d))
               (rp-context-from (rp-match-lhs-subterms a b c d)))
        (equal (mv-nth 0 (rp-match-lhs a b c d))
               (rp-context-from (rp-match-lhs a b c d))))
   :hints (("Goal" :in-theory (enable rp-context-from)))))||#

#|(encapsulate
  nil

  (skip-proofs
   (defthm-rp-match-lhs
     (defthm rp-match-lhs-binds-all
       (implies
        (and (rp-termp term)
             (rp-termp rule-lhs)
             (bindings-alistp acc-bindings)
             (equal
              res-bindings
              (bindings-from
               (rp-match-lhs term rule-lhs context acc-bindings)))
             (bindings-valid
              (rp-match-lhs term rule-lhs context acc-bindings)))
        (all-vars-bound (get-vars2 rule-lhs) res-bindings))
       :flag rp-match-lhs)

     (defthm rp-match-lhs-subterms-binds-all
       (implies
        (and (rp-term-listp subterms)
             (rp-term-listp sublhs)
             (bindings-alistp acc-bindings)
             (equal
              res-bindings
              (bindings-from
               (rp-match-lhs-subterms subterms sublhs context acc-bindings)))
             (bindings-valid
              (rp-match-lhs-subterms subterms sublhs context acc-bindings)))
        (all-vars-bound (get-vars2-subterms sublhs)
                        res-bindings))
       :flag rp-match-lhs-subterms)
     :hints (("Goal"
              :in-theory (e/d #|(bindings-from bindings-valid)||#
                          #|(bindings-from-lemma
                          bindings-valid-lemma)||#))))))||#

;;;;;;;;;;;;;;;;;;;

(encapsulate
  nil

  (local
   (include-book "std/lists/top" :dir :system))

  (local
   (defthm lemma1-2
     (implies (and (subsetp context (context-from-rp term context))
                   (subsetp (context-from-rp term context) c))
              (subsetp context c))
     :hints (("goal"
              :in-theory (disable acl2::subsetp-trans2)
              :use ((:instance acl2::subsetp-trans2
                               (acl2::x context)
                               (acl2::y (context-from-rp term context))
                               (acl2::z c)))))))

  (local
   (defthm stupid
     (implies
      (and
       (subsetp-equal
        (context-from-rp term context)
        (mv-nth 0
                (rp-match-lhs-subterms (cdr (put-term-in-cons (ex-from-rp term)))
                                       (cdr rule-lhs)
                                       (context-from-rp term context)
                                       acc-bindings))))
      (subsetp-equal
       context
       (mv-nth 0
               (rp-match-lhs-subterms (cdr (put-term-in-cons (ex-from-rp term)))
                                      (cdr rule-lhs)
                                      (context-from-rp term context)
                                      acc-bindings))))
     :instructions (:promote (:rewrite lemma1-2) :s :s)))

  (local
   (defthm  stupid-2
     (implies
      (and
       (subsetp-equal
        (context-from-rp term context)
        (mv-nth 0
                (rp-match-lhs-subterms (cdr (ex-from-rp term))
                                       (cdr rule-lhs)
                                       (context-from-rp term context)
                                       acc-bindings))))
      (subsetp-equal
       context
       (mv-nth 0
               (rp-match-lhs-subterms (cdr (ex-from-rp term))
                                      (cdr rule-lhs)
                                      (context-from-rp term context)
                                      acc-bindings))))
     :instructions (:promote (:rewrite lemma1-2) :s :s)))

  (defthm-rp-match-lhs
    (defthm rp-match-lhs-subsetp-context
      (subsetp context
               (rp-context-from
                (rp-match-lhs term rule-lhs context acc-bindings)))
      :flag rp-match-lhs)

    (defthm rp-match-lhs-subterms-subsetp-context
      (subsetp context
               (rp-context-from
                (rp-match-lhs-subterms subterms sublhs context acc-bindings)))
      :flag rp-match-lhs-subterms)
    :hints (("Goal"
             :in-theory (e/d ()
                             ((:META ACL2::MV-NTH-CONS-META)
                              car-cons cdr-cons endp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  nil

  (defthm valid-sc-put-term-in-cons
    (implies (and (should-term-be-in-cons rule-lhs term))
             (valid-sc (put-term-in-cons term) a))
    :hints (("Goal"
             :in-theory (e/d (should-term-be-in-cons
                              put-term-in-cons) ()))))

  (local
   (defthm lemma1
     (implies (and (valid-sc term a)
                   (consp term)
                   (not (equal (car term) 'quote))
                   (not (is-rp term))
                   (not (equal (car term) 'if)))
              (valid-sc-subterms (cdr term) a))
     :hints (("Goal"
              :expand ((valid-sc term a)
                       (VALID-SC-SUBTERMS (CDR TERM) A)
                       (VALID-SC-SUBTERMS (CDDR TERM) A)
                       (VALID-SC-SUBTERMS (CDDDR TERM) A))
              :in-theory (e/d (is-if) ())))))

  (local
   (defthm lemma2
     (NOT (IS-RP (EX-FROM-RP TERM)))
     :hints (("Goal"
              :in-theory (e/d (is-rp ex-from-rp) ())))))

  (local
   (defthm lemma3
     (NOT (EQUAL (CAR (PUT-TERM-IN-CONS (EX-FROM-RP TERM)))
                 'QUOTE))
     :hints (("Goal"
              :in-theory (e/d (put-term-in-cons) ())))))

  (local
   (defthm lemma4
     (NOT (IS-RP (PUT-TERM-IN-CONS (EX-FROM-RP TERM))))
     :hints (("Goal"
              :in-theory (e/d (is-rp
                               put-term-in-cons) ())))))

  (local
   (defthm lemma5
     (NOT (EQUAL (CAR (PUT-TERM-IN-CONS (EX-FROM-RP TERM)))
                 'IF))
     :hints (("Goal"
              :in-theory (e/d (put-term-in-cons) ())))))

  (defthm-rp-match-lhs
    (defthm rp-match-lhs-returns-valid-sc-bindings
      (implies (and (valid-sc term a)
                    (not (include-fnc rule-lhs 'if))
                    (valid-sc-bindings acc-bindings a)
                    (mv-nth 2 (rp-match-lhs term
                                            rule-lhs
                                            context
                                            acc-bindings)))
               (valid-sc-bindings
                (mv-nth 1 (rp-match-lhs term
                                        rule-lhs
                                        context
                                        acc-bindings))
                a))
      :flag rp-match-lhs)

    (defthm rp-match-lhs-returns-valid-sc-bindings-subterms
      (implies (and (valid-sc-subterms subterms a)
                    (not (include-fnc-subterms sublhs 'if))
                    (valid-sc-bindings acc-bindings a)
                    (mv-nth 2 (rp-match-lhs-subterms
                               subterms
                               sublhs
                               context
                               acc-bindings)))
               (valid-sc-bindings
                (mv-nth 1 (rp-match-lhs-subterms
                           subterms
                           sublhs
                           context
                           acc-bindings))
                a))
      :flag rp-match-lhs-subterms)
    :hints (("Goal"
             :in-theory (e/d ()
                             ((:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                              (:DEFINITION ACL2::APPLY$-BADGEP)
                              (:DEFINITION RP-TERMP)
                              (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                              (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                              (:DEFINITION TRUE-LISTP)
                              (:REWRITE VALID-SC-CONS)
                              (:DEFINITION SUBSETP-EQUAL)
                              (:DEFINITION MEMBER-EQUAL)
                              (:DEFINITION FALIST-CONSISTENT)
                              (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
; Obsolete (see Matt K. comment above):
;                             (:REWRITE SHOULD-TERM-BE-IN-CONS-LEMMA1)
                              (:REWRITE NOT-INCLUDE-RP)
                              (:DEFINITION FALIST-CONSISTENT-AUX)
                              (:REWRITE ACL2::O-P-O-INFP-CAR)
                              (:REWRITE
                               ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)))))))

(local
 (in-theory (disable context-syntaxp)))

(defthm return-val-of-rp-rw-rule-aux-context
  (implies (and (context-syntaxp context)
                (rule-list-syntaxp rules-for-term)
                (rp-termp term))
           (context-syntaxp (mv-nth 3 (rp-rw-rule-aux term rules-for-term
                                                      context iff-flg state))))
  :hints (("Goal"
           :in-theory (e/d (rule-syntaxp)
                           ((:DEFINITION SUBSETP-EQUAL)
                            (:DEFINITION RP-TERMP)
                            (:DEFINITION MEMBER-EQUAL)
                            (:DEFINITION VALID-RULEP)
                            (:DEFINITION TRUE-LISTP)
                            (:DEFINITION ALWAYS$)
                            (:REWRITE ACL2::PLAIN-UQI-TRUE-LIST-LISTP)
                            (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                            (:DEFINITION VALID-RULEP-SK)
                            (:DEFINITION VALID-RULEP-SK-BODY)
                            (:DEFINITION TRUE-LIST-LISTP)
                            (:REWRITE
                             ACL2::TRUE-LIST-LISTP-IMPLIES-ALWAYS$-TRUE-LISTP)
                            (:DEFINITION FALIST-CONSISTENT)
                            (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP))))))

(defthm return-val-of-rp-rw-rule-aux-context-RP-TERM-LISTP
  (implies (and (RP-TERM-LISTP context)
                (rule-list-syntaxp rules-for-term)
                (rp-termp term))
           (RP-TERM-LISTP (mv-nth 3 (rp-rw-rule-aux term rules-for-term
                                                    context iff-flg state))))
  :hints (("Goal"
           :use ((:instance return-val-of-rp-rw-rule-aux-context))
           :in-theory '(context-syntaxp))))

(defthm return-val-of-rp-rw-rule-aux-bindings
  (implies (and (rule-list-syntaxp rules-for-term)
                (rp-termp term))
           (bindings-alistp (mv-nth 2 (rp-rw-rule-aux term rules-for-term
                                                      context iff-flg state))))
  :hints (("Goal"
           :in-theory (e/d (rule-syntaxp)
                           ((:DEFINITION SUBSETP-EQUAL)
                            (:DEFINITION VALID-RULEP)
                            (:DEFINITION RP-TERMP)
                            (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                            (:DEFINITION MEMBER-EQUAL)
                            (:DEFINITION TRUE-LISTP)
                            (:DEFINITION ALWAYS$)
                            (:REWRITE ACL2::PLAIN-UQI-TRUE-LIST-LISTP)
                            (:DEFINITION VALID-RULEP-SK)
                            (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                            (:DEFINITION VALID-SC)
; Obsolete (see Matt K. comment above):
;                           (:REWRITE SHOULD-TERM-BE-IN-CONS-LEMMA1)
                            (:REWRITE
                             ACL2::TRUE-LIST-LISTP-IMPLIES-ALWAYS$-TRUE-LISTP)
                            (:DEFINITION FALIST-CONSISTENT))))))

(defthm return-val-of-rp-rw-rule-aux-bindings-alistp
  (alistp (mv-nth 2 (rp-rw-rule-aux term rules-for-term
                                    context iff-flg state)))
  :hints (("Goal"
           :in-theory (e/d () ((:DEFINITION SUBSETP-EQUAL)
                               (:DEFINITION VALID-RULEP)
                               (:DEFINITION RP-TERMP)
                               (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                               (:DEFINITION MEMBER-EQUAL)
                               (:DEFINITION TRUE-LISTP)
                               (:DEFINITION ALWAYS$)
                               (:REWRITE ACL2::PLAIN-UQI-TRUE-LIST-LISTP)
                               (:DEFINITION VALID-RULEP-SK)
                               (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                               (:DEFINITION VALID-SC)
; Obsolete (see Matt K. comment above):
;                              (:REWRITE SHOULD-TERM-BE-IN-CONS-LEMMA1)
                               (:REWRITE
                                ACL2::TRUE-LIST-LISTP-IMPLIES-ALWAYS$-TRUE-LISTP)
                               (:DEFINITION FALIST-CONSISTENT))))))

(defthm return-val-of-rp-rw-rule-aux-valid-rule
  (implies (and (rule-list-syntaxp rules-for-term)
                (mv-nth 0 (rp-rw-rule-aux term rules-for-term context iff-flg state)))
           (rule-syntaxp (mv-nth 0 (rp-rw-rule-aux term rules-for-term
                                                   context iff-flg state))))
  :hints (("Goal"
           :in-theory (disable (:DEFINITION LEN)
; Obsolete (see Matt K. comment above):
;                              (:REWRITE SHOULD-TERM-BE-IN-CONS-LEMMA1)
                               (:REWRITE RP-EQUAL2-BINDINGS-1TO1-CONSP)
                               (:REWRITE SHOULD-TERM-BE-IN-CONS-LEMMA4)
                               (:REWRITE DEFAULT-<-1)
                               (:DEFINITION SYMBOL-LISTP)
                               (:TYPE-PRESCRIPTION INCLUDE-FNC)
                               (:REWRITE SHOULD-TERM-BE-IN-CONS-LEMMA2)
                               (:TYPE-PRESCRIPTION RP-TERMP)
                               (:TYPE-PRESCRIPTION SUBSETP-EQUAL)
                               (:REWRITE
                                RP-TERM-LISTP-IS-TRUE-LISTP)
                               (:DEFINITION RP-MATCH-LHS)
                               (:DEFINITION RP-DOES-LHS-MATCH)
                               (:META ACL2::MV-NTH-CONS-META)
                               (:TYPE-PRESCRIPTION RP-DOES-LHS-MATCH)
                               (:TYPE-PRESCRIPTION PUT-TERM-IN-CONS$INLINE)
                               (:DEFINITION TRUE-LISTP)
                               (:DEFINITION GET-VARS)
                               (:DEFINITION GET-VARS1)
                               RULE-SYNTAXP
                               VALID-RULESP-IMPLIES-RULE-LIST-SYNTAXP
                               (:DEFINITION MEMBER-EQUAL)
                               (:TYPE-PRESCRIPTION MEMBER-EQUAL)
                               (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                               (:TYPE-PRESCRIPTION SHOULD-TERM-BE-IN-CONS$INLINE)))))

(defthm return-val-of-rp-rw-rule-aux-rest-rules
  (implies (rule-list-syntaxp rules-for-term)
           (rule-list-syntaxp (mv-nth 1
                                      (rp-rw-rule-aux term rules-for-term
                                                      context iff-flg state))))
  :hints (("goal" :in-theory (e/d (rp-rw-rule-aux)
                                  (rule-syntaxp
                                   VALID-RULESP-IMPLIES-RULE-LIST-SYNTAXP
                                   VALID-RULESP)))))

(encapsulate
  nil

  (local
   (defthm lemma1
     (implies (and (rule-syntaxp rule)
                   (rp-rule-rwp rule))
              (not (include-fnc (rp-lhs rule) 'if)))
     :hints (("Goal"
              :in-theory (e/d (rule-syntaxp) ())))))

  (local
   (defthm lemma2
     (implies (and (consp rules-for-term)
                   (rp-rule-rw-listp rules-for-term)
                   (rule-list-syntaxp rules-for-term))
              (NOT (INCLUDE-FNC (RP-LHS (CAR RULES-FOR-TERM))
                                'IF)))
     :hints (("Goal"
              :in-theory (e/d (rule-list-syntaxp) ())))))

  (defthm valid-sc-bindings-rp-rw-rule-aux
    (mv-let (rule rules-rest bindings rp-context)
      (rp-rw-rule-aux term rules-for-term context iff-flg state)
      (declare (ignorable rules-rest rp-context))
      (implies (and rule
                    (rule-list-syntaxp rules-for-term)
                    (rp-rule-rwp rule)
                    (valid-sc term a))
               (valid-sc-bindings bindings a)))
    :hints (("Goal"
             :in-theory (e/d (RP-MATCH-LHS-RETURNS-VALID-SC-BINDINGS
                              rp-rw-rule-aux)
                             (VALID-SC-BINDINGS
                              (:REWRITE
                               VALID-RULESP-IMPLIES-RULE-LIST-SYNTAXP)
                              (:DEFINITION VALID-RULESP)
                              (:DEFINITION VALID-RULEP)
                              (:DEFINITION VALID-RULEP-SK)
                              (:DEFINITION VALID-RULEP-SK-BODY)
                              (:DEFINITION VALID-SC)
                              RP-DOES-LHS-MATCH
                              rule-syntaxp))))))

(local
 (defthm consp-rule-syntaxp
   ;; not used !!!!!!!!!!!!!!!!!!!
   (implies (rule-syntaxp (mv-nth 0 (rp-rw-rule-aux term rules-for-term
                                                    context iff-flg state)))
            (consp (mv-nth 0 (rp-rw-rule-aux term rules-for-term
                                             context iff-flg state))))
   :hints (("Goal"
            :in-theory (e/d (rule-syntaxp)
                            (rp-rw-rule-aux))))))

#|(encapsulate
  nil

  (local
   (defthmd lemma0
     (implies (falist-consistent term)
              (quotep (cadr term)))))

#|  (local
   (defthm lemma1
     (implies (and (all-falist-consistent term)
                   (not (equal (car term) 'quote)))
              (all-falist-consistent-lst (cdr term)))
     :hints (("Goal"
              :use lemma0
              :expand ((all-falist-consistent term)
                       (ALL-FALIST-CONSISTENT (CADR TERM))
                       (ALL-FALIST-CONSISTENT-LST (CDR TERM)))
              :in-theory (e/d (all-falist-consistent-lst
                               is-falist
                               all-falist-consistent)
                              (FALIST-CONSISTENT
                               ))))))||#

  (defthm-rp-match-lhs
    (defthm valid-falist-rp-match-lhs
      (implies (and (all-falist-consistent-bindings acc-bindings)
                    (all-falist-consistent term))
               (all-falist-consistent-bindings
                (mv-nth 1
                        (rp-match-lhs term rule-lhs context acc-bindings))))
      :flag rp-match-lhs)
    (defthm valid-falist-rp-match-lhs-subterms
      (implies (and (all-falist-consistent-bindings acc-bindings)
                    (all-falist-consistent-lst subterms))
               (all-falist-consistent-bindings
                (mv-nth 1
                        (rp-match-lhs-subterms subterms
                                               sublhs context acc-bindings))))
      :flag rp-match-lhs-subterms))

  (defthm valid-falist-rp-rw-rule-aux
    (implies (all-falist-consistent term)
             (all-falist-consistent-bindings
              (mv-nth 2 (rp-rw-rule-aux term rules-for-term
                                        context iff-flg state))))
    :hints (("Goal" :in-theory (e/d nil (ALL-FALIST-CONSISTENT-BINDINGS
                                         all-falist-consistent))))))||#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|(encapsulate
  nil

  (defthm-rp-match-lhs
    (defthm rp-syntaxp-bindings-rp-match-lhs
      (implies (and (rp-syntaxp-bindings acc-bindings)
                    (rp-syntaxp term)
                    (not (include-fnc rule-lhs 'rp)))
               (rp-syntaxp-bindings
                (mv-nth 1
                        (rp-match-lhs term rule-lhs context acc-bindings))))
      :flag rp-match-lhs)
    (defthm rp-syntaxp-bindings-rp-match-lhs-subterms
      (implies (and (rp-syntaxp-bindings acc-bindings)
                    (rp-syntaxp-lst subterms)
                    (not (include-fnc-subterms sublhs 'rp)))
               (rp-syntaxp-bindings
                (mv-nth 1
                        (rp-match-lhs-subterms subterms sublhs
                                               context acc-bindings))))
      :flag rp-match-lhs-subterms))

  (defthm rp-syntaxp-bindings-rp-rw-rule-aux
    (implies (and (rp-syntaxp term)
                  (rule-list-syntaxp rules-for-term))
             (rp-syntaxp-bindings
              (mv-nth 2 (rp-rw-rule-aux term rules-for-term
                                        context iff-flg state))))
    :hints (("Goal" :in-theory (e/d (rp-syntaxp-bindings-rp-match-lhs
                                     rp-rw-rule-aux
                                     valid-rulesp)
                                    (rp-syntaxp-bindings
                                     VALID-RULESP-IMPLIES-RULE-LIST-SYNTAXP))))))||#

(defthm rp-rw-rule-aux-does-not-return-rule-with-iff-flg-when-iff-flg=nil
  (implies
   (and (mv-nth 0
                (rp-rw-rule-aux term rules-for-term context nil state))
        (rp-rule-rwp (mv-nth 0
                             (rp-rw-rule-aux term rules-for-term context nil state))))
   (not (rp-iff-flag
         (mv-nth 0
                 (rp-rw-rule-aux term rules-for-term context nil state)))))
  :hints (("goal"
           :in-theory (e/d (rp-rw-rule-aux) (rp-match-lhs
                                             rp-does-lhs-match
                                             rp-iff-flag)))))

(encapsulate
  nil

  (defthm valid-sc-subterms-cdr-put-term-in-cons
    (implies (should-term-be-in-cons rule-lhs term)
             (valid-sc-subterms
              (cdr (put-term-in-cons term)) a))
    :hints (("Goal"
             :in-theory (e/d (should-term-be-in-cons
                              put-term-in-cons) ()))))

  (defthm valid-sc-subterms-context-from-rp
    (implies (and (valid-sc term a)
                  (valid-sc-subterms context a))
             (VALID-SC-SUBTERMS (CONTEXT-FROM-RP TERM CONTEXT)
                                A))
    :hints (("Goal"
             :in-theory (e/d (is-rp
                              ex-from-rp
                              context-from-rp)
                             (EX-FROM-RP-LEMMA1
                              (:DEFINITION RP-TERMP)
                              (:REWRITE CAR-OF-EX-FROM-RP-IS-NOT-RP)
                              (:REWRITE VALID-SC-CONS)
                              (:DEFINITION INCLUDE-FNC)
; Obsolete (see Matt K. comment above):
;                             (:REWRITE SHOULD-TERM-BE-IN-CONS-LEMMA1)
                              (:REWRITE VALID-SC-CADR)
                              (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                              (:TYPE-PRESCRIPTION INCLUDE-FNC)
                              (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                              (:REWRITE ACL2::O-P-O-INFP-CAR))))))

  (local
   (defthm lemma1
     (implies (and (not (equal (car term) 'if))
                   (not (equal (car term) 'rp))
                   (not (equal (car term) 'quote))
                   (valid-sc term a))
              (valid-sc-subterms (cdr term) a))
     :hints (("Goal"
              :in-theory (e/d (is-if
                               is-rp) ())))))
  (local
   (defthm lemma2
     (implies (rp-termp term)
              (NOT (EQUAL (CAR (EX-FROM-RP TERM)) 'RP)))
     :hints (("Goal"
              :in-theory (e/d (is-rp ex-from-rp) ())))))

  (defthm-rp-match-lhs
    (defthm valid-sc-rp-context-from-rp-match-lhs
      (implies
       (and (valid-sc term a)
            (rp-termp term)
            (not (include-fnc rule-lhs 'if))
            (valid-sc-subterms context a))
       (valid-sc-subterms
        (mv-nth 0 (rp-match-lhs term rule-lhs
                                context acc-bindings))
        a))
      :flag rp-match-lhs)
    (defthm valid-sc-rp-context-from-rp-match-lhs-subterms
      (implies
       (and (valid-sc-subterms subterms a)
            (rp-term-listp subterms)
            (not (include-fnc-subterms sublhs 'if))
            (valid-sc-subterms context a))
       (valid-sc-subterms
        (mv-nth 0 (rp-match-lhs-subterms subterms sublhs
                                         context acc-bindings))
        a))
      :flag rp-match-lhs-subterms)
    :hints (("Goal"
             :in-theory (e/d () ()))))

  (defthm valid-sc-subterms-of-context-rp-rw-rule-aux
    ;; valid-sc for the context returned
    (implies (and (valid-sc term a)
                  (valid-sc-subterms context a)
                  (rule-list-syntaxp rules-for-term)
                  (rp-termp term))
             (valid-sc-subterms
              (mv-nth 3
                      (rp-rw-rule-aux term rules-for-term context iff-flg state))
              a))
    :hints (("Goal"
             :in-theory (e/d (rule-syntaxp)
                             (;RULE-SYNTAXP
                              VALID-RULESP-IMPLIES-RULE-LIST-SYNTAXP
                              (:DEFINITION SUBSETP-EQUAL)
                              (:DEFINITION NO-FREE-VARIABLEP)
                              (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                              (:DEFINITION MEMBER-EQUAL)
                              (:DEFINITION TRUE-LISTP)
                              (:DEFINITION ALWAYS$)
                              (:REWRITE ACL2::PLAIN-UQI-TRUE-LIST-LISTP)
                              (:DEFINITION RP-TERMP)
                              (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                              (:REWRITE
                               ACL2::TRUE-LIST-LISTP-IMPLIES-ALWAYS$-TRUE-LISTP)
                              (:DEFINITION TRUE-LIST-LISTP)
                              (:DEFINITION ACL2::APPLY$-BADGEP)))))))

(encapsulate
  nil

  (local
   (defthm lemma1
     (implies (and (valid-sc term a)
                   (is-rp term))
              (valid-sc (caddr term) a))
     :hints (("Goal"
              :in-theory (e/d (is-rp is-if context-from-rp
                                     ex-from-rp) ())))))

  (defthm eval-and-all-context-from-rp
    (implies (and (valid-sc term a)
                  (rp-termp term)
                  (eval-and-all context a))
             (eval-and-all (context-from-rp term context) a))
    :hints (("Goal"
             :in-theory (e/d (eval-and-all
                              is-rp
                              context-from-rp)
                             (ex-from-rp-lemma1

                              (:DEFINITION ACL2::APPLY$-BADGEP)
; Obsolete (see Matt K. comment above):
;                             (:REWRITE SHOULD-TERM-BE-IN-CONS-LEMMA1)
                              (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                              (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                              (:DEFINITION RP-TERMP))))))

  (local
   (defthm lemma3
     (implies (and (not (equal (car term) 'if))
                   (not (equal (car term) 'rp))
                   (not (equal (car term) 'quote))
                   (valid-sc term a))
              (valid-sc-subterms (cdr term) a))
     :hints (("Goal"
              :in-theory (e/d (is-if
                               is-rp) ())))))

  (local
   (defthm lemma4
     (implies (rp-termp term)
              (NOT (EQUAL (CAR (EX-FROM-RP TERM)) 'RP)))
     :hints (("Goal"
              :in-theory (e/d (is-rp ex-from-rp) ())))))

  (defthm-rp-match-lhs

    (defthm rp-match-lhs-returns-valid-context
      (implies
       (and (rp-termp term)
            (rp-termp rule-lhs)
            (eval-and-all context a)
            (valid-sc term a)
            (not (include-fnc rule-lhs 'if)))
       (eval-and-all
        (rp-context-from (rp-match-lhs term rule-lhs context acc-bindings))
        a))
      :flag rp-match-lhs)

    (defthm rp-match-lhs-subterms-returns-valid-context
      (implies
       (and (rp-term-listp subterms)
            (rp-term-listp sublhs)

            (eval-and-all context a)
            (valid-sc-subterms subterms a)
            (not (include-fnc-subterms sublhs 'if)))
       (eval-and-all (rp-context-from
                      (rp-match-lhs-subterms subterms sublhs context acc-bindings))
                     a))
      :flag rp-match-lhs-subterms)
    :hints (("Goal"
             :in-theory (e/d ()
                             ((:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)

                              (:DEFINITION ACL2::APPLY$-BADGEP)
                              (:REWRITE LEMMA1)
                              (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                              (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                              (:DEFINITION TRUE-LISTP)
                              (:REWRITE VALID-SC-CONS)
                              (:REWRITE NOT-INCLUDE-RP)
; Obsolete (see Matt K. comment above):
;                             (:REWRITE SHOULD-TERM-BE-IN-CONS-LEMMA1)
                              (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                              (:REWRITE ACL2::O-P-O-INFP-CAR)
                              (:DEFINITION FALIST-CONSISTENT)
                              (:DEFINITION FALIST-CONSISTENT-AUX)
                              (:DEFINITION SUBSETP-EQUAL))))))

  (defthm rp-rw-rule-aux-returns-valid-context
    (implies (and (rp-termp term)

                  (rule-list-syntaxp rules-for-term)
                  (eval-and-all context a)
                  (valid-sc term a))
             (eval-and-all
              (mv-nth 3 (rp-rw-rule-aux term rules-for-term context iff-flg state)) a))
    :hints (("Goal" :in-theory (e/d (rule-list-syntaxp
                                     rule-syntaxp-implies)
                                    (rp-iff-flag
                                     VALID-RULESP-IMPLIES-RULE-LIST-SYNTAXP
                                     rp-lhs
                                     (:DEFINITION SUBSETP-EQUAL)
                                     (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                                     (:DEFINITION TRUE-LISTP)
                                     (:DEFINITION MEMBER-EQUAL)
                                     (:DEFINITION ALWAYS$)
                                     (:REWRITE ACL2::PLAIN-UQI-TRUE-LIST-LISTP)
                                     (:DEFINITION RP-TERMP)
                                     (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                                     (:REWRITE
                                      ACL2::TRUE-LIST-LISTP-IMPLIES-ALWAYS$-TRUE-LISTP)
                                     (:DEFINITION TRUE-LIST-LISTP)
                                     (:DEFINITION ACL2::APPLY$-BADGEP)
                                     (:DEFINITION FALIST-CONSISTENT)
                                     (:REWRITE ACL2::APPLY$-SYMBOL-ARITY-1)
                                     (:REWRITE ACL2::APPLY$-PRIMITIVE)
                                     (:META ACL2::APPLY$-PRIM-META-FN-CORRECT)
                                     (:DEFINITION FALIST-CONSISTENT-AUX)
                                     rp-does-lhs-match
                                     rp-match-lhs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm SHOULD-TERM-BE-IN-CONS-implies
  (implies (should-term-be-in-cons rule-lhs term)
           (AND (CASE-MATCH rule-lhs (('CONS & &) T)
                  (& NIL))
                (QUOTEP TERM)
                (CONSP (UNQUOTE TERM))
                (IS-CONS RULE-LHS)))
  :hints (("Goal"
           :in-theory (e/d (should-term-be-in-cons
                            is-cons
                            is-quoted-pair) ())))
  :rule-classes :forward-chaining)

(encapsulate
  nil

  (defthm-all-vars-bound
    (defthm all-vars-bound-of-bigger
      (implies (all-vars-bound term acc-bindings)
               (all-vars-bound term (cons (cons x y)
                                          acc-bindings)))
      :flag all-vars-bound)
    (defthm all-vars-bound-of-bigger-subterms
      (implies (all-vars-bound-subterms subterms acc-bindings)
               (all-vars-bound-subterms subterms (cons (cons x y)
                                                       acc-bindings)))
      :flag all-vars-bound-subterms))

  (defthm-rp-match-lhs
    (defthm RP-MATCH-LHS-ALL-VARS-BOUND-lemma
      (implies
       (and (all-vars-bound RULE-LHS1 ACC-BINDINGS)
            (MV-NTH 2
                    (RP-MATCH-LHS term
                                  rule-lhs
                                  CONTEXT ACC-BINDINGS)))
       (ALL-VARS-BOUND RULE-LHS1
                       (MV-NTH 1
                               (RP-MATCH-LHS term
                                             rule-lhs
                                             CONTEXT ACC-BINDINGS))))
      :flag rp-match-lhs)

    (defthm RP-MATCH-LHS-ALL-VARS-BOUND-subterms-lemma
      (implies
       (and (all-vars-bound RULE-LHS1 ACC-BINDINGS)
            (MV-NTH 2
                    (rp-match-lhs-subterms
                     subterms
                     sublhs
                     CONTEXT ACC-BINDINGS)))
       (ALL-VARS-BOUND
        RULE-LHS1
        (MV-NTH 1
                (rp-match-lhs-subterms subterms
                                       sublhs
                                       CONTEXT ACC-BINDINGS))))
      :flag rp-match-lhs-subterms))

  (defthm-rp-match-lhs
    (defthm rp-match-lhs-binds-all
      (implies (and (mv-nth 2 (rp-match-lhs term rule-lhs
                                            context acc-bindings))
                    (rp-termp rule-lhs))
               (all-vars-bound
                rule-lhs
                (mv-nth 1 (rp-match-lhs term rule-lhs
                                        context acc-bindings))))
      :flag rp-match-lhs)
    (defthm rp-match-lhs-binds-all-subterms
      (implies (and (mv-nth 2 (rp-match-lhs-subterms subterms
                                                     sublhs
                                                     context acc-bindings))
                    (rp-term-listp sublhs))
               (all-vars-bound-subterms
                sublhs
                (mv-nth 1 (rp-match-lhs-subterms subterms sublhs
                                                 context acc-bindings))))
      :flag rp-match-lhs-subterms)))

(encapsulate
  nil
  (local
   (in-theory (e/d (bind-bindings-aux
                    put-term-in-cons)
                   (
; Obsolete (see Matt K. comment above):
;                   (:REWRITE SHOULD-TERM-BE-IN-CONS-LEMMA1)
                    (:REWRITE ACL2::O-P-O-INFP-CAR)
                    (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                    (:DEFINITION ACL2::APPLY$-BADGEP)
                    (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                    (:DEFINITION SUBSETP-EQUAL)
                    (:DEFINITION MEMBER-EQUAL)
                    (:REWRITE EX-FROM-SYNP-LEMMA1)))))

  (local
   (defthm lemma1
     (implies (EQUAL (CAR (EX-FROM-RP TERM)) 'QUOTE)
              (EQUAL (CADR (EX-FROM-RP TERM))
                     (RP-EVLt TERM A)))
     :hints (("Goal"
              :in-theory (e/d (is-rp
                               ex-from-rp)
                              (EX-FROM-RP-LEMMA1))))))

  (local
   (defthm lemma2
     (implies (should-term-be-in-cons rule-lhs (EX-FROM-RP TERM))
              (EQUAL (CAR (EX-FROM-RP TERM)) 'QUOTE))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :in-theory (e/d (should-term-be-in-cons
                               is-quoted-pair
                               quotep)
                              (ex-from-rp))))))

  (local
   (defthmd lemma3-lemma1
     (implies (syntaxp (equal term 'term))
              (equal (rp-evlt term a)
                     (rp-evlt (ex-from-falist term) a)))
     :hints (("Goal"
              :expand ((ex-from-falist term))
              :do-not-induct t
              :in-theory (e/d () ())))))

  (local
   (defthmd lemma3-lemma2
     (implies (syntaxp (equal term '(ex-from-falist term)))
              (equal (rp-evlt term a)
                     (rp-evlt (ex-from-rp term) a)))
     :hints (("Goal"))))

  (local
   (defthmd lemma3-lemma3
     (implies (and (EQUAL (RP-EVL-LST x A1)
                          (RP-EVL-LST y A2)))
              (equal (EQUAL
                      (RP-EVL (CADR x)
                              A1)
                      (RP-EVL (CADR y)
                              A2))
                     t))
     :hints (("Goal"))))

  (local
   (defthmd rp-trans-opener
     (and (implies (is-falist term)
                   (equal (rp-trans term)
                          (RP-TRANS (CADDR TERM))))
          (implies (ATOM TERM)
                   (equal (rp-trans term)
                          term))
          (implies (QUOTEP TERM)
                   (equal (rp-trans term)
                          term))
          (implies (AND (EQUAL (CAR TERM) 'LIST)
                        (CONSP (CDR TERM)))
                   (equal (rp-trans term)
                          (TRANS-LIST (RP-TRANS-LST (CDR TERM))))))))

  (local
   (defthm is-falist-fc
     (implies (is-falist term)
              (CASE-MATCH TERM (('FALIST & &) T)
                (& NIL)))
     :rule-classes :forward-chaining))

  (local
   (defthm lemma3-lemma4
     (implies (IS-FALIST RULE-LHS)
              (equal (RP-TRANS-LST (CDR RULE-LHS))
                     (list (RP-TRANS (CAdR RULE-LHS))
                           (RP-TRANS (CAddR RULE-LHS)))))))

  (local
   (defthmd lemma3-lemma5
     (implies (and (equal (rp-evlt-lst (cdr x) a1)
                          (rp-evlt-lst (cdr y) a2))
                   (equal (car x) (car y))
                   (consp x)
                   (consp y)
                   (rp-termp x)
                   (rp-termp y))
              (iff (is-falist x)
                   (is-falist y)))
     :hints (("Goal"
              :expand ((RP-TRANS-LST (CDR Y))
                       (RP-TRANS-LST (CDDR Y))
                       (RP-TRANS-LST (CDDDR Y)))
              :do-not-induct t
              :in-theory (e/d () ())))))

  (local
   (defthm lemma3
     (implies (and (equal (car (ex-from-rp (ex-from-falist term)))
                          (car rule-lhs))
                   (consp rule-lhs)
                   (consp (ex-from-rp (ex-from-falist term)))
                   (rp-termp term)
                   (rp-termp rule-lhs)
                   (not (equal (car rule-lhs) 'quote))
                   (equal (rp-evlt-lst (cdr rule-lhs) a1)
                          (rp-evlt-lst (cdr (ex-from-rp (ex-from-falist term))) a2)))
              (equal (equal (rp-evlt rule-lhs a1)
                            (rp-evlt term a2))
                     t))
     :otf-flg t
     :hints (("goal"
              :do-not-induct t
              :use ((:instance lemma3-lemma5
                               (x RULE-LHS)
                               (y (EX-FROM-RP (EX-FROM-FALIST TERM)))))
              :Expand ((RP-TRANS rule-lhs)
                       (RP-TRANS (EX-FROM-RP (EX-FROM-FALIST TERM))))
              :in-theory (e/d (rp-evl-of-fncall-args
                               lemma3-lemma1
                               lemma3-lemma2
                               rp-trans-opener
                               lemma3-lemma3
                               rp-trans
                               rp-trans-lst)
                              (evl-of-extract-from-rp
                               rp-evlt-of-ex-from-rp
                               ex-from-falist
                               (:TYPE-PRESCRIPTION IS-FALIST)
                               trans-list
                               is-falist
                               ex-from-rp))))))

  (local
   (defthm lemma4
     (implies (should-term-be-in-cons rule-lhs (ex-from-rp term))
              (consp (rp-evlt term a)))
     :hints (("goal"
              :use (:instance lemma3-lemma1)
              :in-theory (e/d (should-term-be-in-cons)
                              (evl-of-extract-from-rp))))))

  (local
   (defthm lemma4-v2
     (implies (should-term-be-in-cons rule-lhs (ex-from-rp (ex-from-falist term)))
              (consp (rp-evlt term a)))
     :hints (("goal"
              :use (:instance lemma3-lemma1)
              :in-theory (e/d (should-term-be-in-cons)
                              (evl-of-extract-from-rp))))))

  (defthm-all-vars-bound
    (defthm all-vars-bound-bind-bindings-aux
      (implies (all-vars-bound term acc-bindings)
               (all-vars-bound term
                               (bind-bindings-aux acc-bindings a)))
      :flag all-vars-bound)
    (defthm all-vars-bound-bind-bindings-aux-subterms
      (implies (all-vars-bound-subterms subterms acc-bindings)
               (all-vars-bound-subterms subterms
                                        (bind-bindings-aux acc-bindings a)))
      :flag all-vars-bound-subterms))

  (defthm-all-vars-bound
    (defthm all-vars-bound-BIND-BINDINGS
      (implies (all-vars-bound term acc-bindings)
               (all-vars-bound term
                               (BIND-BINDINGS ACC-BINDINGS A)))
      :flag all-vars-bound)
    (defthm all-vars-bound-BIND-BINDINGS-subterms
      (implies (all-vars-bound-subterms subterms acc-bindings)
               (all-vars-bound-subterms subterms
                                        (BIND-BINDINGS ACC-BINDINGS A)))
      :flag all-vars-bound-subterms))

  (local
   (defthm lemma101
     (implies (ALISTP ACC-BINDINGS)
              (equal (CONSP
                      (ASSOC-EQUAL RULE-LHS
                                   (BIND-BINDINGS-AUX ACC-BINDINGS A)))
                     (CONSP (ASSOC-EQUAL RULE-LHS ACC-BINDINGS))))))

  (local
   (defthm-all-vars-bound
     (defthm all-vars-bound-rp-trans-bindings
       (implies (all-vars-bound term acc-bindings)
                (all-vars-bound term (rp-trans-bindings acc-bindings)))
       :flag all-vars-bound)
     (defthm all-vars-bound-subtermsrp-trans-bindings
       (implies (all-vars-bound-subterms subterms acc-bindings)
                (all-vars-bound-subterms subterms (rp-trans-bindings acc-bindings)))
       :flag all-vars-bound-subterms)))

  (local
   (defthm-all-vars-bound
     (defthm lemma5-lemma1-term
       (implies
        (and
         (not (consp (assoc-equal rule-lhs acc-bindings)))
         (all-vars-bound term acc-bindings)
         (rp-termp term)
         (symbolp rule-lhs)
         rule-lhs)
        (equal
         (equal
          (rp-evl term
                  (cons (cons rule-lhs val)
                        (append acc-bindings a)))
          (rp-evl term
                  (append acc-bindings a)))
         t))
       :flag all-vars-bound)
     (defthm lemma5-lemma1-subterms
       (implies
        (and
         (not (consp (assoc-equal rule-lhs acc-bindings)))
         #|(equal (rp-evl-lst subterms
         (append acc-bindings a))
         rp-evl-term1-a-subterms)||#
         (all-vars-bound-subterms subterms acc-bindings)
         (rp-term-listp subterms)
         (symbolp rule-lhs)
         rule-lhs)
        (equal
         (equal
          (rp-evl-lst subterms
                      (cons (cons rule-lhs val)
                            (append acc-bindings a)))
          (rp-evl-lst subterms
                      (append acc-bindings a)))
         t))
       :flag all-vars-bound-subterms)
     :hints (("Goal"
              :in-theory (e/d (rp-evl-of-fncall-args) ())))))

  (defthm lemma5-lemma1
    (implies
     (and
      (not (consp (assoc-equal rule-lhs acc-bindings)))
      (equal (rp-evl term
                     (append acc-bindings a))
             rp-evl-term1-a)
      (all-vars-bound term acc-bindings)
      (rp-termp term)
      (symbolp rule-lhs)
      rule-lhs)
     (equal
      (equal
       (rp-evl term
               (cons (cons rule-lhs val)
                     (append acc-bindings a)))
       rp-evl-term1-a)
      t)))

  (local
   (defthm lemma5-lemma2
     (implies (alistp acc-bindings)
              (iff (CONSP (ASSOC-EQUAL RULE-LHS
                                       (BIND-BINDINGS-AUX acc-bindings
                                                          A)))
                   (CONSP (ASSOC-EQUAL RULE-LHS ACC-BINDINGS))))))

  (local
   (defthm lemma5-lemma3
     (implies (alistp acc-bindings)
              (iff (CONSP (ASSOC-EQUAL RULE-LHS
                                       (RP-TRANS-BINDINGS ACC-BINDINGS)))
                   (CONSP (ASSOC-EQUAL RULE-LHS ACC-BINDINGS))))))

  (local
   (defthm-rp-match-lhs
     (defthm lemma5-term
       (implies
        (and (equal (rp-evl rule-lhs1 (bind-bindings (rp-trans-bindings acc-bindings) a))
                    (rp-evlt term1 a))
             (all-vars-bound rule-lhs1 acc-bindings)
             (rp-termp rule-lhs1)
             (rp-termp term)
             (rp-termp rule-lhs)
             (bindings-alistp acc-bindings)
             (mv-nth 2 (rp-match-lhs term
                                     rule-lhs
                                     context
                                     acc-bindings)))
        (equal (equal (rp-evl
                       rule-lhs1
                       (bind-bindings
                        (rp-trans-bindings
                         (mv-nth 1 (rp-match-lhs term
                                                 rule-lhs
                                                 context
                                                 acc-bindings)))
                        a))
                      (rp-evlt term1 a))
               t))
       :flag rp-match-lhs)

     (defthm lemma5-subterms
       (implies
        (and (equal (rp-evl rule-lhs1 (bind-bindings (rp-trans-bindings acc-bindings) a))
                    (rp-evlt term1 a))
             (bindings-alistp acc-bindings)
             (rp-termp rule-lhs1)
             (rp-term-listp subterms)
             (rp-term-listp sublhs)
             (all-vars-bound rule-lhs1 acc-bindings)
             (mv-nth 2 (rp-match-lhs-subterms subterms
                                              sublhs
                                              context
                                              acc-bindings)))
        (equal (equal (rp-evl
                       rule-lhs1
                       (bind-bindings
                        (rp-trans-bindings
                         (mv-nth 1 (rp-match-lhs-subterms subterms
                                                          sublhs
                                                          context
                                                          acc-bindings)))
                        a))
                      (rp-evlt term1 a))
               t))
       :flag rp-match-lhs-subterms)))

  (local
   (defthmd rp-evlt-of-ex-from-falist-reverse
     (implies (syntaxp (equal term 'term))
              (EQUAL  (RP-EVL (RP-TRANS TERM) A)
                      (RP-EVL (RP-TRANS (EX-FROM-FALIST TERM))
                              A)))
     :hints (("Goal"
              :in-theory (e/d (ex-from-falist) ())))))

  (local
   (defthmd rp-evlt-of-ex-from-falist
     (implies t
              (EQUAL        (RP-EVL (RP-TRANS (EX-FROM-FALIST TERM))
                                    A)
                            (RP-EVL (RP-TRANS TERM) A)))
     :hints (("Goal"
              :in-theory (e/d (ex-from-falist) ())))))

  (local
   (defthmd rp-evlt-of-ex-from-rp-reverse
     (implies (syntaxp (equal term '(EX-FROM-FALIST TERM)))
              (EQUAL (RP-EVL (RP-TRANS TERM) A)
                     (RP-EVL (RP-TRANS (EX-FROM-RP TERM)) A)))
     :hints (("Goal"
              :in-theory (e/d (ex-from-rp
                               is-rp) ())))))

  (local
   (defthmd rp-evl-of-ex-from-rp-ex-from-falist-reverse
     (implies (syntaxp (equal term 'term))
              (equal (rp-evl term a)
                     (rp-evl (ex-from-rp (ex-from-falist term)) a)))))


  (local
   (defthm lemma6-lemma1
     (implies (and (EQUAL 'FALIST (CAR RULE-LHS))
                   (RP-TERMP RULE-LHS))
              (equal (rp-evl rule-lhs a1)
                     (rp-evl (caddr rule-lhs) a1)))))

  (local
   (defthm lemma6-lemma2
     (implies (and (EQUAL 'FALIST (CAR RULE-LHS))
                   (RP-TERMP RULE-LHS))
              (is-falist rule-lhs))))

  (local
   (defthmd rp-trans-opener-2
     (implies (and (consp x)
                   (not (equal (car x) 'quote))
                   (not (equal (car x) 'list))
                   (not (is-falist x)))
              (equal (rp-trans x)
                     (CONS (CAR x)
                           (RP-TRANS-LST (CDR x)))))
     :hints (("Goal"
              :expand (rp-trans x)
              :do-not-induct t
              :in-theory (e/d () ())))))

  (local
   (defthm lemma6-lemma3
     (implies (and (equal (car (ex-from-rp (ex-from-falist term)))
                          (car rule-lhs))
                   (not (include-fnc rule-lhs 'list)))
              (not (equal (car (ex-from-rp (ex-from-falist term)))
                          'list)))
     :rule-classes :forward-chaining))

  (local
   (defthm lemma6
     (implies
      (and (equal (car (ex-from-rp (ex-from-falist term)))
                  (car rule-lhs))
           (not (include-fnc rule-lhs 'list))
           (rp-termp rule-lhs)
           (rp-termp term)
           (not (equal (car rule-lhs) 'quote))
           (consp rule-lhs)
           (equal (rp-evl-lst (cdr rule-lhs) a1)
                  (rp-evl-lst (rp-trans-lst (cdr (ex-from-rp (ex-from-falist term))))
                              a2)))
      (equal
       (rp-evl rule-lhs a1)
       (rp-evl (rp-trans term) a2)))
     :otf-flg t
     :hints (("Goal"
              :do-not-induct t
              :use ((:instance rp-trans-opener-2
                               (x (ex-from-rp (ex-from-falist term)))))
              :cases ((is-falist rule-lhs)
                      (is-falist (EX-FROM-RP (EX-FROM-FALIST TERM))))
              :in-theory (e/d (rp-evlt-of-ex-from-rp-reverse
                               rp-evlt-of-ex-from-falist-reverse
                               rp-evl-of-ex-from-rp-ex-from-falist-reverse
                               rp-evl-of-fncall-args
                               rp-trans-opener
;rp-trans-opener-2
                               )
                              (rp-evlt-of-ex-from-rp
                               is-falist
                               include-fnc
                               rp-trans
                               rp-termp
                               RP-EVL-OF-EX-FROM-FALIST
                               EVL-OF-EXTRACT-FROM-RP))))))

  (defthm-rp-match-lhs

    (defthm rp-match-lhs-returns-valid-bindings-lemma
      (mv-let (rp-context bindings valid-bindings)
        (rp-match-lhs term rule-lhs context acc-bindings)
        (declare (ignorable rp-context))
        (implies (and valid-bindings
                      (bindings-alistp acc-bindings)
                      (not (include-fnc rule-lhs 'rp))
                      (not (include-fnc rule-lhs 'list))
                      (alistp a)
                      (not (include-fnc rule-lhs 'synp))
                      (rp-termp rule-lhs)
                      (rp-termp term))
                 (equal (rp-evlt (rp-apply-bindings rule-lhs bindings) a)
                        (rp-evlt term a))))
      :flag rp-match-lhs)

    (defthm rp-match-lhs-subterms-returns-valid-bindings-lemma
      (mv-let (rp-context bindings valid-bindings)
        (rp-match-lhs-subterms subterms sublhs context acc-bindings)
        (declare (ignorable rp-context))
        (implies (and valid-bindings
                      (alistp a)
                      (not (include-fnc-subterms sublhs 'rp))
                      (not (include-fnc-subterms sublhs 'list))
                      (not (include-fnc-subterms sublhs 'synp))
                      (bindings-alistp acc-bindings)
                      (rp-term-listp sublhs)
                      (rp-term-listp subterms))
                 (equal (rp-evlt-lst (rp-apply-bindings-subterms sublhs
                                                                 bindings)
                                     a)
                        (rp-evlt-lst subterms a))))
      :flag rp-match-lhs-subterms)
    :otf-flg t
    :hints (("Goal"
;:expand (RP-TRANS (EX-FROM-RP (EX-FROM-FALIST TERM)))
             :do-not-induct t
             :in-theory (e/d (rp-evlt-of-ex-from-falist)
                             (RP-TRANS-LST-OF-RP-APPLY-BINDINGS-SUBTERMS
                              rp-evlt-of-ex-from-rp))))))

(local
 (defthm rp-match-lhs-returns-valid-bindings-lemma-2
   (mv-let (rp-context bindings valid-bindings)
     (rp-match-lhs term rule-lhs context acc-bindings)
     (declare (ignorable rp-context))
     (implies (and valid-bindings
                   (bindings-alistp acc-bindings)
                   (not (include-fnc rule-lhs 'rp))
                   (not (include-fnc rule-lhs 'list))
                   (alistp a)
                   (not (include-fnc rule-lhs 'synp))
                   (rp-termp rule-lhs)
                   (rp-termp term))
              (equal (rp-evl (rp-apply-bindings rule-lhs (rp-trans-bindings bindings)) a)
                     (rp-evlt term a))))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance rp-match-lhs-returns-valid-bindings-lemma))
            :in-theory (e/d () (rp-match-lhs-returns-valid-bindings-lemma))))))

(encapsulate
  nil

  (defthm rp-rw-rule-aux-returns-valid-bindings
    (mv-let (rule rules-rest bindings rp-context)
      (rp-rw-rule-aux term rules-for-term context iff-flg state)
      (declare (ignorable rules-rest rp-context))
      (implies (and rule
                    (alistp a)
                    (rule-list-syntaxp rules-for-term)
                    (rp-rule-rwp rule)
                    (rp-termp term))
               (and (equal (rp-evl (rp-apply-bindings (rp-lhs rule)
                                                      (rp-trans-bindings bindings))
                                   a)
                           (rp-evlt term a))
                    (equal (rp-evlt (rp-apply-bindings (rp-lhs rule) bindings)
                                    a)
                           (rp-evlt term a)))))
    :hints (("Goal"
             :induct (rp-rw-rule-aux term rules-for-term context iff-flg state)
             :do-not-induct t
             :in-theory (e/d (rule-list-syntaxp
                              rule-syntaxp-implies)
                             (rp-iff-flag
                              rp-equal2-is-symmetric
                              no-free-variablep
                              VALID-RULESP-IMPLIES-RULE-LIST-SYNTAXP
; Obsolete (see Matt K. comment above):
;                             SHOULD-TERM-BE-IN-CONS-LEMMA1
                              INCLUDE-FNC
                              rule-syntaxp
                              weak-custom-rewrite-rule-p
                              get-vars
                              rp-lhs
                              rp-does-lhs-match
                              rp-match-lhs)))))

  (defthm rp-rw-rule-aux-returns-valid-rulep
    (mv-let (rule rules-rest bindings rp-context)
      (rp-rw-rule-aux term rules-for-term context iff-flg state)
      (declare (ignorable bindings rp-context))
      (implies (and rule
                    (valid-rulesp rules-for-term))
               (and (valid-rulep rule)
                    (valid-rulesp rules-rest))))
    :hints (("Goal" :in-theory (disable VALID-RULEP
                                        rp-does-lhs-match
                                        rp-match-lhs)))))
