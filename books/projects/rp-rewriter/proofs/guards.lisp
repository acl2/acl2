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
(local (include-book "rp-rw-lemmas"))
(local (include-book "rp-correct"))

(encapsulate
  nil
  (local
   (defthm lemma1
     (IMPLIES (AND (RP-TERMP TERM2)
                   (CONSP (EX-FROM-RP TERM2)))
              (SYMBOLP (CAR (EX-FROM-RP TERM2))))
     :hints (("Goal"
              :in-theory (e/d (is-rp
                               ex-from-rp) ())))))

  (local
   (defthm lemma2
     (IMPLIES (AND (RP-TERMP TERM2)
                   (CONSP (EX-FROM-RP-LOOSE TERM2)))
              (SYMBOLP (CAR (EX-FROM-RP-LOOSE TERM2))))
     :hints (("Goal"
              :in-theory (e/d (is-rp-loose
                               ex-from-rp-loose) ())))))

  (verify-guards rp-equal-cnt)
  (verify-guards rp-equal)
  (verify-guards rp-equal-loose))

(verify-guards rp-check-context)

(verify-guards rp-rw-relieve-synp-wrap)

(encapsulate
  nil
  ;; guard for rp-match-lhs
  (local
   (defthm guard-lemma1
     (implies (and (bindings-alistp acc-bindings)
                   (consp (assoc-equal rule-lhs acc-bindings))
                   (not (consp rule-lhs)))
              (rp-termp (cdr (assoc-equal rule-lhs acc-bindings))))))

  (local
   (defthm guard-lemma2
     (implies (rp-termp term)
              (ex-from-rp term))
     :hints (("goal" :in-theory (enable ex-from-rp is-rp)))))

  (local
   (defthm guard-lemma3
     (implies (and (rp-termp term)
                   (consp (ex-from-rp term))
                   (equal (car (ex-from-rp term)) 'quote))
              (consp (cdr (ex-from-rp term))))
     :hints (("goal" :in-theory (enable ex-from-rp is-rp)))))

  (local
   (defthm guard-lemma4
     (implies (and (rp-termp term)
                   (consp (ex-from-rp term)))
              (symbolp (car (ex-from-rp term))))
     :hints (("goal" :in-theory (enable ex-from-rp is-rp)))))

  (local
   (defthm guard-lemma5
     (implies (and (rp-termp term)
                   (equal (car (ex-from-rp term)) 'quote)
                   (consp (ex-from-rp term)))
              (not (cddr (ex-from-rp term))))))

  (verify-guards rp-match-lhs))

(verify-guards rp-rw-rule-aux
  :hints (("Goal"
           :in-theory (e/d (RULE-SYNTAXP)
                           (EX-FROM-RP-LEMMA1
                            FALIST-CONSISTENT
                            NO-FREE-VARIABLEP
                            (:REWRITE
                             VALID-RULESP-IMPLIES-RULE-LIST-SYNTAXP)
                            (:DEFINITION VALID-RULESP)
                            (:DEFINITION VALID-RULEP)
                            (:DEFINITION VALID-RULEP-SK)
                            (:DEFINITION VALID-RULEP-SK-BODY)
                            (:DEFINITION VALID-SC)
                            (:REWRITE VALID-RULEP-IMPLIES-VALID-SC))))))

(verify-guards rp-rw-meta-rule)

(verify-guards rp-rw-meta-rules
  :hints (("Goal"
           :in-theory (e/d (WEAK-RP-META-RULE-RECS-P
                            RP-META-VALID-SYNTAX-LISTP)
                           (RP-META-TRIG-FNC)))))

(local
 (defthm rp-term-listp-lemma1
   (implies (and (consp subterms)
                 (rp-term-listp subterms))
            (and (rp-term-listp (cdr subterms))
                 (rp-termp (car subterms))))
   :hints (("goal" :in-theory (enable rp-termp rp-term-listp)))))

(local
 (defthm rp-term-listp-lemma2
   (implies (and ;(consp term)
             (not (equal (car term) 'quote))
             (rp-termp term))
            (rp-term-listp (cdr term)))
   :hints (("goal"
            :expand (rp-termp term)
            :in-theory (enable quotep rp-termp rp-term-listp)))))

#|(local
 (defthm pseudo-termp-lemma3
   (implies (and (rp-term-listp subterms)
                 (not (equal sym 'quote))
                 (symbolp sym)
                 sym)
            (rp-termp (cons sym subterms)))
   :hints (("goal"
            :expand (rp-termp (cons sym subterms))
            :in-theory (enable
                        (:type-prescription rp-termp)
                        quotep rp-termp rp-term-listp)))))||#

#|(local
 (defthm pseudo-termp-lemma3-5
   (implies (and (rp-term-listp subterms)
                 (not (equal (car term) 'quote))
                 (rp-termp term)
                 (car term))
            (rp-termp (cons (car term) subterms)))
   :hints (("goal"
            :expand (rp-termp (cons sym subterms))
            :in-theory (enable
                        (:type-prescription rp-termp)
                        quotep rp-termp rp-term-listp)))))||#

(local
 (defthm not-quotep-implies
   (implies (and (not (quotep x))
                 (consp x))
            (not (equal (car x) 'quote)))
   :hints (("goal" :in-theory (enable quotep)))))

(local
 (defthm pseudo-termp-lemma4
   (implies (and (rp-termp term)
                 (consp term))
            (symbolp (car term)))
   :hints (("goal"
;:expand (rp-termp (cons sym subterms))
            :in-theory (enable
                        (:type-prescription rp-termp)
                        quotep rp-termp rp-term-listp)))))

#|(defthm not-meta-changed-flg-implies
  (implies (not (mv-nth 0 (rp-rw-apply-meta term meta-rules state)))
           (equal (mv-nth 1 (rp-rw-apply-meta term meta-rules state))
                  term))
  :hints (("goal" :in-theory (enable rp-rw-apply-meta))))||#

(defthm not-meta-changed-flg-implies-rp-rw-meta-rules
  (implies (not (mv-nth 0 (rp-rw-meta-rules term meta-rules rp-state state)))
           (equal (mv-nth 1 (rp-rw-meta-rules term meta-rules rp-state state))
                  term))
  :hints (("goal" :in-theory (enable rp-rw-meta-rules))))

(defthm rule-list-syntaxp-rp-get-rules-for-term
  (implies (rules-alistp rules-alist)
           (rule-list-syntaxp (rp-get-rules-for-term fn-name rules-alist)))
  :hints (("goal"
           :in-theory (e/d (hons-get
                            rules-alistp)
                           (RULE-LIST-SYNTAXP
                            (:REWRITE
                             VALID-RULESP-IMPLIES-RULE-LIST-SYNTAXP)
                            (:DEFINITION VALID-RULESP)
                            (:DEFINITION VALID-RULEP)
                            (:DEFINITION VALID-RULEP-SK)
                            (:DEFINITION VALID-RULEP-SK-BODY)
                            (:DEFINITION VALID-SC)
                            (:DEFINITION RP-TERMP))))))

(local
 (defthm dont-rw-if-fix-type
   (let ((res (dont-rw-if-fix dont-rw)))
     (and (consp res)
          (consp (cdr res))
          (consp (cddr res))
          (consp (cdddr res))
          (equal (cddddr res) nil)))
   :hints (("Goal"
            :in-theory (e/d (dont-rw-if-fix) ())))))

(local
 (in-theory (enable
             RP-TERMP
             rp-term-listp
             rule-syntaxp-implies)))

(local
 (in-theory (disable rule-syntaxp weak-custom-rewrite-rule-p
                     rp-hyp
                     rp-lhs
                     dumb-negate-lit2
                     context-syntaxp
                     rp-term-listp
                     ;;rp-termp
                     symbol-listp
                     hons-get
                     state-p
                     true-listp
;rp-get-rules-for-term
                     not
                     rp-rhs
                     is-nonnil-fix
                     rules-alistp
; rp-stat-p
                     nonnil-p
                     quotep
                     rp-rw-rule-aux)))

(local
 (defthm pseudo-termp-listp-lemma4
   (implies (and (rp-term-listp subterms)
                 (consp subterms)
                 (rp-term-listp subterms2))
            (rp-term-listp
             (cons (car subterms) subterms2)))
   :hints (("goal" :in-theory (enable rp-term-listp
                                      rp-termp)))))

(local
 (defthm pseudo-termp-listp-lemma5
   (implies (and (rp-termp term)
                 (rp-term-listp subterms2))
            (rp-term-listp
             (cons term subterms2)))
   :hints (("goal" :in-theory (enable rp-term-listp
                                      rp-termp)))))

(defthm rp-ex-counterpart-returns-rp-statp
  (implies (rp-statep rp-state)
           (rp-statep (mv-nth 1
                              (rp-ex-counterpart term exc-rules rp-state
                                                 state))))
  :hints (("Goal"
           :in-theory (e/d () (rp-statep)))))

(local
 (defthm lemma1
   (implies (rp-statep rp-state)
            (consp rp-state))
   :rule-classes :forward-chaining
   :hints (("goal"
            :in-theory (e/d (rp-statep) ())))))

#|(local
 (defthm lemma2
   (implies (not (mv-nth 0 (rp-rw-apply-falist-meta term)))
            (equal (mv-nth 1 (rp-rw-apply-falist-meta term))
                   term))
   :hints (("Goal"
            :in-theory (e/d (#|hons-get-rp-meta||#
                             #|FAST-ALIST-FREE-RP-META||#) ())))))||#

#|(local
 (defthm lemma3
   (implies (all-falist-consistent-lst subterms)
            (all-falist-consistent-lst (cdr subterms)))))||#

#|(local
 (defthm lemma4
   (implies (all-falist-consistent-lst subterms)
            (all-falist-consistent (car subterms)))))||#

#|(local
 (defthm lemma5
   (equal (all-falist-consistent (cons 'hide rest))
          (all-falist-consistent-lst rest))
   :hints (("goal"
            :in-theory (e/d (quotep) ())))))||#

(local
 (defthm rp-rw-of-quotep-term
   (implies (quotep term)
            (equal (equal (rp-rw term dont-rw context limit rules-alist exc-rules
                                 meta-rules iff-flg rp-state state)
                          (list term rp-state))
                   t))
   :hints (("Goal"
            :expand (rp-rw term dont-rw context limit rules-alist
                           exc-rules meta-rules iff-flg rp-state state)
            :do-not-induct t
            :in-theory (e/d (rp-ex-counterpart
                             quotep
                             rp-check-context) ())))))

(local
 (defthm lemma6
   (implies (not (equal (car term) 'quote))
            (not (quotep term)))
   :hints (("goal"
            :in-theory (e/d (quotep) ())))))

#|(local
 (defthm lemma7
   (implies (and (not (equal car-term 'falist))
                 (all-falist-consistent-lst subterms))
            (all-falist-consistent (cons car-term subterms)))))||#

(local
 (defthm lemma8
   (implies (not (equal (car
                         (MV-NTH 0
                                 (RP-EX-COUNTERPART term
                                                    EXC-RULES rp-state STATE)))
                        'quote))
            (equal (MV-NTH 0
                           (RP-EX-COUNTERPART term
                                              EXC-RULES rp-state STATE))
                   term))
   :hints (("Goal"
            :in-theory (e/d (rp-ex-counterpart) ())))))

#|(local
 (defthm lemma9
   (implies (and (RP-SYNTAXP TERM)
                 (NOT (EQUAL (CAR TERM) 'QUOTE)))
            (RP-SYNTAXP-LST (CDR TERM)))
   :hints (("Goal"
            :cases ((is-rp term))
            :in-theory (e/d (is-rp) ())))))||#

(local
 (defun induct-1 (x limit)
   (if (OR (ATOM x) (ZP LIMIT))
       x
     (cons (car x)
           (induct-1 (cdr x) (1- limit))))))

(local
 (defthm lemma10
   (equal (consp (MV-NTH
                  0
                  (RP-RW-SUBTERMS SUBTERMS DONT-RW CONTEXT
                                  LIMIT RULES-ALIST EXC-RULES meta-rules rp-state STATE)))
          (consp subterms))
   :hints (("Goal"
            :induct (induct-1 subterms limit)
            :expand (RP-RW-SUBTERMS SUBTERMS DONT-RW CONTEXT
                                    LIMIT RULES-ALIST EXC-RULES meta-rules rp-state STATE)
            :in-theory (e/d (RP-RW-SUBTERMS) (RP-RW))))))

(local
 (defthm lemma11
   (implies (and (rp-termp term)
                 (syntaxp (equal (car term) 'rp-check-context))
                 (EQUAL (CAR term) 'QUOTE))
            (consp (cdr term)))))

(local
 (defthm lemma12
   (implies (case-split (equal (car term) 'quote))
            (equal (MV-NTH 0
                           (RP-EX-COUNTERPART term
                                              EXC-RULES rp-state STATE))
                   term))
   :hints (("Goal"
            :in-theory (e/d () ())))))

(local
 (defthm lemma13
   (implies (is-rp term)
            (equal (MV-NTH
                    0
                    (rp-rw (cadr term) RULES-FOR-TERM CONTEXT LIMIT RULES-ALIST
                           EXC-RULES meta-rules IFF-FLG rp-state STATE))
                   (cadr term)))
   :hints (("Goal"
            :expand ((rp-rw (cadr term) RULES-FOR-TERM CONTEXT LIMIT RULES-ALIST
                            EXC-RULES meta-rules IFF-FLG rp-state STATE))
            :in-theory (e/d (is-rp) (rp-rw-subterms
                                     rp-rw))))))

#|(local
 (defthm lemma14
   (implies (and (rp-syntaxp-lst subterms))
            (and (rp-syntaxp (car subterms))
                 (rp-syntaxp (cadr subterms))
                 (RP-SYNTAXP-LST (CDDR subterms))
                 (RP-SYNTAXP-LST (CDR subterms))
                 (rp-syntaxp (caddr subterms))))
   :rule-classes :forward-chaining))||#

(local
 (defthmd lemma15
   (implies (and
             (rp-term-listp subterms)
             (not (consp (cdr subterms))))
            (equal (cdr subterms) nil))
   :hints (("Goal"
            :expand (rp-term-listp subterms)
            :in-theory (e/d (rp-term-listp rp-termp) ())))))

#|(local
 (defthm lemma16
   (implies (and (rp-syntaxp term)
                 (context-syntaxp context)
                 (RULES-ALISTP RULES-ALIST)
                 (SYMBOL-ALISTP EXC-RULES)
                 (NOT (EQUAL (CAR term) 'FALIST))
                 (all-falist-consistent term)
                 (rp-meta-valid-syntax-listp meta-rules state)
                 (rp-termp term))
            (rp-syntaxp
             (cons
              (car term)
              (mv-nth 0 (RP-RW-SUBTERMS (cdr term) DONT-RW CONTEXT
                                        LIMIT RULES-ALIST EXC-RULES meta-rules rp-state
                                        STATE)))))
   :hints (("Goal"
            :cases ((equal (car term) 'quote))
            :do-not-induct t
            :in-theory (e/d ()
                            (SYMBOL-ALISTP
                             all-falist-consistent
                             is-falist
                             rp-termp
                             rp-rw
                             RP-TERMP-IMPLIES-CDR-LISTP
                             RP-TERM-LISTP-IS-TRUE-LISTP
                             RP-TERMP
                             VALID-RULES-ALISTP-IMPLIES-RULES-ALISTP
                             context-syntaxp
                             RULES-ALISTP))))))||#

(verify-guards check-if-relieved-with-rp-aux
  :hints (("Goal"
           :in-theory (e/d (is-rp) ()))))

(verify-guards check-if-relieved-with-rp)

(local
 (defthm REMOVE-RP-FROM-BINDINGS-FOR-SYNP-return-val
   (implies
    (bindings-alistp bindings)
    (bindings-alistp (REMOVE-RP-FROM-BINDINGS-FOR-SYNP rule bindings)))
   :hints (("Goal"
            :in-theory (e/d (REMOVE-RP-FROM-BINDINGS-FOR-SYNP) ())))))

(local
 (defthm REMOVE-RP-FROM-BINDINGS-FOR-SYNP-return-val-alistp
   (implies
    (alistp bindings)
    (alistp (REMOVE-RP-FROM-BINDINGS-FOR-SYNP rule bindings)))
   :hints (("Goal"
            :in-theory (e/d (REMOVE-RP-FROM-BINDINGS-FOR-SYNP) ())))))

;; (local
;;  (defthm WEAK-RP-STAT-P-implies-fc
;;    (implies (WEAK-RP-STAT-P rp-state)
;;             (AND (CONSP rp-state)
;;                  (LET ((rp-state (CDR rp-state)))
;;                       (CONSP rp-state))))
;;    :rule-classes :forward-chaining
;;    :hints (("Goal"
;;             :in-theory (e/d (weak-rp-stat-p) ())))))

(local
 (defthm integerp-of-rp-state-push-to-try-to-rw-stack
   (implies (rp-statep rp-state)
            (and (integerp (mv-nth 0 (rp-state-push-to-try-to-rw-stack rule var-bindings
                                                                       rp-context
                                                                       rp-state)))))
   :hints (("Goal"
            :in-theory (e/d (rp-state-push-to-try-to-rw-stack
                             rp-statep) ())))))

(verify-guards rp-rw
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d
                       (dont-rw-if-fix-type

                        dont-rw-syntaxp
                        TRUE-LISTP
                        QUOTEP
                        )
                       (
                        rp-termp
                        rp-term-listp
                        (:DEFINITION VALID-RULESP)
                        (:DEFINITION VALID-RULEP)
                        (:DEFINITION VALID-RULEP-SK)
                        (:REWRITE
                         VALID-RULES-ALISTP-IMPLIES-RULES-ALISTP)
                        (:DEFINITION VALID-RULES-ALISTP)
                        (:DEFINITION RP-EQUAL)
                        (:DEFINITION RP-CHECK-CONTEXT)
                        (:REWRITE RP-EQUAL-IS-SYMMETRIC)
                        (:DEFINITION VALID-SC)
                        (:REWRITE RP-EQUAL-CNT-IS-RP-EQUAL)
                        (:DEFINITION EX-FROM-RP)
                        (:REWRITE NOT-INCLUDE-RP)
                        (:REWRITE NOT-QUOTEP-IMPLIES)
                        (:DEFINITION INCLUDE-FNC)
                        (:REWRITE RP-EVL-OF-RP-EQUAL2)
                        (:DEFINITION RP-EQUAL2)
                        (:REWRITE ACL2::O-P-O-INFP-CAR)
                        (:DEFINITION QUOTEP)
                        (:REWRITE RP-EQUAL-IMPLIES-RP-EQUAL2)
                        (:REWRITE LEMMA11)
                        (:DEFINITION EVAL-AND-ALL)
                        (:TYPE-PRESCRIPTION INCLUDE-FNC)
                        (:REWRITE LEMMA6)
                        FALIST-CONSISTENT
                        is-if
                        IS-FALIST
                        #|RP-RW-APPLY-FALIST-META||#
                        rp-rw-meta-rules

                        RP-EX-COUNTERPART
                        (:DEFINITION LEN)
                        (:DEFINITION RP-RW)
;(:DEFINITION RP-RW-APPLY-META)
                        (:REWRITE DEFAULT-<-1)
                        (:TYPE-PRESCRIPTION ALISTP)
                        (:TYPE-PRESCRIPTION TRUE-LIST-LISTP)
                        (:TYPE-PRESCRIPTION EQLABLE-ALISTP)
                        (:TYPE-PRESCRIPTION SYMBOL-ALISTP))))))





(verify-guards rp-rw-aux
  :otf-flg t
  :hints (("goal"
           :do-not-induct t
           ;;:use ((:instance rp-termp-remove-return-last))
           :in-theory
           (e/d (rp-term-listp
                 rp-statep
                 context-syntaxp
                 rp-termp)
                (#|rp-termp-remove-return-last||#
                 rp-rw
                 ;;rp-stat-p
                 ;;is-exc-enabled
                 rp-ex-counterpart
                 #|rp-rw-apply-falist-meta||#
                 (:rewrite
                  valid-rules-alistp-implies-rules-alistp)
                 (:definition valid-rules-alistp)
                 (:definition valid-rulesp)
                 (:definition valid-rulep)
                 (:definition valid-rulep-sk)
                 (:definition valid-rulep-sk-body)
                 (:definition rp-termp)
                 (:rewrite lemma11)
                 (:rewrite rp-evl-of-rp-equal2)
                 (:definition rp-equal2)
                 (:definition ex-from-rp)
                 (:definition rp-equal)
                 (:rewrite rp-equal-implies-rp-equal2)
                 (:rewrite not-include-rp)
                 (:definition include-fnc)
                 (:linear acl2::apply$-badgep-properties . 1)
                 (:definition acl2::apply$-badgep)
                 (:definition include-fnc-subterms)
                 (:definition subsetp-equal)
                 (:definition member-equal)
                 (:definition falist-consistent)
                 (:definition len)
                 (:definition rp-rw)
                 ;;(:definition rp-rw-apply-meta)
                 ;;(:type-prescription context-syntaxp)
                 (:rewrite default-<-1)
                 (:type-prescription alistp)
                 (:type-prescription true-list-listp)
                 (:type-prescription eqlable-alistp)
                 (:type-prescription symbol-alistp))))))
