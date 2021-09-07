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
(local (include-book "local-lemmas"))
(local (include-book "aux-function-lemmas"))
(include-book "proof-functions")
(local (include-book "proof-function-lemmas"))
(local (include-book "rp-equal-lemmas"))
(local (include-book "apply-bindings-lemmas"))
(local (include-book "match-lhs-lemmas"))
(local (include-book "rp-rw-lemmas"))
(local (include-book "extract-formula-lemmas"))

(in-theory (disable rp-iff-flag rp-lhs rp-rhs rp-hyp))



(progn

  #|(defthm attach-sc-from-context-returns-context-syntaxp
    (implies (context-syntaxp context)
             (context-syntaxp (attach-sc-from-context context term)))
    :hints (("Goal"
             :do-not-induct t
             :induct (attach-sc-from-context context term)
             :in-theory (e/d (attach-sc-from-context) ()))))||#

  

  #|(defthm eval-of-context-from-attach-sc-from-context-returns
    (implies (eval-and-all context a)
             (eval-and-all (mv-nth 0 (attach-sc-from-context context term)) a))
    :hints (("Goal"
             :do-not-induct t
             :induct (attach-sc-from-context context term)
             :in-theory (e/d (attach-sc-from-context) ()))))||#

  

  #|(defthm VALID-SC-SUBTERMS-from-attach-sc-from-context-returns
    (implies (VALID-SC-SUBTERMS context a)
             (VALID-SC-SUBTERMS (mv-nth 0 (attach-sc-from-context context term)) a))
    :hints (("Goal"
             :do-not-induct t
             :induct (attach-sc-from-context context term)
             :in-theory (e/d (attach-sc-from-context) ()))))||#

  

  (defthm eval-of-term-from-attach-sc-from-context-returns
    (implies (and (eval-and-all context a))
             (equal (rp-evlt (attach-sc-from-context context term) a)
                    (rp-evlt term a)))
    :hints (("Goal"
             :do-not-induct t
             :expand ((IS-RP (LIST 'RP ''QUOTE (CADR (CAR CONTEXT)))))
             :induct (attach-sc-from-context context term)
             :in-theory (e/d (attach-sc-from-context) ()))))


  (local
   (defthm not-is-rp-ex-from-rp
     (not (is-rp (ex-from-rp term)))
     :hints (("Goal"
              :in-theory (e/d (is-rp
                               ex-from-rp)
                              ())))))

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
  
  (defthm valid-sc-term-from-attach-sc-from-context-returns
    (implies (and (eval-and-all context a)
                  (rp-termp term)
;(not (include-fnc-subterms context 'list))

                  (valid-sc term a))
             (valid-sc (attach-sc-from-context context term) a))
    :hints (("Goal"
             :do-not-induct t
             :induct (attach-sc-from-context context term)
             :in-theory (e/d (attach-sc-from-context is-if
                                                     RP-EVLt-OF-FNCALL-ARGS
                                                     RP-EVL-OF-FNCALL-ARGS
                                                     is-rp) ()))))

  (defthm rp-termp-attach-sc-from-context
    (implies (and (rp-termp term)
                  (context-syntaxp context))
             (rp-termp (attach-sc-from-context context term)))
    :hints (("Goal"
             :do-not-induct t
             :induct (attach-sc-from-context context term)
             :in-theory (e/d (attach-sc-from-context) ())))))


(progn
  (defthm attach-sc-from-context-lst-returns-context-syntaxp
    (implies (and (context-syntaxp context)
                  (context-syntaxp terms))
             (context-syntaxp (attach-sc-from-context-lst context terms)))
    :hints (("Goal"
             :do-not-induct t
             :induct (attach-sc-from-context-lst context terms)
             :in-theory (e/d (attach-sc-from-context-lst) ()))))

  (defthm eval-of-context-from-attach-sc-from-context-lst
    (implies (and (eval-and-all context a)
                  (eval-and-all terms a))
             (eval-and-all (attach-sc-from-context-lst context terms) a))
    :hints (("Goal"
             :do-not-induct t
             :induct (attach-sc-from-context-lst context terms)
             :in-theory (e/d (attach-sc-from-context-lst) ()))))

  (defthm VAlid-sc-subterms-from-attach-sc-from-context-lst
    (implies (and (valid-sc-subterms context a)
                  (eval-and-all context a)
                  (valid-sc-subterms terms a)
                  (rp-term-listp terms))
             (valid-sc-subterms (attach-sc-from-context-lst context terms) a))
    :hints (("Goal"
             :do-not-induct t
             :induct (attach-sc-from-context-lst context terms)
             :in-theory (e/d (attach-sc-from-context-lst) ()))))

  (defthm eval-of-term-from-attach-sc-from-context-lst
    (implies (and (eval-and-all context a))
             (equal (rp-evlt-lst (attach-sc-from-context-lst context terms) a)
                    (rp-evlt-lst terms a)))
    :hints (("Goal"
             :do-not-induct t
             :induct (attach-sc-from-context-lst context terms)
             :in-theory (e/d (attach-sc-from-context-lst) ())))))



(defthm attach-sc-from-context-lst-returns-rp-term-listp
  (implies (and (rp-term-listp context)
                (rp-term-listp terms))
           (rp-term-listp (attach-sc-from-context-lst context terms)))
  :hints (("Goal"
           :do-not-induct t
           :induct (attach-sc-from-context-lst context terms)
           :in-theory (e/d (attach-sc-from-context-lst) ()))))


(local
 (defthm rp-state-preservedp-chain-lemma
   (IMPLIES
    (AND  (RP-STATE-PRESERVEDP RP-STATE1 x)
          (syntaxp (and (not (equal rp-state1 x))
                        (not (equal rp-state x))
                        (not (equal rp-state1 rp-state))))
          (RP-STATE-PRESERVEDP RP-STATE RP-STATE1))
    (RP-STATE-PRESERVEDP RP-STATE x))
   :hints (("Goal"
            :expand ((RP-STATE-PRESERVEDP-SK RP-STATE X))
            :use ((:instance RP-STATE-PRESERVEDP-SK-necc
                             (old-rp-state rp-state1)
                             (new-rp-state x)
                             (key (RP-STATE-PRESERVEDP-SK-WITNESS RP-STATE X)))
                  (:instance RP-STATE-PRESERVEDP-SK-necc
                             (old-rp-state rp-state)
                             (new-rp-state rp-state1)
                             (key (RP-STATE-PRESERVEDP-SK-WITNESS RP-STATE X))))
            :in-theory (e/d (RP-STATE-PRESERVEDP
                             )
                            (RP-STATE-PRESERVEDP-SK))))))

#|(local
 (defthm RP-STATE-PRESERVEDP-chain-lemma1
   (implies (and (RP-STATE-PRESERVEDP rp-state rp-state1))
            (rp-state-preservedp
             rp-state
             (MV-NTH 1 (RP-RW-PREPROCESSOR term context rp-state1 STATE))))
   :hints (("Goal"
            :use ((:instance rp-rw-preprocessor-rp-state-preservedp
                             (rp-state rp-state1)))
            :in-theory (e/d () (rp-rw-preprocessor-rp-state-preservedp))))))||#


#|(local
 (defthm dummy-nonnil-p-lemma
   (implies (and (nonnil-p res-term)
                 (iff (rp-evlt res-term a)
                      (rp-evlt term a)))
            (rp-evlt term a))
   :hints (("Goal"
            :in-theory (e/d () ())))))||#

(local
 (defthmd dummy-nonnil-p-lemma2
   (implies (and (nonnil-p res-term)
                 (rp-evlt (cadr term) a) 
                 (syntaxp (and (consp res-term)
                               (equal (car res-term)
                                      'rp-rw-postprocessor)
                               ))
                 (force (iff (rp-evlt res-term a)
                             (rp-evlt (caddr term) a)))
                 (not (include-fnc (caddr term)  'list)))
            (rp-evl (caddr term) a))
   :hints (("Goal"
            :in-theory (e/d () ())))))



(local
 (defthmd nonnil-p-lemma
   (implies (nonnil-p term)
            (and (rp-evlt term a)
                 (rp-evl term a)))))


(local
 (encapsulate
   nil
   (local
    (defthm lemma1
      (implies (and (consp term)
                    (consp (cdr term))
                    (consp (cddr term))
                    (not (equal (car term) 'quote))
                    (rp-termp term))
               (and (rp-termp (caddr term))
                    (rp-termp (cadr term))))))

   #|(local
   (defthm lemma2
   (implies (and (consp term)
   (consp (cdr term))
   (consp (cddr term))
   (not (equal (car term) 'quote))
   (all-falist-consistent term))
   (and (all-falist-consistent (caddr term))
   (all-falist-consistent (cadr term))))))||#

   #|(local
   (defthm lemma3
   (implies (and (consp term)
   (consp (cdr term))
   (consp (cddr term))
   (not (equal (car term) 'quote))
   (rp-syntaxp term))
   (and (rp-syntaxp (caddr term))
   (rp-syntaxp (cadr term))))
   :hints (("Goal"
   :in-theory (e/d (is-rp) ())))))||#

   (local
    (defthm lemma4
      (implies (and (valid-sc term a)
                    (consp term)
                    (consp (cdr term))
                    (consp (cddr term))
                    (equal (car term) 'implies))
               (and (valid-sc (cadr term) a)
                    (valid-sc (caddr term) a)))
      :hints (("Goal"
               :expand ((VALID-SC TERM A))
               :in-theory (e/d (is-if is-rp) ())))))

   (local
    (defthm is-falist-of-implies
      (not (is-falist (cons 'implies x)))))

   (local
    (defthm include-fnc-lemma
      (implies (and (NOT (INCLUDE-FNC term 'LIST))
                    (not (quotep term)))
               (and (NOT (INCLUDE-FNC (CADR TERM) 'LIST))
                    (NOT (INCLUDE-FNC (CAdDR TERM) 'LIST))))))


   (local
    (in-theory (e/d (valid-rp-statep-implies-valid-rp-state-syntaxp
                               rp-evl-and-side-cond-consistent-of-rp-rw)
                              (rp-rw
                               rp-statep
                               nonnil-p-lemma
                               nonnil-p
                               (:type-prescription nonnil-p) 
                               valid-rp-statep
                               RW-STEP-LIMIT
                               dummy-nonnil-p-lemma2
                               is-falist
                               rp-termp
                               include-fnc
                               valid-sc
                               rp-trans
                               rp-trans-lst
                               valid-sc
                               valid-rules-alistp
                               RP-EVL-of-variable
                               ;;valid-rp-meta-rule-listp
                               EVAL-AND-ALL
                               ;;rp-evl-and-side-cond-consistent-of-rp-rw

                               (:DEFINITION VALID-SC-SUBTERMS)
                               (:REWRITE VALID-SC-CONS)
                               (:TYPE-PRESCRIPTION RP-TERMP)
                               (:TYPE-PRESCRIPTION VALID-SC)
                               (:DEFINITION ACL2::APPLY$-BADGEP)

                               (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                               (:TYPE-PRESCRIPTION ALISTP)
                               (:REWRITE ACL2::O-P-O-INFP-CAR)
                               (:DEFINITION SUBSETP-EQUAL)
                               (:REWRITE VALID-SC-CADR)
                               (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                               (:DEFINITION RP-EXTRACT-CONTEXT)
                               (:REWRITE EX-FROM-SYNP-LEMMA1)
                               (:REWRITE
                                CHECK-IF-RELIEVED-WITH-RP-IS-CORRECT)
                               (:REWRITE ACL2::APPEND-WHEN-NOT-CONSP)
                               (:DEFINITION BINARY-APPEND)
                               (:TYPE-PRESCRIPTION RP-EXTRACT-CONTEXT)
                               (:TYPE-PRESCRIPTION IS-RP$INLINE)
                               (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                               (:TYPE-PRESCRIPTION INCLUDE-FNC)
                               (:TYPE-PRESCRIPTION FALIST-CONSISTENT)
                               (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                               (:TYPE-PRESCRIPTION VALID-RULES-ALISTP)
                               ;;(:TYPE-PRESCRIPTION VALID-RP-META-RULE-LISTP)
                               (:TYPE-PRESCRIPTION SYMBOL-ALISTP)
                               #|(:TYPE-PRESCRIPTION
                                RP-META-VALID-SYNTAX-LISTP)||#
                               (:TYPE-PRESCRIPTION EQLABLE-ALISTP)

                               rp-termp
                               CONTEXT-SYNTAXP
                               INCLUDE-FNC
                               RP-TERMP
                               TRUE-LISTP
                               beta-search-reduce))))
    

   (defthm preprocess-then-rp-rw-is-correct-lemma
     (implies (and (rp-termp term)
                   (valid-sc term a)
                   (not (include-fnc term 'rp))
                   (alistp a)
                   (rp-evl-meta-extract-global-facts :state state)
                   (rp-formula-checks state)
                   (valid-rp-statep rp-state)
                   (rp-statep rp-state)
                   )
              (iff (rp-evl
                    (mv-nth 0 (preprocess-then-rp-rw term rp-state state)) a)
                   (rp-evl term a)))
     :hints (("Goal"
              :do-not-induct t
              :do-not '(preprocess fertilize)
              :in-theory (e/d (dummy-nonnil-p-lemma2
                               nonnil-p-lemma)
                              ())
              :use ()

                    #|(:instance rp-evl-and-side-cond-consistent-of-rp-rw
                               (term term #|(remove-return-last term)||#)
                               (dont-rw nil)
                               (context nil)
                               (hyp-flg nil)
                               (limit (rw-step-limit rp-state))
                               (iff-flg t))
                    (:instance rp-evl-and-side-cond-consistent-of-rp-rw
                               (term (cadr term #|(remove-return-last term)||#))
                               (dont-rw nil)
                               (context nil)
                               (hyp-flg nil)
                               (limit (rw-step-limit rp-state))
                               (iff-flg t))

                    (:instance rp-evl-and-side-cond-consistent-of-rp-rw
                               (term (MV-NTH 0
                                             (RP-RW-PREPROCESSOR TERM NIL RP-STATE STATE)))
                               (dont-rw nil)
                               (context nil)
                               (hyp-flg nil)
                               (limit (rw-step-limit rp-state))
                               (rp-state (MV-NTH 1
                                                 (RP-RW-PREPROCESSOR TERM NIL RP-STATE STATE)))
                               (iff-flg t))
                    
                    (:instance rp-evl-and-side-cond-consistent-of-rp-rw
                               (term (mv-nth
                                      0
                                      (rp-rw-preprocessor
                                       (attach-sc-from-context
                                        (rp-extract-context
                                         (mv-nth 0
                                                 (rp-rw (cadr term)
                                                        nil nil t nil (rw-step-limit rp-state)
                                                        rp-state state)))
                                        (caddr term))
                                       (attach-sc-from-context-lst
                                        (rp-extract-context
                                         (mv-nth 0
                                                 (rp-rw (cadr term)
                                                        nil nil t nil (rw-step-limit rp-state)
                                                        rp-state state)))
                                        (rp-extract-context
                                         (mv-nth 0
                                                 (rp-rw (cadr term)
                                                        nil nil t nil (rw-step-limit rp-state)
                                                        rp-state state))))
                                       (mv-nth 1
                                               (rp-rw (cadr term)
                                                      nil nil t nil (rw-step-limit rp-state)
                                                      rp-state state))
                                       state)))
                               (dont-rw nil)
                               (context (attach-sc-from-context-lst
                                         (rp-extract-context
                                          (mv-nth 0
                                                  (rp-rw (cadr term)
                                                         nil nil t nil (rw-step-limit rp-state)
                                                         rp-state state)))
                                         (rp-extract-context
                                          (mv-nth 0
                                                  (rp-rw (cadr term)
                                                         nil nil t nil (rw-step-limit rp-state)
                                                         rp-state state)))))
                               (limit (rw-step-limit rp-state))
                               (iff-flg t)
                               (hyp-flg nil)
                               (rp-state  (mv-nth
                                           1
                                           (rp-rw-preprocessor
                                            (attach-sc-from-context
                                             (rp-extract-context
                                              (mv-nth 0
                                                      (rp-rw (cadr term)
                                                             nil nil t nil (rw-step-limit rp-state)
                                                             rp-state state)))
                                             (caddr term))
                                            (attach-sc-from-context-lst
                                             (rp-extract-context
                                              (mv-nth 0
                                                      (rp-rw (cadr term)
                                                             nil nil t nil (rw-step-limit rp-state)
                                                             rp-state state)))
                                             (rp-extract-context
                                              (mv-nth 0
                                                      (rp-rw (cadr term)
                                                             nil nil t nil (rw-step-limit rp-state)
                                                             rp-state state))))
                                            (mv-nth 1
                                                    (rp-rw (cadr term)
                                                           nil nil t nil (rw-step-limit rp-state)
                                                           rp-state state))
                                            state))))||#
                    #|(:instance rp-evl-and-side-cond-consistent-of-rp-rw
                               (term (mv-nth
                                      1
                                      (attach-sc-from-context
                                       (rp-extract-context
                                        (mv-nth 0
                                                (rp-rw (cadr term)
                                                       nil nil
                                                       t nil (rw-step-limit
                                                          rp-state)
                                                       rp-state state)))
                                       (caddr term))))
                               (dont-rw nil)
                               (context (mv-nth
                                         0
                                         (attach-sc-from-context
                                          (rp-extract-context
                                           (mv-nth 0
                                                   (rp-rw (cadr term)
                                                          nil nil
                                                          t nil (rw-step-limit rp-state) rp-state state)))
                                          (caddr term))))
                               (limit (rw-step-limit rp-state))
                               (iff-flg t)
                               (hyp-flg nil)
                               (rp-state (mv-nth 1
                                                 (rp-rw (cadr term)
                                                        nil nil
                                                        t nil (rw-step-limit
                                                            rp-state)
                                                        rp-state
                                                        state))))||#
              :expand ((:free (x y) (iff x y))
                       (:free (x) (rp-trans (cons 'implies x)))
                       (:free (x y) (RP-TRANS-LST (cons x y))))
              )))))



(encapsulate
  nil

  (defthmd preprocess-then-rp-rw-is-correct
    (implies (and (rp-termp term)
                  (not (Include-fnc term 'rp))
                  (valid-rp-statep rp-state)
                  (rp-statep rp-state)
                  (alistp a)
                  (rp-evl-meta-extract-global-facts :state state)
                  (rp-formula-checks state)
                  )
             (iff (rp-evl (mv-nth 0 (preprocess-then-rp-rw term rp-state state)) a)
                  (rp-evl term a)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d ()
                             (rp-rw
                              preprocess-then-rp-rw
                              valid-rules-alistp
                              valid-termp
                              remove-return-last
                              beta-search-reduce))))))

#|(defthm rp-meta-rule-recs-p-implies-WEAK-RP-META-RULE-REC-P
  (implies (rp-meta-rule-recs-p meta-rules state)
           (weak-rp-meta-rule-recs-p meta-rules))
  :hints (("Goal"
           :induct (weak-rp-meta-rule-recs-p meta-rules)
           :in-theory (e/d (weak-rp-meta-rule-recs-p
                            rp-meta-rule-recs-p) ()))))||#

#|(defthm remove-disabled-meta-rules-returns-rp-meta-rule-recs-p
  (implies (rp-meta-rule-recs-p meta-rules state)
           (rp-meta-rule-recs-p
            (remove-disabled-meta-rules meta-rules
                                        disabled-meta-rules)
            state))
  :hints (("Goal"
           :in-theory (e/d (rp-meta-rule-recs-p
                            remove-disabled-meta-rules)
                           ()))))||#

#|(defthm remove-disabled-meta-rules-returns-RP-META-VALID-SYNTAX-LISTP
  (implies (RP-META-VALID-SYNTAX-LISTP meta-rules state)
           (RP-META-VALID-SYNTAX-LISTP
            (remove-disabled-meta-rules meta-rules
                                        disabled-meta-rules)
            state))
  :hints (("Goal"
           :in-theory (e/d (RP-META-VALID-SYNTAX-LISTP
                            remove-disabled-meta-rules)
                           ()))))||#

(defthm rp-statep-of-preprocess-then-rp-rw
  (implies (rp-statep rp-state)
           (rp-statep (mv-nth 1 (preprocess-then-rp-rw term  rp-state state))))
  :hints (("Goal"
           :in-theory (e/d ()
                           ((:DEFINITION RP-RW)
                            (:DEFINITION RP-STATEP)
                            (:DEFINITION QUOTEP)
                            (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                            (:DEFINITION TRUE-LISTP))))))

(defthm valid-rp-state-syntaxp-of-preprocess-then-rp-rw
  (implies (valid-rp-state-syntaxp rp-state)
           (valid-rp-state-syntaxp (mv-nth 1 (preprocess-then-rp-rw term  rp-state state))))
  :hints (("Goal"
           :in-theory (e/d ()
                           ((:DEFINITION RP-RW)
                            (:DEFINITION RP-STATEP)
                            (:DEFINITION QUOTEP)
                            (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                            (:DEFINITION TRUE-LISTP))))))

(defthm valid-rp-statep-of-preprocess-then-rp-rw
  (implies (and (valid-rp-statep rp-state)
                (rp-statep rp-state))
           (valid-rp-statep (mv-nth 1 (preprocess-then-rp-rw term  rp-state state))))
  :hints (("Goal"
           :in-theory (e/d ()
                           ((:DEFINITION RP-RW)
                            (:DEFINITION RP-STATEP)
                            valid-rulesp
                            (:DEFINITION QUOTEP)
                            (:DEFINITION INCLUDE-FNC)
                            (:DEFINITION INCLUDE-FNC-SUBTERMS)
                            (:DEFINITION IS-FALIST)
                            (:DEFINITION MV-NTH)
                            (:DEFINITION RP-TRANS-LST)
                            (:DEFINITION RW-STEP-LIMIT)
                            (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                            (:DEFINITION TRUE-LISTP))))))
