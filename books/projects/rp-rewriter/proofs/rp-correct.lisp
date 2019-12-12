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


(encapsulate
  nil


  (defthm attach-sc-from-context-returns-context-syntaxp
    (implies (context-syntaxp context)
             (context-syntaxp (mv-nth 0 (attach-sc-from-context context term))))
    :hints (("Goal"
             :do-not-induct t
             :induct (attach-sc-from-context context term)
             :in-theory (e/d (attach-sc-from-context) ()))))
  
  (defthm eval-of-context-from-attach-sc-from-context-returns
    (implies (eval-and-all context a)
             (eval-and-all (mv-nth 0 (attach-sc-from-context context term)) a))
    :hints (("Goal"
             :do-not-induct t
             :induct (attach-sc-from-context context term)
             :in-theory (e/d (attach-sc-from-context) ()))))

  (defthm VALID-SC-SUBTERMS-from-attach-sc-from-context-returns
    (implies (VALID-SC-SUBTERMS context a)
             (VALID-SC-SUBTERMS (mv-nth 0 (attach-sc-from-context context term)) a))
    :hints (("Goal"
             :do-not-induct t
             :induct (attach-sc-from-context context term)
             :in-theory (e/d (attach-sc-from-context) ()))))

  (defthm eval-of-term-from-attach-sc-from-context-returns
    (implies (and (eval-and-all context a))
             (equal (rp-evlt (mv-nth 1 (attach-sc-from-context context term)) a)
                    (rp-evlt term a)))
    :hints (("Goal"
             :do-not-induct t
             :expand ((IS-RP (LIST 'RP ''QUOTE (CADR (CAR CONTEXT)))))
             :induct (attach-sc-from-context context term)
             :in-theory (e/d (attach-sc-from-context) ()))))

  (defthm valid-sc-term-from-attach-sc-from-context-returns
    (implies (and (eval-and-all context a)
                  (rp-termp term)
                  ;(not (include-fnc-subterms context 'list))
                  
                  (valid-sc term a))
             (valid-sc (mv-nth 1 (attach-sc-from-context context term)) a))
    :hints (("Goal"
             :do-not-induct t
             :induct (attach-sc-from-context context term)
             :in-theory (e/d (attach-sc-from-context is-if
                                                     is-rp) ()))))

  (defthm rp-termp-attach-sc-from-context
    (implies (and (rp-termp term)
                  (context-syntaxp context))
             (rp-termp (mv-nth 1 (attach-sc-from-context context term))))
    :hints (("Goal"
             :do-not-induct t
             :induct (attach-sc-from-context context term)
             :in-theory (e/d (attach-sc-from-context) ()))))

  

  )



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
   
   (defthm rp-rw-aux-is-correct-lemma
     (implies (and (rp-termp term)
                   (valid-sc term a)
                   (not (include-fnc term 'rp))
                   (alistp a)
                   (rp-evl-meta-extract-global-facts :state state)
                   (valid-rp-meta-rule-listp meta-rules state)
                   (rp-meta-valid-syntax-listp meta-rules state)
                   (symbol-alistp exc-rules)
                   ;;(rp-syntaxp term)
                   (valid-rules-alistp rules-alist))
              (iff (rp-evl
                    (mv-nth 0 (rp-rw-aux term rules-alist exc-rules meta-rules rp-state state)) a)
                   (rp-evl term a)))
     :hints (("Goal"
              :do-not-induct t
              :do-not '(preprocess fertilize)
              :use ((:instance rp-evl-and-side-cond-consistent-of-rp-rw
                               (term term #|(REMOVE-RETURN-LAST TERM)||#)
                               (dont-rw nil)
                               (context nil)
                               (limit (RW-STEP-LIMIT RP-STATE))
                               (iff-flg t))
                    (:instance rp-evl-and-side-cond-consistent-of-rp-rw
                               (term (CADR term #|(REMOVE-RETURN-LAST TERM)||#))
                               (dont-rw nil)
                               (context nil)
                               (limit (RW-STEP-LIMIT RP-STATE))
                               (iff-flg t))
                    (:instance rp-evl-and-side-cond-consistent-of-rp-rw
                               (term (MV-NTH
                                      1
                                      (ATTACH-SC-FROM-CONTEXT
                                       (RP-EXTRACT-CONTEXT
                                        (MV-NTH 0
                                                (RP-RW (CADR TERM)
                                                       NIL NIL (RW-STEP-LIMIT RP-STATE)
                                                       RULES-ALIST
                                                       EXC-RULES META-RULES T RP-STATE STATE)))
                                       (CADDR TERM))))
                               (dont-rw nil)
                               (context (MV-NTH
                                         0
                                         (ATTACH-SC-FROM-CONTEXT
                                          (RP-EXTRACT-CONTEXT
                                           (MV-NTH 0
                                                   (RP-RW (CADR TERM)
                                                          NIL NIL (RW-STEP-LIMIT RP-STATE)
                                                          RULES-ALIST
                                                          EXC-RULES META-RULES T RP-STATE STATE)))
                                          (CADDR TERM))))
                               (limit (RW-STEP-LIMIT RP-STATE))
                               (iff-flg t)
                               (rp-state (MV-NTH 1
                                                 (RP-RW (CADR term #|(REMOVE-RETURN-LAST TERM)||#)
                                                        NIL NIL (RW-STEP-LIMIT RP-STATE)
                                                        RULES-ALIST EXC-RULES
                                                        meta-rules T rp-state
                                                        STATE)))))
              :expand ((:free (x y) (iff x y))
                       (:free (x) (rp-trans (cons 'implies x)))
                       (:free (x y) (RP-TRANS-LST (cons x y)))) 
;:expand ((:free (context) (CONTEXT-SYNTAXP context)))
              :in-theory (e/d (;rp-evl-of-remove-from-last
                               ;;context-syntaxp-implies
                               )
                              (rp-rw
                               RW-STEP-LIMIT
                               SYNP
                               is-falist
                               rp-termp
                               include-fnc
                               valid-sc
                               rp-trans
                               rp-trans-lst
                               valid-sc
                               valid-rules-alistp
                               RP-EVL-of-variable
                               valid-rp-meta-rule-listp
                               EVAL-AND-ALL
                               rp-evl-and-side-cond-consistent-of-rp-rw

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
                               (:TYPE-PRESCRIPTION VALID-RP-META-RULE-LISTP)
                               (:TYPE-PRESCRIPTION SYMBOL-ALISTP)
                               (:TYPE-PRESCRIPTION
                                RP-META-VALID-SYNTAX-LISTP)
                               (:TYPE-PRESCRIPTION EQLABLE-ALISTP)
                               
                               
                               rp-termp
                               CONTEXT-SYNTAXP
                               INCLUDE-FNC
                               RP-TERMP
                               TRUE-LISTP

;remove-return-last
                               beta-search-reduce)))))))

#|(defthmd no-rp-no-falist-term-implies-valid-termp
  (implies (valid-term-syntaxp term)
           (valid-termp term  a))
  :hints (("Goal"
           :in-theory (e/d (EXT-SIDE-CONDITIONS ALL-FALIST-CONSISTENT
                                                is-falist is-rp) ()))))||#





(encapsulate
  nil
  #|(local
   (defthm lemma1
     (implies (valid-term-syntaxp term)
              (not (include-fnc term 'rp)))
     :hints (("Goal"
              :in-theory (e/d (valid-term-syntaxp) ())))))||#

  (defthmd rp-rw-aux-is-correct
    (implies (and (rp-termp term)
                  (not (Include-fnc term 'rp))
                  (symbol-alistp exc-rules)
                  (alistp a)
                  (rp-evl-meta-extract-global-facts :state state)
                  (rp-meta-valid-syntax-listp meta-rules state)
                  (valid-rp-meta-rule-listp meta-rules state)
                  (valid-rules-alistp rules-alist))
             (iff (rp-evl (mv-nth 0 (rp-rw-aux term rules-alist exc-rules meta-rules rp-stat state)) a)
                  (rp-evl term a)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (#|no-rp-no-falist-term-implies-valid-termp||#)
                             (rp-rw
                              rp-rw-aux
                              valid-rules-alistp
                              #|valid-term-syntaxp||#
                              valid-termp
                              remove-return-last
                              beta-search-reduce))))))



(defthm rp-meta-rule-recs-p-implies-WEAK-RP-META-RULE-REC-P
  (implies (rp-meta-rule-recs-p meta-rules state)
           (weak-rp-meta-rule-recs-p meta-rules))
  :hints (("Goal"
           :induct (weak-rp-meta-rule-recs-p meta-rules)
           :in-theory (e/d (weak-rp-meta-rule-recs-p
                            rp-meta-rule-recs-p) ()))))

(defthm remove-disabled-meta-rules-returns-rp-meta-rule-recs-p
  (implies (rp-meta-rule-recs-p meta-rules state)
           (rp-meta-rule-recs-p
            (remove-disabled-meta-rules meta-rules
                                        disabled-meta-rules)
            state))
  :hints (("Goal"
           :in-theory (e/d (rp-meta-rule-recs-p
                            remove-disabled-meta-rules) ()))))

(defthm remove-disabled-meta-rules-returns-valid-rp-meta-rule-listp
  (implies (valid-rp-meta-rule-listp meta-rules state)
           (valid-rp-meta-rule-listp
            (remove-disabled-meta-rules meta-rules
                                        disabled-meta-rules)
            state))
  :hints (("Goal"
           :in-theory (e/d (valid-rp-meta-rule-listp
                            remove-disabled-meta-rules)
                           ((:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE NOT-INCLUDE-RP)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE VALID-SC-CONS))))))

(defthm remove-disabled-meta-rules-returns-RP-META-VALID-SYNTAX-LISTP
  (implies (RP-META-VALID-SYNTAX-LISTP meta-rules state)
           (RP-META-VALID-SYNTAX-LISTP
            (remove-disabled-meta-rules meta-rules
                                        disabled-meta-rules)
            state))
  :hints (("Goal"
           :in-theory (e/d (RP-META-VALID-SYNTAX-LISTP
                            remove-disabled-meta-rules) ()))))

(defthm rp-statep-of-rp-rw-aux
  (implies (rp-statep rp-state)
           (rp-statep (mv-nth 1 (rp-rw-aux term rules-alist exc-rules
                                           meta-rules rp-state state))))
  :hints (("Goal"
           :in-theory (e/d ()
                           ((:DEFINITION RP-RW)
                            (:DEFINITION RP-STATEP)
                            (:DEFINITION QUOTEP)
                            (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                            (:DEFINITION TRUE-LISTP))))))
