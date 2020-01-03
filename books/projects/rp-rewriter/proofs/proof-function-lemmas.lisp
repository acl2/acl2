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

(include-Book "proof-functions")

(include-Book "eval-functions-lemmas")

(local (include-book "aux-function-lemmas"))

(defthm eval-and-all-append
  (equal (eval-and-all (append x y) a)
         (and (eval-and-all x a)
              (eval-and-all y a)))
  :hints (("Goal"
           :in-theory (e/d (eval-and-all
                            append) ()))))

(defthm eval-sc-append
  (equal (eval-sc (append x y) a)
         (and (eval-sc x a)
              (eval-sc y a)))
  :hints (("Goal"
           :in-theory (e/d (eval-sc
                            append
                            eval-and-all) ()))))

#|(encapsulate
  nil
  (local
   (defthm flag-for-not-include-rp-of-beta-reduce-term
    (implies (and (not (include-fnc-subterms vals 'rp))
                  #|(symbol-listp keys)||#
                  (if arg
                      (not (include-fnc-subterms term 'rp))
                    (not (include-fnc term 'rp))))
             (if arg
                 (not (include-fnc-subterms (acl2::beta-reduce-term arg term keys vals)
                                            'rp))
               (not (include-fnc (acl2::beta-reduce-term arg term keys vals)
                                 'rp))))))
  (defthm not-include-rp-of-beta-reduce-term-arg=nil
    (implies (and (not (include-fnc-subterms vals 'rp))
                  #|(symbol-listp keys)||#
                  (not (include-fnc term 'rp)))
             (not (include-fnc (acl2::beta-reduce-term nil term keys vals)
                               'rp)))
    :hints (("Goal"
             :use ((:instance flag-for-not-include-rp-of-beta-reduce-term
                              (arg nil)))
             :in-theory (e/d () ()))))

  (defthm not-include-rp-of-beta-reduce-term-expr
    (implies (and (is-lambda term)
                  (not (include-fnc term 'rp)))
             (not (include-fnc (beta-reduce-lambda-expr term) 'rp)))
    :hints (("Goal"
             :use ((:instance not-include-rp-of-beta-reduce-term-arg=nil
                              (term (CAR (CDR (CDR (CAR TERM)))))
                              (keys (CAR (CDR (CAR TERM))))
                              (vals (CDR TERM))))
             :in-theory (e/d (beta-reduce-lambda-expr
                              is-lambda)
                             (acl2::beta-reduce-term
                              not-include-rp-of-beta-reduce-term-arg=nil)))))
  )||#

(defthm-valid-sc
  (defthm not-include-rp-means-valid-sc
    (implies (not (include-fnc term 'rp))
             (and (valid-sc term a)))
    :flag valid-sc)
  (defthm not-include-rp-means-valid-sc-lst
    (implies (not (include-fnc-subterms subterms 'rp))
             (and (valid-sc-subterms subterms a)))
    :flag valid-sc-subterms)
  :hints (("Goal" 
           :in-theory (e/d (is-rp
                            valid-sc-nt) ()))))

(defthm-valid-sc-nt
  (defthm not-include-rp-means-valid-sc-nt
    (implies (not (include-fnc term 'rp))
             (and (valid-sc-nt term a)))
    :flag valid-sc-nt)
  (defthm not-include-rp-means-valid-sc-nt-subterms
    (implies (not (include-fnc-subterms subterms 'rp))
             (and (valid-sc-nt-subterms subterms a)))
    :flag valid-sc-nt-subterms)
  :hints (("Goal" 
           :in-theory (e/d (is-rp
                            valid-sc-nt) ()))))

(defthm valid-sc-ex-from-rp
  (implies (valid-sc term a)
           (valid-sc (ex-from-rp term) a))
  :hints (("Goal"
           :induct (ex-from-rp term)
           :in-theory (e/d (ex-from-rp is-rp) ()))))

(defthm valid-sc-ex-from-rp-2
  (implies (EVAL-AND-ALL (CONTEXT-FROM-RP TERM NIL)
                         A)
           (equal (valid-sc (ex-from-rp term) a)
                  (valid-sc term a)))
  :hints (("Goal"
           :induct (ex-from-rp term)
           :in-theory (e/d (CONTEXT-FROM-RP
                            ex-from-rp
                            is-rp) ()))))

(defthm valid-sc-nil
  (and (VALID-SC NIL A)
       (VALID-SC-BINDINGS NIL A))
  :hints (("Goal"
           :in-theory (e/d (valid-sc
                            valid-sc-bindings) ()))))

(encapsulate
  nil

  (defthm extract-from-rp-pseudo-term-listp
    (implies (rp-termp term)
             (rp-termp (ex-from-rp TERM)))
    :hints (("Goal"
             :induct (ex-from-rp TERM)
             :in-theory (enable is-rp ex-from-rp))))

  (defthm extract-from-synp-pseudo-term-listp
    (implies (rp-termp term)
             (rp-termp (ex-from-synp TERM)))
    :hints (("Goal"
             :in-theory (enable is-synp extract-from-synp)))
    :rule-classes :forward-chaining)

  (local
   (defthmd pseudo-termp-lemma2
     (implies (rp-termp term)
              (not (equal term nil)))))

  (local
   (defthm stupid-lemma1
     (implies (and (rp-termp term)
                   (should-term-be-in-cons term term2))
              (and (ex-from-synp (ex-from-rp (cadr term)))))
     :instructions
     ((:in-theory (e/d (should-term-be-in-cons)
                       (ex-from-synp)))
      (:use (:instance pseudo-termp-lemma2
                       (term (ex-from-synp (ex-from-rp (cadr term))))))
      :promote (:demote 1)
      (:dv 1 1)
      (:rewrite pseudo-termp-extract-from-synp)
      (:change-goal nil t)
      (:rewrite extract-from-rp-pseudo-term-listp)
      (:change-goal nil t)
      (:change-goal nil t)
      :expand :s-prop (:demote 2)
      (:dive 1)
      :s :top
      :promote :prove
      :top :s)))

  (local
   (defthm stupid-lemma2
     (implies (and (rp-termp term)
                   (should-term-be-in-cons term term2))
              (and (ex-from-synp (ex-from-rp (caddr term)))))
     :instructions
     ((:in-theory (e/d (should-term-be-in-cons)
                       (ex-from-synp)))
      (:use (:instance pseudo-termp-lemma2
                       (term (ex-from-synp (ex-from-rp (caddr term))))))
      :promote (:demote 1)
      (:dv 1 1)
      (:rewrite pseudo-termp-extract-from-synp)
      (:change-goal nil t)
      (:rewrite extract-from-rp-pseudo-term-listp)
      (:change-goal nil t)
      (:change-goal nil t)
      :expand :s-prop (:demote 2)
      (:dive 1)
      :s :top
      :promote :prove
      :top :s)))

  (defthm psuedo-termp2-and-ex-form-synp&rp
    (implies (and (rp-termp term)
                  (should-term-be-in-cons term term2))
             (and (ex-from-synp (ex-from-rp (cadr term)))
                  (ex-from-synp (ex-from-rp (caddr term)))))
    :hints (("goal"
             :use ((:instance stupid-lemma2)
                   (:instance stupid-lemma1))
             :in-theory (e/d (stupid-lemma2 stupid-lemma1)
                             (ex-from-synp)))))

  (defthm is-if-rp-termp
    (implies (and (rp-termp term)
                  (is-if term))
             (and (rp-termp (cadr term))
                  (rp-termp (caddr term))
                  (rp-termp (cadddr term))))
    :hints (("Goal" :in-theory (enable is-if)))))

(defthm rp-termp-implies-subterms
  (implies (and (consp term)
                (not (quotep term))
                (rp-termp term))
           (rp-term-listp (cdr term))))

(defthm valid-sc-subterms-append
  (equal (valid-sc-subterms (append x y) a)
         (and (valid-sc-subterms x a)
              (valid-sc-subterms y a)))
  :hints (("Goal"
           :in-theory (e/d (valid-sc
                            append) ()))))



(defthm valid-rulep-implies-valid-sc
  (implies (and (valid-rulep rule)
                (rp-evl (rp-hyp rule) a))
           (valid-sc-nt (rp-rhs rule) a))
  :hints (("Goal"
           :use (:instance valid-rulep-sk-necc)
           :in-theory (e/d (valid-rulep)
                           (valid-sc
                            rp-rhs
                            rp-hyp
                            valid-sc-nt
                            VALID-RULEP-SK
                            valid-rulep-sk-necc
                            rule-syntaxp)))))

(defthm-ext-side-conditions
  (defthm not-include-rp-EXT-SIDE-CONDITIONS
    (implies (NOT (INCLUDE-FNC TERM 'RP))
             (equal (EXT-SIDE-CONDITIONS TERM context)
                    nil))
    :flag ext-side-conditions)
  (defthm not-include-rp-EXT-SIDE-CONDITIONS-subterms
    (implies (NOT (INCLUDE-FNC-SUBTERMS subterms 'RP))
             (equal (ext-side-conditions-subterms subterms context)
                    nil))
    :flag ext-side-conditions-subterms)
  :hints (("Goal"
           :in-theory (e/d (is-rp
                            ext-side-conditions-subterms
                            ext-side-conditions)
                           (EXTRACT-FROM-RP-WITH-CONTEXT)))))

(encapsulate
  nil
  (defthm not-include-synp
    (implies (not (include-fnc term 'synp))
             (not (is-synp term)))
    :hints (("Goal" :in-theory (enable is-synp))))

  (defthm not-include-rp
    (implies (not (include-fnc term 'rp))
             (not (is-rp term)))
    :hints (("Goal" :in-theory (enable is-rp))))

  (defthm not-include-ex-from-rp
    (implies (not (include-fnc term fnc))
             (not (include-fnc (ex-from-rp term) fnc)))
    :hints (("Goal"
             :in-theory (enable ex-from-rp)
             :induct (ex-from-rp term))))

  (defthm ex-from-rp-put-term-in-cons
    (equal (ex-from-rp (put-term-in-cons term))
           (put-term-in-cons term))
    :hints (("Goal" :in-theory (enable put-term-in-cons ex-from-rp))))

  (defthm quotep-term-with-ex-from-rp
    (implies (quotep term)
             (quotep (EX-FROM-RP TERM)))
    :hints (("Goal" :in-theory (enable ex-from-rp))))

  (defthm quotep-term-with-ex-from-synp
    (implies (quotep term)
             (quotep (EX-FROM-synp TERM)))
    :hints (("Goal" :in-theory (enable ex-from-synp))))

  (defthm ex-from-synp-put-term-in-cons
    (equal (ex-from-synp (put-term-in-cons term))
           (put-term-in-cons term))
    :hints (("Goal" :in-theory (enable put-term-in-cons ex-from-synp
                                       is-synp))))

  (defthm should-term-be-in-cons-lemma2
    (implies (should-term-be-in-cons lhs1 term1)
             (and (not (should-term-be-in-cons t2 lhs1))
                  (not (should-term-be-in-cons term1 t3))))
    :hints (("Goal" :in-theory (enable should-term-be-in-cons))))

  (defthm should-term-be-in-cons-lemma3
    (not (should-term-be-in-cons lhs (PUT-TERM-IN-CONS TERM)))
    :hints (("Goal" :in-theory (enable put-term-in-cons
                                       should-term-be-in-cons))))

  (defthm car-put-term-in-cons
    (equal (car (put-term-in-cons term))
           'cons)
    :hints (("Goal" :in-theory (enable put-term-in-cons))))

  (defthmd should-term-be-in-cons-lemma4
    (implies (should-term-be-in-cons lhs term)
             (equal (car lhs)
                    'cons))
    :hints (("Goal" :in-theory (enable should-term-be-in-cons))))

  (defthm is-synp-put-term-cons
    (NOT (IS-SYNP (PUT-TERM-IN-CONS term)))
    :hints (("Goal" :in-theory (enable put-term-in-cons is-synp))))

  (defthm ex-from-rp-cons-cons
    (equal (ex-from-rp (cons 'cons x))
           (cons 'cons x))
    :hints (("Goal" :in-theory (enable ex-from-rp
                                       is-rp))))

  (defthm ex-from-rp-put-term-cons
    (equal (EX-FROM-RP (PUT-TERM-IN-CONS term))
           (put-term-in-cons term))
    :hints (("Goal" :in-theory (enable put-term-in-cons
                                       is-rp
                                       ex-from-rp))))

  (defthm RP-TERM-LISTP-CDR-PUT-TERM-IN-CONS
    (RP-TERM-LISTP (CDR (PUT-TERM-IN-CONS term)))
    :hints (("Goal" :in-theory (enable PUT-TERM-IN-CONS)))))

#|(encapsulate
  nil
  (local
   (defthm lemma1
     (implies (subtermp-lst x z)
              (subtermp-lst x (cons y z)))))
  (defthm subtermp-lst-of-the-same
    (subtermp-lst x x)))||#

;; (defthm subtermp-ex-from-rp
;;   (subtermp (ex-from-rp term) term)
;;   :hints (("Goal" :in-theory (enable is-rp ex-from-rp)
;;            :induct (ex-from-rp term))))

;; (defthm subtermp-of-the-same
;;   (subtermp term term))

(encapsulate
  nil

  (local
   (defthm subsetp-lemma
     (implies (subsetp x y)
              (subsetp x (cons s y)))))

  (defthm context-from-subsetp
    (subsetp context (context-from-rp term context) )
    :hints (("Goal" :in-theory (enable context-from-rp)
             :induct (context-from-rp term context)))))

(encapsulate
  nil

  (local
   (defthm lemma1
     (implies
      (valid-rulesp lst)
      (RULE-LIST-SYNTAXP lst))
     :hints (("Goal"
              :in-theory (e/d (rule-list-syntaxp)
                              (valid-rulep-sk
                               rule-syntaxp))))))

  (local
   (defthm lemma2
     (IMPLIES (AND (VALID-RULES-LIST-LISTP alist))
              (RULE-LIST-LIST-SYNTAXP alist))
     :hints (("Goal"
              :in-theory (e/d () (rule-syntaxp
                                  valid-rulep-sk))))))

  (defthm valid-rules-alistp-implies-RULES-ALISTP
    (implies (valid-rules-alistp rules-alist)
             (rules-alistp rules-alist))
    :otf-flg t
    :hints (("Goal"
             :in-theory (e/d (valid-rules-alistp
                              RULE-LIST-LIST-SYNTAXP
                              VALID-RULES-LIST-LISTP
                              valid-rulesp
                              rules-alistp
                              valid-rulep)
                             (valid-rulep-sk
                              rule-syntaxp))))))

(defthm VALID-RULESP-implies-RULE-LIST-SYNTAXP
  (implies (valid-rulesp rules)
           (rule-list-syntaxp rules))
  :hints (("Goal"
           :in-theory (e/d (valid-rulesp
                            rule-list-syntaxp)
                           ((:definition falist-consistent)
                            (:definition rp-termp)
                            rule-syntaxp
                            (:definition subsetp-equal))))))

(defthm VALID-SC-and-is-if
  (implies (and (is-if term)
                (valid-sc term a))
           (and (valid-sc (cadr term) a)
                (if (rp-evlt (cadr term) a)
                    (valid-sc (caddr term) a)
                  (valid-sc (cadddr term) a))))
  :rule-classes :forward-chaining
  :hints (("Goal"
           :expand (valid-sc term a)
           :in-theory (e/d (is-if)
                           (valid-sc)))))



(defthm valid-rules-subsetp
  (implies (and (valid-rulesp rules)
                (subsetp subrules rules))
           (valid-rulesp subrules))
  :hints (("Goal"
           :in-theory (disable valid-rulep))))

(encapsulate
  nil
  (local
   (defthm rp-evl-of-beta-reduce-lambda-expr-lemma
     (implies (AND (ACL2::LAMBDA-EXPR-P acl2::TERM)
                   (PSEUDO-TERMP acl2::TERM))
              (equal (rp-evl (acl2::beta-reduce-lambda-expr acl2::term) acl2::a1)
                     (rp-evl acl2::term acl2::a1)))
     :hints (("Goal"
              :use ((:functional-instance
                     acl2::beta-eval-to-beta-reduce-lambda-expr
                     (acl2::beta-eval rp-evl)
                     (acl2::beta-eval-list rp-evl-lst)))
              :in-theory (e/d (is-lambda
                               rp-evl-of-fncall-args)
                              (acl2::beta-eval-to-beta-reduce-lambda-expr
                               ))))))

  (defthm rp-evl-of-beta-reduce-lambda-expr
    (implies (AND (rp-termp term)
                  (is-lambda term))
             (equal (rp-evl (acl2::beta-reduce-lambda-expr term) a)
                    (rp-evl term a)))
    :hints (("Goal"
             :in-theory (e/d (is-lambda) ()))))

  #|(defthm rp-termp-of-beta-reduce-lambda-expr
  (implies (and (rp-termp term)
  (is-lambda term))
  (rp-termp (acl2::beta-reduce-lambda-expr term))))||#

  #|(defthm ALL-FALIST-CONSISTENT-of-beta-reduce-lambda-expr
  (implies (and (rp-termp term)
  (all-falist-consistent term)
  (is-lambda term))
  (all-falist-consistent (acl2::beta-reduce-lambda-expr term))))||#

  #|(defthm rp-syntaxp-of-beta-reduce-lambda-expr
  (implies (and (rp-termp term)
  (rp-syntaxp term)
  (is-lambda term))
  (rp-syntaxp (acl2::beta-reduce-lambda-expr term))))||#)

#|(defthm valid-sc-caddr-term
  (implies (and (valid-sc term a)
                (not (equal (car term) 'if))
                (not (equal (car term) 'quote))
                (consp term)
                (consp (cdr term))
                (consp (cddr term)))
           (VALID-SC (CADDR TERM) A))
  :hints (("Goal"
           :expand ((VALID-SC TERM A))
           :in-theory (e/d (valid-sc
                            is-if
                            is-rp)
                           ()))))||#



#|(defthm valid-sc-cadr-ex-from-rp
  (IMPLIES (AND
              (CONSP (EX-FROM-RP TERM))
              (Not (EQUAL (CAR (EX-FROM-RP TERM)) 'if))
              (Not (EQUAL (CAR (EX-FROM-RP TERM)) 'quote))
              (CONSP (CDR (EX-FROM-RP TERM)))
              (VALID-SC TERM A))
           (VALID-SC (CADR (EX-FROM-RP TERM)) A))
  :hints (("Goal"
           :in-theory (e/d (ex-from-rp
                            is-if
                            is-rp) ()))))||#






(defthm valid-sc-ex-from-falist
  (implies (valid-sc x a)
           (valid-sc (ex-from-falist x) a))
  :rule-classes :rewrite
  :hints (("Goal"
           :expand (ex-from-falist x)
           :in-theory (e/d (is-rp
                            is-if) ()))))

(defthm valid-sc-ex-from-falist-replace
  (implies (rp-termp x)
           (equal (valid-sc (ex-from-falist x) a)
                  (valid-sc x a)))
  :rule-classes :rewrite
  :hints (("Goal"
           :expand (ex-from-falist x)
           :in-theory (e/d (is-rp
                            is-if) ()))))

(defthm rp-evl-of-ex-from-falist
  (equal (rp-evl (ex-from-falist x) a)
         (rp-evl x a))
  :hints (("Goal"
           :Expand (ex-from-falist x)
           :in-theory (e/d () ()))))



(defthm eval-and-all-nt-is-eval-and-all
  (implies (not (include-fnc-subterms lst 'list))
           (equal (eval-and-all-nt lst a)
                  (eval-and-all lst a))))

(defthm EVAL-AND-ALL-NT-of-context-from-rp
  (implies (and (not (include-fnc-subterms context 'list))
                (not (include-fnc term 'list)))
           (equal (EVAL-AND-ALL-NT (CONTEXT-FROM-RP TERM context) A)
                  (EVAL-AND-ALL (CONTEXT-FROM-RP TERM context) A)))
  :hints (("Goal"
           :induct (CONTEXT-FROM-RP TERM context)
           :in-theory (e/d (context-from-rp
                            eval-and-all-nt-is-eval-and-all
                            is-rp
                            rp-evl-of-fncall-args)
                           ()))))
         
(defthm-valid-sc
  (defthm valid-sc-nt-is-valid-sc
    (implies (not (include-fnc term 'list))
             (equal (valid-sc-nt term a)
                    (valid-sc term a)))
    :flag valid-sc)
  (defthm valid-sc-nt-subterms-valid-sc-subterms
    (implies (not (include-fnc-subterms subterms 'list))
             (equal (valid-sc-nt-subterms subterms a)
                    (valid-sc-subterms subterms a)))
    :flag valid-sc-subterms)
  :hints (("Goal"
           :in-theory (e/d (EVAL-AND-ALL-NT-of-context-from-rp) ()))))




  
(defthm rp-evl-of-trans-list-lemma
  (equal (rp-evl (trans-list lst) a)
         (rp-evl-of-trans-list lst a))
  :hints (("Goal"
           :do-not-induct t
           :induct (trans-list lst)
           :in-theory (e/d () ()))))



(local
 (defun two-cdr-induct (x y)
   (if (or (atom x)
           (atom y))
       nil
     (acons (car x)
            (car y)
            (two-cdr-induct (cdr x) (cdr y))))))

(local
 (defthm rp-evl-of-trans-list-lemma-3
   (implies (and (not (consp x))
                 (not (rp-evl-lst y a)))
            (not (rp-evl-of-trans-list y a)))))


(defthm rp-evl-of-trans-list-lemma-2
  (implies (equal (rp-evl-lst x a1)
                  (rp-evl-lst y a2))
           (equal (equal (rp-evl-of-trans-list x a1)
                         (rp-evl-of-trans-list y a2))
                  t))
  :otf-flg t
  :hints (("goal"
           :do-not-induct t
           :induct (two-cdr-induct x y)
           :in-theory (e/d (rp-evl-of-trans-list) ()))))

(defthm consp-of-RP-EVL-OF-TRANS-LIST
  (equal (CONSP (RP-EVL-OF-TRANS-LIST lst A))
         (consp lst))
  :hints (("Goal"
           :in-theory (e/d (RP-EVL-OF-TRANS-LIST) ()))))

(defthm RP-EVL-OF-TRANS-LIST-nil
  (equal (RP-EVL-OF-TRANS-LIST nil A)
         nil)
  :hints (("Goal"
           :in-theory (e/d (RP-EVL-OF-TRANS-LIST) ()))))

(in-theory (disable rp-evl-of-trans-list))
