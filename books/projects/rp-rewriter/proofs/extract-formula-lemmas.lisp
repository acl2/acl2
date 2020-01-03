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


(defthm remove-warning-from-rule-syntaxp
  (implies (syntaxp (not (equal warning ''nil)))
           (equal (rule-syntaxp rule :warning warning)
                  (rule-syntaxp rule :warning nil)))
  :hints (("Goal"
           :in-theory (e/d (rule-syntaxp) ()))))



(local
 ;;local funcitons for local lemmas
 (encapsulate
   nil

   (local
    (in-theory (disable (:definition rp-termp)
                        (:definition valid-sc-nt)
                        (:rewrite not-include-rp-means-valid-sc)
                        (:rewrite car-of-ex-from-rp-is-not-rp)
                        (:definition falist-consistent)
                        (:rewrite default-cdr)
                        (:rewrite acl2::o-p-o-infp-car)
                        (:rewrite is-if-rp-termp)
                        (:rewrite default-car)
                        (:rewrite rp-termp-caddr)
                        (:rewrite is-rp-pseudo-termp)
                        (:rewrite rp-termp-cadddr)
                        (:type-prescription o-p)
                        (:rewrite rp-evl-of-rp-equal2)
                        (:rewrite rp-evl-of-rp-equal-loose)
                        (:rewrite rp-evl-of-rp-equal)
                        (:rewrite acl2::o-p-def-o-finp-1)
                        (:rewrite rp-termp-cadr)
                        rule-syntaxp
                        rp-trans
                        ex-from-synp-lemma1
                        rp-trans-lst
                        evl-of-extract-from-rp-2
                        (:type-prescription is-rp$inline))))

   (defmacro valid-rulep-with-a (rule a)
     `(valid-rulep-sk-body ,rule ,a))

   (defun valid-rulesp-with-a (rules a)
     (if (atom rules)
         t
       (and (rule-syntaxp (car rules))
            (valid-rulep-with-a (car rules) a)
            (valid-rulesp-with-a (cdr rules) a))))

   #|(local
   (defthm forced-rp-trans-is-term-when-list-is-absent
   (implies (force (not (include-fnc term 'list)))
   (equal (rp-evl (rp-trans term) a)
   (rp-evl term a)))))||#

   (local
    (in-theory (e/d (rule-syntaxp-implies rule-syntaxp)
                    (rp-hyp rp-lhs rp-rhs
                            formulas-to-rules
                            valid-rulesp-with-a
                            eval-and-all-nt
                            rp-trans
                            rp-trans-lst))))

   (defthm correctness-of-formulas-to-rules
     (implies (eval-and-all-nt formulas a)
              (valid-rulesp-with-a (formulas-to-rules rune rule-new-synp warning formulas) a))
     :hints (("Goal"
;:expand ((:free (warning x y) (rule-syntaxp-fn (cons x y) warning)))
              :in-theory (e/d (formulas-to-rules
                               valid-rulesp-with-a
                               eval-and-all-nt
                               rp-lhs rp-rhs rp-hyp)
                              (rule-syntaxp
                               RP-EVL-OF-VARIABLE
                               EX-FROM-RP-LEMMA1
                               (:TYPE-PRESCRIPTION IS-RP-LOOSE$INLINE)))
              )))

   (defun-sk eval-and-all-sk ( formulas)
     (forall a
             (eval-and-all-nt formulas a)))

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
     (equal (eval-and-all-nt (not-to-equal-nil-list new-terms) a)
            (eval-and-all-nt new-terms a))
     :hints (("Goal"
              :in-theory (e/d (not-to-equal-nil-list) ())))))

  (local
   (defthm rp-evl-lst-of-if-to-and-list
     (implies (rp-evl term a)
              (eval-and-all-nt (if-to-and-list term) a))
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
     (implies (and (eval-and-all-nt qs a))
              (eval-and-all-nt (make-rule-better-aux1 p qs) a))))

  (local
   (defthm make-rule-better-aux1-lemma2
     (implies (and (not (rp-evl p a))
                   (consp qs))
              (eval-and-all-nt (make-rule-better-aux1 p qs) a))))

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
             (eval-and-all-nt (make-formula-better formula) a))
    :hints (("Goal"
             :do-not-induct t
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

(local
 (encapsulate nil
   (make-flag insert-iff-to-force :defthm-macro-name
              defthm-insert-iff-to-force)


   (defthm-insert-iff-to-force
     (defthm rp-evl-of-insert-off-to-force-lemma
       (if iff-flg
           (iff (rp-evl (insert-iff-to-force term iff-flg) a)
                (rp-evl term a))
         (equal (rp-evl (insert-iff-to-force term iff-flg) a)
                (rp-evl term a)))
       :flag insert-iff-to-force)
     (defthm rp-evl-lst-of-insert-off-to-force-lst
       (equal (rp-evl-lst (insert-iff-to-force-lst lst) a)
              (rp-evl-lst lst a))
       :flag insert-iff-to-force-lst)
     :hints (("Goal"
              :in-theory (e/d (RP-EVL-OF-FNCALL-ARGS)
                              ((:definition rp-termp)
                               (:definition falist-consistent)
                               (:rewrite rp-evl-of-rp-equal2)
                               (:definition falist-consistent-aux)
                               (:rewrite acl2::o-p-o-infp-car)
                               (:type-prescription insert-iff-to-force))))))

   (defthm rp-evl-of-insert-off-to-force
     (and (iff (rp-evl (insert-iff-to-force term t) a)
               (rp-evl term a))
          (equal (rp-evl (insert-iff-to-force term nil) a)
                 (rp-evl term a)))
     :hints (("Goal"
              :use ((:instance rp-evl-of-insert-off-to-force-lemma
                               (iff-flg t))
                    (:instance rp-evl-of-insert-off-to-force-lemma
                               (iff-flg nil)))
              :in-theory (e/d () ()))))))

(encapsulate
  nil

  (local
   (defthm correctness-of-formulas-to-rules2
     (implies (eval-and-all-sk formulas)
              (valid-rulesp-with-a
               (formulas-to-rules rune rule-new-synp warning formulas) a))
     :hints (("Goal"
              :use ((:instance correctness-of-formulas-to-rules)
                    (:instance eval-and-all-sk-necc))
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
              :expand ((eval-and-all-sk NIL)
                       (eval-and-all-sk (cdr formulas)))
              :use ((:instance eval-and-all-sk-necc
                               (a (EVAL-AND-ALL-SK-WITNESS (CDR FORMULAS)))))
              :in-theory (e/d () (eval-and-all-sk-necc
                                  eval-and-all-sk))))))

  (local
   (defthm correctness-of-formulas-to-rules3
     (implies (eval-and-all-sk formulas)
              (valid-rulesp (formulas-to-rules rune rule-new-synp warning formulas)))
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
             (valid-rulesp (custom-rewrite-with-meta-extract rule-name
                                                             rule-new-synp warning state)))
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

(defthm valid-sc-nt-subtermsof-ex-from-rp
  (implies (valid-sc-nt term a)
           (valid-sc-nt (ex-from-rp term) a))
  :hints (("Goal"
;:induct (ex-from-rp-loose term)
           :induct (ex-from-rp term)
           :do-not-induct t
           :in-theory (e/d (valid-sc-nt
                            is-rp
                            is-if
                            ex-from-rp
                            ex-from-rp-loose
                            is-rp-loose)
                           ((:DEFINITION RP-TERMP))))))

(encapsulate
  nil
  (local
   (defthm valid-sc-nt-single-step-lemma
     (implies (EVAL-AND-ALL-nt (CONTEXT-FROM-RP TERM NIL)
                            A)
              (EQUAL (valid-sc-nt (EX-FROM-RP term) A)
                     (valid-sc-nt term A)))
     :hints (("Goal"
              :in-theory (e/d (is-if
                               is-rp) ())))))

  (local
   (defthm valid-sc-nt-single-step-lemma2
     (implies (and (EVAL-AND-ALL-nt (CONTEXT-FROM-RP TERM NIL) A)
                   (IS-RP TERM))
              (EVAL-AND-ALL-nt (CONTEXT-FROM-RP (CADDR TERM) NIL) A))
     :hints (("Goal"
              :in-theory (e/d (is-if
                               EVAL-AND-ALL-nt
                               context-from-rp
                               is-rp) ())))))

  (local
   (defthm valid-sc-nt-single-step-lemma3-lemma
     (implies (not (equal fnc 'quote))
              (equal (RP-EVL (LIST fnc (EX-FROM-RP term)) A)
                     (RP-EVL (LIST fnc term) A)))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d (is-if
                               rp-evl-of-ex-from-rp
                               EVAL-AND-ALL-nt
                               rp-evl-of-fncall-args
                               is-rp) ())))))

  (local
   (defthm valid-sc-nt-single-step-lemma3
     (implies (and (IS-RP TERM)
                   (NOT (RP-EVL (LIST (CADR (CADR TERM)) (CADDR TERM)) A)))
              (not (EVAL-AND-ALL-nt (CONTEXT-FROM-RP TERM NIL) A)))
     :hints (("Goal"
              :do-not-induct t
              :expand (CONTEXT-FROM-RP TERM NIL)
              :in-theory (e/d (is-if
                               EVAL-AND-ALL-nt
                               rp-evl-of-fncall-args
                               is-rp)
                              (EX-FROM-RP-LEMMA1))))))

  (local
   (defthm valid-sc-nt-single-step-lemma4
     (implies (and (IS-RP TERM)
                   (NOT (RP-EVL (LIST (CADR (CADR TERM)) (CADDR TERM)) A)))
              (not (EVAL-AND-ALL-nt (CONTEXT-FROM-RP TERM NIL) A)))
     :hints (("Goal"
              :do-not-induct t
              :expand (CONTEXT-FROM-RP TERM NIL)
              :in-theory (e/d (is-if
                               rp-evl-of-fncall-args
                               EVAL-AND-ALL-nt
                               is-rp)
                              (EX-FROM-RP-LEMMA1))))))

  (local
   (defthm valid-sc-nt-single-step-lemma5
     (implies (and (RP-EVL (LIST (CADR (CADR TERM)) (CADDR TERM))
                           A)
                   (IS-RP TERM)
                   (NOT (EVAL-AND-ALL-nt (CONTEXT-FROM-RP TERM NIL)
                                      A)))
              (NOT (EVAL-AND-ALL-nt (CONTEXT-FROM-RP (caddr TERM) NIL)
                                 A)))
     :hints (("Goal"
              :in-theory (e/d (is-rp EVAL-AND-ALL-nt
                                     rp-evl-of-fncall-args
                                     context-from-rp)
                              (EX-FROM-RP-LEMMA1))))))

  (local
   (defthm valid-sc-nt-single-step-lemma6
     (implies (and (NOT (EVAL-AND-ALL-nt (CONTEXT-FROM-RP TERM NIL)
                                      A)))
              (NOT (valid-sc-nt term A)))
     :hints (("Goal"
              :in-theory (e/d (is-rp EVAL-AND-ALL-nt
                                     is-if
                                     context-from-rp) ())))))

  (defthmd valid-sc-nt-single-step
    (implies (and (rp-termp term)
                  (is-rp term))
             (equal (valid-sc-nt term a)
                    (and (RP-EVL `(,(cadr (cadr term)) ,(caddr term))  a)
                         (valid-sc-nt (caddr term) a))))
    :hints (("Goal"
             :do-not-induct t
             :expand ((valid-sc-nt TERM A))
             :in-theory (e/d (is-rp-implies-fc
                              is-if-implies-fc)
                             ())))))

(encapsulate
  nil

  (local
   (use-measure-lemmas t))

  (make-flag attach-sc :defthm-macro-name defthm-attach-sc)


  (defthm-attach-sc
    (defthm rp-evlt-of-attach-sc
      (equal (rp-evlt (attach-sc term sc-type sc-term) a)
             (rp-evlt term a))
      :flag attach-sc)
    (defthm rp-evlt-lst-of-attach-sc-lst
      (equal (rp-evlt-lst (attach-sc-lst lst sc-type sc-term) a)
             (rp-evlt-lst lst a))
      :flag attach-sc-lst)
    :otf-flg t
    :hints (("Goal"
             :expand ((rp-trans term)
                      (RP-TRANS SC-TERM))
             :in-theory (e/d (rp-evl-of-fncall-args
                              rp-trans
                              rp-trans-lst) ()))))
  
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
               (not (equal sc-type 'list))
               (IS-RP (LIST 'RP
                            (LIST 'QUOTE SC-TYPE)
                            SC-TERM))
               (RP-EVL (LIST SC-TYPE SC-TERM) A))
              (valid-sc-nt (LIST 'RP (LIST 'QUOTE SC-TYPE) SC-TERM)
                           A))
     :hints (("Goal"
              :in-theory (e/d (IS-RP-IMPLIES-FC
                               ;; rp-evl-constraint-0
                               CONTEXT-FROM-RP
                               eval-and-all-nt
                               ex-from-rp
                               is-rp
                               is-if)
                              (VALID-SC-EX-FROM-RP-2))))))

  (local
   (defthm lemma1-v2
     (IMPLIES (AND
               (NOT (CONSP SC-TERM))
               (not (equal sc-type 'list))
               (IS-RP (LIST 'RP
                            (LIST 'QUOTE SC-TYPE)
                            SC-TERM))
               (RP-EVLt (LIST SC-TYPE SC-TERM) A))
              (valid-sc (LIST 'RP (LIST 'QUOTE SC-TYPE) SC-TERM)
                           A))
     :hints (("Goal"
              :in-theory (e/d (IS-RP-IMPLIES-FC
                               ;; rp-evl-constraint-0
                               CONTEXT-FROM-RP
                               eval-and-all-nt
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
     (implies (and (rp-termp term)
                   (not (is-rp term)))
              (equal (ex-from-rp (cons (car term) rest))
                     (cons (car term) rest)))
     :hints (("Goal"
              :in-theory (e/d (ex-from-rp
                               is-rp) ())))))

  (local
   (defthm context-from-rp-lemma1
     (implies (and (rp-termp term)
                   (not (is-rp term)))
              (equal (context-from-rp (cons (car term) rest) context)
                     context))
     :hints (("Goal"
              :in-theory (e/d (context-from-rp
                               is-rp) ())))))
  (local
   (defthm lemma10
     (implies (and (rp-termp term)
                   (not (is-rp term)))
              (not (equal (car term) 'rp)))))

  (local
   (defthm lemma11
     (and (implies (not (is-if term))
                   (not (IS-IF (CONS (CAR TERM)
                                     (ATTACH-SC-LST (CDR TERM)
                                                    SC-TYPE SC-TERM)))))
          (implies (and (not (is-rp term))
                        (rp-termp term))
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
                   (NOT (EQUAL SC-TYPE 'falist))
                   (NOT (EQUAL SC-TYPE 'RP))))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))

  (local
   (defthm lemma13
     (implies (and (eval-and-all-nt (context-from-rp term nil)
                                    a)
                   (is-rp term))
              (eval-and-all-nt (context-from-rp (caddr term) nil)
                               a))
     :hints (("goal"
              :in-theory (e/d (is-rp
                               context-from-rp)
                              (ex-from-rp-lemma1))))))

  (local
   (defthm lemma13-v2
     (implies (and (eval-and-all (context-from-rp term nil)
                                    a)
                   (is-rp term))
              (eval-and-all (context-from-rp (caddr term) nil)
                               a))
     :hints (("goal"
              :in-theory (e/d (is-rp
                               context-from-rp)
                              (ex-from-rp-lemma1))))))


  (defthm valid-sc-nt-cadddr
    (IMPLIES (AND
              (CONSP term)
              (Not (EQUAL (CAR term) 'if))
              (Not (EQUAL (CAR term) 'rp))
              (Not (EQUAL (CAR term) 'quote))
              (CONSP (CDR term))
              (CONSP (CDdR term))
              (CONSP (CDddR term))
              (VALID-SC-nt TERM A))
             (VALID-SC-nt (CAdDdR term) A))
    :hints (("Goal"
             :do-not-induct t
             :expand ((VALID-SC-nt TERM A))
             :in-theory (e/d (is-if
                              is-rp)
                             ((:REWRITE LEMMA10)
                              (:DEFINITION RP-TERMP)
                              (:DEFINITION INCLUDE-FNC)
                              (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC-NT))))))

  (local
   (defthm lemma14
     (implies (and (valid-sc-nt term a)
                   (consp term)
                   (rp-termp term)
                   (not (eq (car term) 'quote))
                   (not (is-if term)))
              (valid-sc-nt-subterms (cdr term) a))
     :hints (("goal" 
              :do-not-induct t 
              :cases ((is-rp term))
              :in-theory (e/d (is-rp
                               valid-sc-nt-single-step)
                              (EX-FROM-RP-LEMMA1))))))

  (local
   (defthm lemma14-v2
     (implies (and (valid-sc term a)
                   (consp term)
                   (rp-termp term)
                   (not (eq (car term) 'quote))
                   (not (is-if term)))
              (valid-sc-subterms (cdr term) a))
     :hints (("goal" 
              :do-not-induct t 
              :cases ((is-rp term))
              :in-theory (e/d (is-rp
                               valid-sc-single-step)
                              (ex-from-rp-lemma1))))))

  #|(local
  (defthm lemma15
  (implies (and (RP-SYNTAXP TERM)
  (NOT (EQUAL (CAR TERM) 'QUOTE)))
  (RP-SYNTAXP-LST (CDR TERM)))
  :hints (("Goal"
  :cases ((is-rp term))
  :in-theory (e/d (is-rp) ())))))||#

  (local
   (defthm lemma16
     (implies (valid-sc-nt term a)
              (valid-sc-nt (EX-FROM-RP TERM) A))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :in-theory (e/d (VALID-SC-EX-FROM-RP-2) ())))))

  (local
   (defthm lemma16-v2
     (implies (valid-sc term a)
              (valid-sc (EX-FROM-RP TERM) A))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :in-theory (e/d (VALID-SC-EX-FROM-RP-2) ())))))


  (local
   (defthm is-rp-implies-lemma
     (implies (IS-RP (LIST 'RP
                             (LIST 'QUOTE SC-TYPE)
                             SC-TERM))
              (not (equal sc-type 'list)))
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))


  (local
   (defthm is-rp-of-if
     (not (is-rp (cons 'if x)))
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))


  (local
   (defthm is-rp-of-rp
     (NOT (IS-RP (LIST 'RP
                       (LIST 'RP
                             x
                             y)
                       z)))
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))
  
  (local
   (defthm lemma17
     (implies (and (eval-and-all-nt (context-from-rp term nil) a)
                   (rp-termp term)
                   (not (is-rp sc-term))
                   (is-rp (LIST 'RP (LIST 'QUOTE SC-TYPE) SC-TERM))
                   (rp-evl `(,sc-type ,sc-term) a))
              (eval-and-all-nt (context-from-rp (attach-sc term sc-type sc-term)
                                                nil)
                               a))
     :hints (("Goal"
              :expand ((ATTACH-SC SC-TERM SC-TYPE SC-TERM)
                       (ATTACH-SC TERM SC-TYPE SC-TERM)

                       )
              :cases ((equal term sc-term)
                      (is-rp term)
                      (consp term))
              :in-theory (e/d (eval-and-all-nt
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
                   (NOT (EQUAL (CAR TERM) 'quote))
                   (not (EQUAL TERM SC-TERM))
                   (valid-sc-nt-subterms (ATTACH-SC-LST (CDR TERM)
                                                        SC-TYPE SC-TERM)
                                         A)
                   (valid-sc-nt TERM A)
                   (not (is-rp sc-term))
                   (rp-termp TERM)
;   (NOT (EQUAL (CAR TERM) 'IF))
;  (NOT (INCLUDE-FNC-SUBTERMS (CDR TERM) 'IF))
                   (IS-RP (LIST 'RP
                                (LIST 'QUOTE SC-TYPE)
                                SC-TERM))
                   (RP-EVL (LIST SC-TYPE SC-TERM) A))
              (valid-sc-nt (CONS (CAR TERM)
                                 (ATTACH-SC-LST (CDR TERM)
                                                SC-TYPE SC-TERM))
                           A))
;:otf-flg t
     :hints (("Goal"
              :expand ((valid-sc-nt TERM A)
                       (ATTACH-SC-LST (CDDR TERM)
                                      SC-TYPE SC-TERM)
                       (ATTACH-SC-LST (CDR TERM)
                                      SC-TYPE SC-TERM)
                       (EX-FROM-RP (LIST 'RP
                                         (CADR TERM)
                                         (ATTACH-SC (CADDR TERM)
                                                    SC-TYPE SC-TERM)))
                       (valid-sc-nt (LIST 'RP
                                          (CADR TERM)
                                          (ATTACH-SC (CADDR TERM)
                                                     SC-TYPE SC-TERM))
                                    A))
              :in-theory (e/d (IS-RP-IMPLIES-FC
                               is-if
                               ;;is-rp
                               eval-and-all-nt
                               rp-evl-of-fncall-args
                               RP-EVL-lst-of-cons
                               CONTEXT-FROM-RP)
                              (VALID-SC-EX-FROM-RP-2
                               EX-FROM-RP-LEMMA1
                               valid-sc-nt))))))

  (local
   (defthm lemma19
     (IMPLIES (AND
               (CONSP SC-TERM)
               ;(case-split (NOT (EQUAL (CAR SC-TERM) 'QUOTE)))
               (valid-sc-nt-subterms (ATTACH-SC-LST (CDR SC-TERM)
                                                    SC-TYPE SC-TERM)
                                     A)
               (valid-sc-nt SC-TERM A)
               (rp-termp SC-TERM)
;   (NOT (EQUAL (CAR SC-TERM) 'IF))
;   (NOT (INCLUDE-FNC-SUBTERMS (CDR SC-TERM)
;                             'IF))
               (case-split (is-rp sc-term))
               (not (is-rp sc-term))
               (IS-RP (LIST 'RP
                            (LIST 'QUOTE SC-TYPE)
                            SC-TERM))
               (RP-EVL (LIST SC-TYPE SC-TERM) A))
              (valid-sc-nt (LIST 'RP
                                 (LIST 'QUOTE SC-TYPE)
                                 (CONS (CAR SC-TERM)
                                       (ATTACH-SC-LST (CDR SC-TERM)
                                                      SC-TYPE SC-TERM)))
                           A))
     :hints (("Goal"
              :expand ((valid-sc-nt (LIST 'RP
                                          (LIST 'QUOTE SC-TYPE)
                                          (LIST 'RP
                                                (CADR SC-TERM)
                                                (ATTACH-SC (CADDR SC-TERM)
                                                           SC-TYPE SC-TERM)))
                                    A)

                       (ATTACH-SC-LST (CDR SC-TERM)
                                      SC-TYPE SC-TERM)
                       (valid-sc-nt (LIST 'RP
                                          (CADR SC-TERM)
                                          (ATTACH-SC (CADDR SC-TERM)
                                                     SC-TYPE SC-TERM))
                                    A)
                       (valid-sc-nt SC-TERM A)
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

                               eval-and-all-nt
                               rp-evl-of-fncall-args
                               RP-EVL-lst-of-cons
                               CONTEXT-FROM-RP)
                              (VALID-SC-EX-FROM-RP-2
                               EX-FROM-RP-LEMMA1
                               is-rp
                               valid-sc-nt))))))



  (local
   (defthm rp-evlt-lemma20
     (implies (and (equal (rp-evlt-lst lst1 a)
                          (rp-evlt-lst lst2 a))
                   (not (equal fn 'quote)))     
              (equal (rp-evlt (cons fn lst1) a)
                     (rp-evlt (cons fn lst2) a)))
     :hints (("Goal"
              :expand ((RP-TRANS (CONS FN LST1))
                       (RP-TRANS (CONS FN LST2)))
              :in-theory (e/d (rp-evl-of-fncall-args) ())))))

  (local
   (defthm rp-evl-lemma20
     (implies (and (equal (rp-evl-lst lst1 a)
                          (rp-evl-lst lst2 a))
                   (not (equal fn 'quote))
                   )     
              (equal (rp-evl (cons fn lst1) a)
                     (rp-evl (cons fn lst2) a)))
     :hints (("Goal"
              :expand ((RP-TRANS (CONS FN LST1))
                       (RP-TRANS (CONS FN LST2)))
              :in-theory (e/d (rp-evl-of-fncall-args) ())))))
  
  
  
  (local
   (defthm lemma20
     (IMPLIES (AND
               (CONSP SC-TERM)
               (case-split (NOT (EQUAL (CAR SC-TERM) 'QUOTE)))
               (valid-sc-nt-subterms (ATTACH-SC-LST (CDR SC-TERM)
                                                    SC-TYPE SC-TERM)
                                     A)
               (valid-sc-nt SC-TERM A)
               (rp-termp SC-TERM)
               (case-split (NOT (is-if sc-term)))
; (NOT (INCLUDE-FNC-SUBTERMS (CDR SC-TERM)
;                           'IF))
               (not (is-rp sc-term))
               (IS-RP (LIST 'RP
                            (LIST 'QUOTE SC-TYPE)
                            SC-TERM))
               (RP-EVL (LIST SC-TYPE SC-TERM) A))
              (valid-sc-nt (LIST 'RP
                                 (LIST 'QUOTE SC-TYPE)
                                 (CONS (CAR SC-TERM)
                                       (ATTACH-SC-LST (CDR SC-TERM)
                                                      SC-TYPE SC-TERM)))
                           A))
     :hints (("Goal"
              :expand ((valid-sc-nt (LIST 'RP
                                          (LIST 'QUOTE SC-TYPE)
                                          (CONS (CAR SC-TERM)
                                                (ATTACH-SC-LST (CDR SC-TERM)
                                                               SC-TYPE SC-TERM)))
                                    A)
                       (valid-sc-nt (CONS (CAR SC-TERM)
                                          (ATTACH-SC-LST (CDR SC-TERM)
                                                         SC-TYPE SC-TERM))
                                    A)
                        (VALID-SC-NT (LIST 'RP (LIST 'QUOTE SC-TYPE) SC-TERM)
                                     A)
                       (EX-FROM-RP (LIST 'RP
                                         (LIST 'QUOTE SC-TYPE)
                                         (CONS (CAR SC-TERM)
                                               (ATTACH-SC-LST (CDR SC-TERM)
                                                              SC-TYPE
                                                              SC-TERM)))))
              :cases ((EQUAL (CAR SC-TERM) 'QUOTE))
              :use ((:instance rp-evl-lemma20
                               (fn (CAR SC-TERM))
                               (lst1 (ATTACH-SC-LST (CDR SC-TERM)
                                                    SC-TYPE SC-TERM))
                               (lst2 (cdr sc-term))))
              :in-theory (e/d (IS-RP-IMPLIES-FC
                               ;;is-if
  

                               eval-and-all-nt
                               rp-evl-of-fncall-args
                               RP-EVL-lst-of-cons
                               rp-evl-of-fncall-args
                               CONTEXT-FROM-RP)
                              (VALID-SC-EX-FROM-RP-2
                               EX-FROM-RP-LEMMA1
                               rp-evl-lemma20
                               rp-termp
                               is-rp
                               valid-sc-nt))))))

  
  #|(skip-proofs
   (local
    (defthm lemma20-v2
      (IMPLIES (AND
                (CONSP SC-TERM)
                (NOT (EQUAL (CAR SC-TERM) 'QUOTE))
                (valid-sc-subterms (ATTACH-SC-LST (CDR SC-TERM)
                                                  SC-TYPE SC-TERM)
                                   A)
                (valid-sc SC-TERM A)
                (rp-termp SC-TERM)
                (NOT (EQUAL (CAR SC-TERM) 'IF))
; (NOT (INCLUDE-FNC-SUBTERMS (CDR SC-TERM)
;                           'IF))
                (not (is-rp sc-term))
                (IS-RP (LIST 'RP
                             (LIST 'QUOTE SC-TYPE)
                             SC-TERM))
                (RP-EVLt (LIST SC-TYPE SC-TERM) A))
               (valid-sc (LIST 'RP
                               (LIST 'QUOTE SC-TYPE)
                               (CONS (CAR SC-TERM)
                                     (ATTACH-SC-LST (CDR SC-TERM)
                                                    SC-TYPE SC-TERM)))
                         A))
      :hints (("Goal"
               :expand ((valid-sc (LIST 'RP
                                        (LIST 'QUOTE SC-TYPE)
                                        (CONS (CAR SC-TERM)
                                              (ATTACH-SC-LST (CDR SC-TERM)
                                                             SC-TYPE SC-TERM)))
                                  A)
                        (valid-sc (CONS (CAR SC-TERM)
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

                                eval-and-all-nt
                                rp-evl-of-fncall-args
                                RP-EVL-lst-of-cons
                                CONTEXT-FROM-RP
                                rp-evl-of-fncall-args)
                               (VALID-SC-EX-FROM-RP-2
                                EX-FROM-RP-LEMMA1
                                is-rp
                                valid-sc-nt)))))))||#



  
  
  (local
   (defthm lemma21
     (IMPLIES (AND (CONSP SC-TERM)
                   ;;(EQUAL (CAR SC-TERM) 'IF)
                   (valid-sc-nt SC-TERM A)
                   (rp-termp SC-TERM)
                   (IS-RP (LIST 'RP
                                (LIST 'QUOTE SC-TYPE)
                                SC-TERM))
                   (NOT (IS-RP SC-TERM))
                   (RP-EVL (LIST SC-TYPE SC-TERM) A))
              (valid-sc-nt (LIST 'RP (LIST 'QUOTE SC-TYPE) SC-TERM)
                           A))
     :otf-flg t
     :hints (("Goal"
              :expand ((valid-sc-nt (LIST 'RP (LIST 'QUOTE SC-TYPE) SC-TERM)
                                    A))
              :in-theory (e/d (CONTEXT-FROM-RP
                               EX-FROM-RP
                               )
                              (is-rp IS-IF-LEMMA1
                                     IS-RP-LEMMA2
                                     VALID-SC-EX-FROM-RP-2
                                     ))))))

  (local
   (defthm lemma21-v2
     (IMPLIES (AND (CONSP SC-TERM)
                   ;;(EQUAL (CAR SC-TERM) 'IF)
                   (valid-sc SC-TERM A)
                   (rp-termp SC-TERM)
                   (IS-RP (LIST 'RP
                                (LIST 'QUOTE SC-TYPE)
                                SC-TERM))
                   (NOT (IS-RP SC-TERM))
                   (RP-EVLt (LIST SC-TYPE SC-TERM) A))
              (valid-sc (LIST 'RP (LIST 'QUOTE SC-TYPE) SC-TERM)
                           A))
     :otf-flg t
     :hints (("Goal"
              :expand ((valid-sc (LIST 'RP (LIST 'QUOTE SC-TYPE) SC-TERM)
                                    A))
              :in-theory (e/d (CONTEXT-FROM-RP
                               EX-FROM-RP
                               )
                              (is-rp IS-IF-LEMMA1
                                     IS-RP-LEMMA2
                                     VALID-SC-EX-FROM-RP-2
                                     ))))))



  (local
   (defthm is-rp-lemma-18
     (implies (IS-RP TERM)
              (is-rp (LIST 'RP
                           (CADR TERM)
                           other)))
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))

  
  (local
   (defthm lemma18-v2
     (IMPLIES (AND (CONSP TERM)
                   (NOT (EQUAL (CAR TERM) 'QUOTE))
                   (case-split (NOT (is-if term)))
                   (NOT (EQUAL TERM SC-TERM))
                   (VALID-SC-SUBTERMS (ATTACH-SC-LST (CDR TERM)
                                                     SC-TYPE SC-TERM)
                                      A)
                   (VALID-SC TERM A)
                   (RP-TERMP TERM)
                   (IS-RP (LIST 'RP
                                (LIST 'QUOTE SC-TYPE)
                                SC-TERM))
                   (NOT (IS-RP SC-TERM))
                   (RP-EVL (LIST SC-TYPE (RP-TRANS SC-TERM))
                           A))
              (VALID-SC (CONS (CAR TERM)
                              (ATTACH-SC-LST (CDR TERM)
                                             SC-TYPE SC-TERM))
                        A))
     :otf-flg t
     :hints (("Goal"
              :do-not-induct t
              :cases ((is-rp term)) 
              :in-theory (e/d (
                               valid-sc-single-step
                               is-rp-implies-fc
                               rp-evl-of-fncall-args)
                              (is-rp
                               is-if
                               rp-termp
                               ))))))


  

  (local
   (defthm lemma20-v2
     (IMPLIES (AND (CONSP SC-TERM)
                   (NOT (EQUAL (CAR SC-TERM) 'QUOTE))
                  ; (NOT (EQUAL (CAR SC-TERM) 'IF))
                   (VALID-SC-SUBTERMS (ATTACH-SC-LST (CDR SC-TERM)
                                                     SC-TYPE SC-TERM)
                                      A)
                   (VALID-SC-SUBTERMS (CDR SC-TERM) A)
                   (RP-TERMP SC-TERM)
                   (case-split (NOT (is-if sc-term)))
                   (IS-RP (LIST 'RP
                                (LIST 'QUOTE SC-TYPE)
                                SC-TERM))
                   (NOT (IS-RP SC-TERM))
                   (RP-EVL (LIST SC-TYPE (RP-TRANS SC-TERM))
                           A))
              (VALID-SC (LIST 'RP
                              (LIST 'QUOTE SC-TYPE)
                              (CONS (CAR SC-TERM)
                                    (ATTACH-SC-LST (CDR SC-TERM)
                                                   SC-TYPE SC-TERM)))
                        A))
     :hints (("Goal"
              :do-not-induct t
              :use ((:instance rp-evlt-lemma20
                               (fn (CAR SC-TERM))
                               (lst1 (cdr SC-TERM))
                               (lst2 (ATTACH-SC-LST (CDR SC-TERM)
                                                    SC-TYPE SC-TERM))))
              ;; :expand ((RP-TRANS (CONS (CAR SC-TERM)
              ;;                          (ATTACH-SC-LST (CDR SC-TERM)
              ;;                                         SC-TYPE SC-TERM))))
              :in-theory (e/d (valid-sc-single-step
                               rp-evl-of-fncall-args
                               )
                              (rp-evlt-lemma20
                               is-if))))))


  ;; (skip-proofs
  ;;  (local
  ;;   (defthm lemma22-lemma
  ;;     (implies (and (equal (len (cdr term)) (len sublist))
  ;;                   (is-if term)
  ;;                   (consp term))
  ;;              (is-if (CONS 'if sublist)))
  ;;     :rule-classes :forward-chaining
  ;;     :hints (("Goal"
  ;;              :do-not-induct t
  ;;              :in-theory (e/d (is-if) ()))))))
  

  ;; (local
  ;;  (defthm lemma22
  ;;    (implies (and (rp-termp term)
  ;;                  ;(rp-term-listp sublist)
  ;;                  (if (rp-evl (car sublist) a)
  ;;                      (valid-sc-nt (cadr sublist) a)
  ;;                    (valid-sc-nt (caddr sublist) a))
  ;;                  (valid-sc-nt (car sublist) a)
  ;;                  (equal (rp-evl (cadr term) a)
  ;;                         (rp-evl (car sublist) a))
  ;;                  (consp term)
  ;;                  (case-split (is-if term))
  ;;                  (equal (len (cdr term)) (len sublist))
  ;;                  (valid-sc-nt term a))
  ;;             (VALID-SC-NT (CONS (CAR TERM) sublist)
  ;;                          A))
  ;;    :hints (("Goal"
  ;;             :do-not-induct t
  ;;             :expand ((VALID-SC-NT (CONS 'IF SUBLIST) A))
  ;;             :in-theory (e/d (VALID-SC-NT
  ;;                              is-rp)
  ;;                             (rp-termp
  ;;                              len
  ;;                              rp-term-listp)))))) 


  ;; (local
  ;;  (defthm lemma23
  ;;    (EQUAL (LEN (ATTACH-SC-LST subterms
  ;;                               SC-TYPE SC-TERM))
  ;;           (LEN subterms))
  ;;    :hints (("Goal"
  ;;             :induct (LEN subterms)
  ;;             :do-not-induct t
  ;;             :in-theory (e/d (ATTACH-SC-LST) ())))))


  #|(local
   (defthm-attach-sc
     (defthm valid-sc-nt-attach-sc-when-quoted
       (implies (and (valid-sc-nt term a)
                     (rp-termp term)
                     (quotep sc-term)
                     (is-rp (list 'rp (list 'quote sc-type) sc-term))
                     (not (is-rp sc-term))
                     (rp-evl `(,sc-type ,sc-term) a))
                (valid-sc-nt (attach-sc term sc-type sc-term) a))
       :flag attach-sc)

     (defthm valid-sc-nt-subterms-attach-sc-lst
       (implies (and (valid-sc-nt-subterms lst a)
                     (NOT (EQUAL (CAR SC-TERM) 'QUOTE))
                     (rp-term-listp lst)
                     (is-rp (list 'rp (list 'quote sc-type) sc-term))
                     (not (is-rp sc-term))
                     (rp-evl `(,sc-type ,sc-term) a))
                (valid-sc-nt-subterms (attach-sc-lst lst sc-type sc-term) a))
       :flag attach-sc-lst)
     :hints (("goal"
              ;;:cases ((is-rp term))
              :in-theory (e/d (is-rp-implies-fc
                               is-if
                               ;;rp-evl-constraint-0
                               eval-and-all-nt
                               context-from-rp
                               valid-sc-nt-single-step)
                              (valid-sc-ex-from-rp-2
                               (:rewrite lemma10)
                               (:definition falist-consistent)
                               (:rewrite measure-lemma1)
                               (:rewrite measure-lemma1-2)
                               (:rewrite default-cdr)
                               (:rewrite default-car)
                               rp-evl-lst-of-cons))))))||#
  (local
   (defthm not-consp-implies-not-is-rp
     (implies (Not (consp x))
              (not (is-rp x)))
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))


  (local
   (defthm is-if-lemma
     (is-if (list 'if x y z))
     :hints (("Goal"
              :in-theory (e/d (is-if) ())))))

  (local
   (defthm rp-evl-lst-of-list
     (equal (rp-evl-lst (list x) a)
            (list (rp-evl x a)))))
  
  (defthm-attach-sc
    (defthm valid-sc-nt-attach-sc
      (implies (and (valid-sc-nt term a)
                    (NOT (quotep sc-term))
                    (rp-termp term)
;          (not (include-fnc term 'if)) ;; rhs should not have any if
                    (is-rp (list 'rp (list 'quote sc-type) sc-term))
                    (not (is-rp sc-term))
                    (rp-evl `(,sc-type ,sc-term) a))
               (valid-sc-nt (attach-sc term sc-type sc-term) a))
      :flag attach-sc)

    (defthm valid-sc-nt-subterms-attach-sc-lst
      (implies (and (valid-sc-nt-subterms lst a)
                    (NOT (quotep sc-term))
                    (NOT (EQUAL (CAR SC-TERM) 'QUOTE))
                    (rp-term-listp lst)
;         (not (include-fnc-subterms lst 'if))
                    (is-rp (list 'rp (list 'quote sc-type) sc-term))
                    (not (is-rp sc-term))
                    (rp-evl `(,sc-type ,sc-term) a))
               (valid-sc-nt-subterms (attach-sc-lst lst sc-type sc-term) a))
      :flag attach-sc-lst)
    :hints (("goal"
             ;;:cases ((is-rp term))
             :in-theory (e/d (is-rp-implies-fc
                             ; is-if
                              ;;rp-evl-constraint-0
                              eval-and-all-nt
                              context-from-rp
                              valid-sc-nt-single-step)
                             (valid-sc-ex-from-rp-2
                              (:rewrite lemma10)
                              (:definition falist-consistent)
                              (:rewrite measure-lemma1)
                              (:rewrite measure-lemma1-2)
                              (:rewrite default-cdr)
                              (:rewrite default-car)
                              rp-evl-lst-of-cons)))))


  

  
  
  (defthm-attach-sc
    (defthm valid-sc-attach-sc
      (implies (and (valid-sc term a)
                    (rp-termp term)
                    (is-rp (LIST 'RP (LIST 'QUOTE SC-TYPE) SC-TERM))
                    (not (is-rp sc-term))
                    (rp-evlt `(,sc-type ,sc-term) a))
               (valid-sc (attach-sc term sc-type sc-term) a))
      :flag attach-sc)

    (defthm valid-sc-subterms-attach-sc-lst
      (implies (and (valid-sc-subterms lst a)
                    (rp-term-listp lst)
                    (is-rp (LIST 'RP (LIST 'QUOTE SC-TYPE) SC-TERM))
                    (not (is-rp sc-term))
                    (rp-evlt `(,sc-type ,sc-term) a))
               (valid-sc-subterms (attach-sc-lst lst sc-type sc-term) a))
      :flag attach-sc-lst)
    :otf-flg t
    :hints (("Subgoal *1/3"
             :use ((:instance RP-EVLt-LEMMA20
                              (fn (car sc-term))
                              (lst1 (cdr sc-term))
                              (lst2 (attach-sc-lst (cdr sc-term) sc-type sc-term)))))          
            ("Goal"
             :do-not-induct t
             ;;:cases ((Is-rp term))
             :in-theory (e/d (IS-RP-IMPLIES-FC
                              ;;is-if
                              ;;rp-evl-constraint-0
                              eval-and-all
                              CONTEXT-FROM-RP
                              rp-trans
                              rp-evl-of-fncall-args
                              valid-sc-single-step)
                             (VALID-SC-EX-FROM-RP-2
                              RP-EVL-LEMMA20
                              NOT-INCLUDE-RP-MEANS-VALID-SC
                              not-include-rp-means-valid-sc-lst
                              RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                              RP-TERMP
                              (:REWRITE LEMMA10)
                              (:DEFINITION FALIST-CONSISTENT)
                              (:REWRITE MEASURE-LEMMA1)
                              (:REWRITE MEASURE-LEMMA1-2)
                              (:REWRITE DEFAULT-CDR)
                              (:REWRITE DEFAULT-CAR)
                              RP-EVL-lst-of-cons)))))
  
  )

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
#|
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
           :in-theory (e/d (is-rp) ()))))||#

(defthm dummy-is-rp-lemma
  (implies (IS-RP (LIST 'RP (LIST 'QUOTE SC-TYPE) sc-term))
           (IS-RP (LIST 'RP (LIST 'QUOTE SC-TYPE) y)))
  :hints (("Goal"
           :in-theory (e/d (is-rp) ()))))

(defthm-rp-termp
  (defthm rp-termp-attach-sc
    (implies (and (rp-termp term)
                  (not (include-fnc term 'falist))
                  (is-rp (LIST 'RP (LIST 'QUOTE SC-TYPE) SC-TERM)))
             (rp-termp (attach-sc term sc-type sc-term)))
    :flag rp-termp)
  (defthm rp-term-listp-attach-sc-lst
    (implies (and (rp-term-listp lst)
                  (not (include-fnc-subterms lst 'falist))
                  (is-rp (LIST 'RP (LIST 'QUOTE SC-TYPE) SC-TERM)))
             (rp-term-listp (attach-sc-lst lst sc-type sc-term)))
    :flag rp-term-listp)
  :otf-flg t
  :hints (("Goal"
           :expand ((ATTACH-SC TERM SC-TYPE SC-TERM)
                    (ATTACH-SC-LST NIL SC-TYPE SC-TERM)
                    (ATTACH-SC SC-TERM SC-TYPE SC-TERM)
                    (ATTACH-SC-LST LST SC-TYPE SC-TERM))
           :in-theory (e/d (is-rp)
                           ((:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                            (:DEFINITION ACL2::APPLY$-BADGEP)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE DEFAULT-CAR)
                            (:DEFINITION SUBSETP-EQUAL)
                            (:DEFINITION MEMBER-EQUAL)
                            (:REWRITE
                             ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:REWRITE IS-IF-RP-TERMP))))))

(make-flag get-vars1 :defthm-macro-name defthm-get-vars)

(defthm-get-vars
  (defthm get-vars1-attach-sc
    (equal (get-vars1 (attach-sc q sc-type sc-term) acc)
           (get-vars1 q acc))
    :flag get-vars1)
  (defthm get-vars1-attach-sc-lst
    (equal (get-vars-subterms (attach-sc-lst subterms sc-type sc-term) acc)
           (get-vars-subterms subterms acc))
    :flag get-vars-subterms)
  :hints (("Goal"
           :expand (ATTACH-SC Q SC-TYPE SC-TERM)
           :in-theory (e/d ()
                           ((:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                            rp-termp
                            true-listp
                            rp-term-listp)))))


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
     (implies (eval-and-all-nt sc-list a)
              (eval-and-all-nt (cdr sc-list) a))
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
                   (eval-and-all-nt SC-LIST A)
                   (CONSP (CDR (CAR SC-LIST)))
                   (EQ (CDDR (CAR SC-LIST)) NIL))
              (RP-EVL (LIST (CAR (CAR SC-LIST))
                            (CADR (CAR SC-LIST)))
                      A))))

  (defthm valid-sc-of-attach-sc-list-to-rhs
    (implies (and (not (include-fnc-subterms sc-list 'rp))
                  (eval-and-all-nt sc-list a)
                  (rp-termp rhs)
                  (not (include-fnc rhs 'falist))
                  (valid-sc-nt rhs a))
             (valid-sc-nt (attach-sc-list-to-rhs rhs sc-list) a)))

  (defthm not-include-fnc-attach-sc-list-to-rhs
    (implies (and (not (include-fnc rhs fn))
                  (not (equal fn 'rp)))
             (not (include-fnc (attach-sc-list-to-rhs rhs sc-list)
                               fn))))

  (defthm rp-termp-attach-sc-list-to-rhs
    (implies (and (rp-termp rhs)
                  (not (include-fnc rhs 'falist)))
             (rp-termp (attach-sc-list-to-rhs rhs sc-list))))

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
    (iff (eval-and-all-nt (if-to-and-list term) a)
         (rp-evl term a))
    :hints (("Goal"
             :in-theory (e/d (if-to-and-list) ()))))

  (defthm eval-and-all-if-to-and-list2
    (implies (rp-evl term a)
             (eval-and-all-nt (if-to-and-list term) a))
    :hints (("Goal"
             :in-theory (e/d (if-to-and-list) ())))))

(local
 (encapsulate
   nil

   (local
    (in-theory (enable rule-syntaxp)))

   (defthm rule-sytanxp-attach-sc-to-rule
     (implies (rule-syntaxp rule)
              (rule-syntaxp (attach-sc-to-rule rule sc-formula)))
     :hints (("Goal"
              :in-theory (e/d (NO-FREE-VARIABLEP) (get-vars1
                                                   RP-TERM-LISTP
                                                   IS-RP-PSEUDO-TERMP
                                                   RP-TERM-LISTP-IS-TRUE-LISTP
                                                   RP-TERMP-IMPLIES-CDR-LISTP
                                                   RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS
                                                   DEFAULT-CAR
                                                   NOT-INCLUDE-RP
                                                   DEFAULT-CDR
                                                   TRUE-LISTP
                                                   (:DEFINITION ALWAYS$)
                                                   (:DEFINITION SUBSETP-EQUAL)
                                                   (:DEFINITION MEMBER-EQUAL)
                                                   (:REWRITE ACL2::PLAIN-UQI-INTEGER-LISTP)
                                                   (:REWRITE ACL2::APPLY$-SYMBOL-ARITY-1)
                                                   (:DEFINITION ACL2::APPLY$-BADGEP)
                                                   (:REWRITE
                                                    ACL2::INTEGER-LISTP-IMPLIES-ALWAYS$-INTEGERP)
                                                   (:DEFINITION INTEGER-LISTP)
                                                   IS-IF-RP-TERMP)))))

   (local
    (defthm rule-syntaxp-implies-m
      (implies (rule-syntaxp rule)
               (AND (WEAK-CUSTOM-REWRITE-RULE-P RULE)
                    (RP-TERMP (RP-HYPm RULE))
                    (RP-TERMP (RP-LHSm RULE))
                    (RP-TERMP (RP-RHSm RULE))
                    (NOT (INCLUDE-FNC (RP-LHSm RULE) 'RP))
                    (NOT (INCLUDE-FNC (RP-HYPm RULE) 'RP))
                    (rp-termp (RP-RHSm RULE))
                    (NOT (INCLUDE-FNC (RP-RHSm RULE) 'FALIST))
                    (NOT (INCLUDE-FNC (RP-HYPm RULE) 'FALIST))
                    (NOT (INCLUDE-FNC (RP-LHSm RULE) 'IF))
                    (NOT (INCLUDE-FNC (RP-LHSm RULE) 'SYNP))
                    (NO-FREE-VARIABLEP RULE)))
      :rule-classes :forward-chaining
      :hints (("Goal"
               :in-theory '(rule-syntaxp quotep
                                         RP-HYP
                                         RP-LHS
                                         RP-RHS)))))

   (local
    (defthm rp-evl-and-eval-and-all
      (implies (and (subsetp x y)
                    (eval-and-all-nt y a))
               (eval-and-all-nt x a))
      :hints (("Goal"
               :in-theory (e/d ()
                               ((:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                                (:DEFINITION TRUE-LISTP)
                                (:REWRITE ACL2::PLAIN-UQI-TRUE-LIST-LISTP)
                                (:DEFINITION ALWAYS$)
                                (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                                (:DEFINITION RP-TERMP)
                                (:REWRITE
                                 ACL2::TRUE-LIST-LISTP-IMPLIES-ALWAYS$-TRUE-LISTP)
                                (:DEFINITION TRUE-LIST-LISTP)
                                (:DEFINITION FALIST-CONSISTENT)
                                (:DEFINITION FALIST-CONSISTENT-AUX)))))))

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
                               rule-syntaxp-implies-m
                               valid-sc-nt-is-valid-sc)
                              (rule-syntaxp
                               (:REWRITE DEFAULT-CDR)
                               (:REWRITE EX-FROM-SYNP-LEMMA1)
                               IS-SYNP
                               (:DEFINITION RP-EQUAL)
                               (:REWRITE RP-EQUAL-IMPLIES-RP-EQUAL2)
                               (:TYPE-PRESCRIPTION INCLUDE-FNC)
                               EX-FROM-RP
                               (:REWRITE RP-EQUAL-IMPLIES-RP-EQUAL2)
                               (:DEFINITION RP-TERMP)
                               (:DEFINITION eval-and-all-nt)
                               get-vars1
                               (:DEFINITION SUBSETP-EQUAL)
                               (:REWRITE ACL2::PLAIN-UQI-TRUE-LIST-LISTP)
                               (:DEFINITION MEMBER-EQUAL)
                               (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                               (:REWRITE ACL2::O-P-O-INFP-CAR)
                               (:DEFINITION TRUE-LISTP)
                               (:DEFINITION RP-TERM-LISTP)
                               (:REWRITE
                                ACL2::TRUE-LIST-LISTP-IMPLIES-ALWAYS$-TRUE-LISTP)
                               (:DEFINITION TRUE-LIST-LISTP)
                               (:REWRITE ACL2::APPLY$-SYMBOL-ARITY-1)
                               (:DEFINITION ACL2::APPLY$-BADGEP)
                               (:REWRITE ACL2::APPLY$-PRIMITIVE)
                               (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                               (:REWRITE DEFAULT-CAR)
                               (:DEFINITION valid-sc-nt)
                               (:META ACL2::APPLY$-PRIM-META-FN-CORRECT))))))))

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

(defthm VALID-RULEP-implies
  (implies (valid-rulep rule)
           (AND (RULE-SYNTAXP RULE)
                (VALID-RULEP-SK RULE)))
  :rule-classes :forward-chaining)

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
;valid-rulep-update-rule-with-sc
                            valid-rulep-sk
                            valid-rulep
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

(progn
  (local
   (defthm valid-rulesp-try-to-add-rule-fnc-lemma-1
     (equal (valid-rulep-sk-body (change custom-rewrite-rule
                                         rule
                                         :rule-fnc x)
                                 a)
            (valid-rulep-sk-body rule a))))

  (local
   (defthm valid-rulesp-try-to-add-rule-fnc-lemma-2
     (implies (valid-rulep-sk rule)
              (valid-rulep-sk (change custom-rewrite-rule
                                      rule
                                      :rule-fnc x)))
     :otf-flg t
     :hints (("goal"
              :expand (valid-rulep-sk (list* (car rule)
                                             (cadr rule)
                                             x (cdddr rule)))
              :use ((:instance valid-rulep-sk-necc
                               (a (list* (car rule)
                                         (cadr rule)
                                         x (cdddr rule)))))
              :in-theory (e/d ()
                              (rule-syntaxp
                               valid-rulep-sk
                               valid-rulep-sk-body))))))

  (local
   (defthm valid-rulesp-try-to-add-rule-fnc-lemma-3
     (implies (valid-rulep rule)
              (valid-rulep (change custom-rewrite-rule
                                   rule
                                   :rule-fnc x)))
     :otf-flg t
     :hints (("goal"
              :in-theory (e/d (valid-rulep-sk-necc
                               NO-FREE-VARIABLEP
                               rule-syntaxp)
                              (valid-rulep-sk))))))

  (defthm valid-rulesp-try-to-add-rule-fnc
    (implies (valid-rulesp rules)
             (valid-rulesp (try-to-add-rule-fnc rules rule-fnc-alist)))
    :hints (("goal"
             :in-theory (e/d (try-to-add-rule-fnc
                              len)
                             (rule-syntaxp
                              weak-custom-rewrite-rule-p
                              valid-rulep
                              check-if-def-rule-should-be-saved
                              custom-rewrite-with-meta-extract
                              update-rules-with-sc))))))

(defthm valid-rulesp-get-rules
  (implies (rp-evl-meta-extract-global-facts :state state)
           (valid-rulesp (get-rule-list runes sc-alist new-synps warning rule-fnc-alist
                                        state)))
  :hints (("Goal"
           :do-not-induct t
           :induct (get-rule-list runes sc-alist new-synps warning rule-fnc-alist
                                  state)
           :in-theory (e/d ()
                           (rule-syntaxp
                            WEAK-CUSTOM-REWRITE-RULE-P
                            ACL2::EQUAL-LEN-1
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

(defthm symbol-alistp-get-disabled-exc-rules-from-table
  (symbol-alistp (get-disabled-exc-rules-from-table x))
  :hints (("Goal"
           :in-theory (e/d (get-disabled-exc-rules-from-table) ()))))

(defthm true-listp-get-enabled-rules-from-table-aux
  (b* (((mv rules-rw rules-def)
        (get-enabled-rules-from-table-aux rp-rules-inorder rp-rules)))
    (and (true-listp rules-rw)
         (true-listp rules-def)))
  :hints (("Goal"
           :in-theory (e/d (get-enabled-rules-from-table-aux) ()))))

(defthm symbol-listp-get-enabled-rules-from-table
  (symbol-alistp (mv-nth 1 (get-enabled-rules-from-table state)))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (get-enabled-rules-from-table) ()))))
