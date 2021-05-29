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

(include-book "aux-functions")
(include-book "macros")

(local
 (include-book "proofs/proof-function-lemmas"))
(local
 (include-book "proofs/aux-function-lemmas"))
(local
 (include-book "proofs/rp-equal-lemmas"))

(include-book "rp-rewriter")

;;(include-book "create-rule-fnc")

(include-book "std/strings/suffixp" :dir :system)

(local
 (in-theory (enable rule-syntaxp)))

(defun custom-rewrite-from-formula (formula)
  (declare (xargs :guard t))
  (case-match formula
    (('implies hyp conc)
     (case-match conc
       (('equal lhs rhs)
        (mv nil hyp lhs rhs))
       (&
        (mv t hyp conc ''t;`(nonnil-fix ,conc)
            ))))
    (&
     (case-match formula
       (('equal lhs rhs)
        (mv nil ''t lhs rhs))
       (&
        (mv t ''t formula ''t;`(nonnil-fix ,formula)
            ))))))


#|(mutual-recursion
 (defun force-to-force$ (term rule-name)
   (cond ((or (atom term)
              (quotep term))
          term)
         ((case-match term (('force &) t))
          `(force$ ,(cadr term) ',rule-name ',(cadr term)))
         (t (cons-with-hint (car term)
                            (force-to-force$ (cdr term) rule-name)
                            term))))
 (defun force-to-force$-lst (lst rule-name)
   (if (atom lst)
       nil
     (cons-with-hint (force-to-force$ (car lst) rule-name hyp)
                     (force-to-force$-lst (cdr lst) rule-name hyp)
                     lst))))||#
       

(defund if-to-and-list (if-form)
  (declare (xargs :guard t))
  (case-match if-form
    (('if a b ''nil)
     (cons a
           (if-to-and-list b)))
    (& (cons if-form nil))))

(defun sc-rule-p (formula sc-formula)
  (declare (xargs :guard t
                  :verify-guards nil))
  "Checks whether the given side-condition formula can be used."
  (and (or (not (equal formula ''t))
           (hard-error 'side-condition-check
                       "Rule cannot be found ~%" nil))
       (or (not (equal sc-formula ''t))
           (hard-error 'side-condition-check
                       "Side condition rule cannot be found ~%" nil))
       (or
        (not (include-fnc formula 'rp))
        (hard-error 'side-condition-check
                    "Rule cannot have any instances of rp ~%" nil))
       (or (not (include-fnc sc-formula 'rp))
           (hard-error 'side-condition-check
                       "Side-condition rule cannot have any instances of rp ~%"
                       nil))
       (case-match formula
         (('implies p &)
          (and
           (b* ((p2 (if-to-and-list p)))
             (case-match sc-formula
               (('implies scp &)
                (b* ((scp2 (if-to-and-list scp)))
                  (or (subsetp-equal scp2 p2)
                      (hard-error 'side-condition-check
                                  "Hypothesis of side-condition rule should be a subset ~
  of the original rule ~%" nil))))
               (& t)))))
         (& (case-match sc-formula
              (('implies & &)
               (hard-error 'side-condition-check
                           "Hypothesis of side-condition rule should be a subset ~
  of the original rule ~%"
                           nil))
              (& t))))))

(defun not-to-equal-nil (term)
  (declare (xargs :guard t))
  (case-match term
    (('not x)
     `(equal ,x nil))
    (& term)))

(defund not-to-equal-nil-list (term-list)
  (declare (xargs :guard t))
  (if (atom term-list)
      nil
    (cons (not-to-equal-nil (car term-list))
          (not-to-equal-nil-list (cdr term-list)))))

(defun make-rule-better-aux1 (p qs)
  (declare (xargs :guard t))
  (if (atom qs)
      nil
    (cons `(implies ,p ,(car qs))
          (make-rule-better-aux1 p (cdr qs)))))

(defun make-formula-better (formula)
  ;; returns a list of rules because a single rule can create multiplie
  ;; rewrite rules because of "and"
  (declare (xargs :guard t))
  (b* ((formula (beta-search-reduce formula *big-number*)))
    (case-match formula
      (('implies p q)
       (b* ((new-terms (if-to-and-list q))
            (new-terms (not-to-equal-nil-list new-terms))
            (formulas (make-rule-better-aux1 p new-terms)))
         formulas))
      (&
       (b* ((new-terms (if-to-and-list formula))
            (new-terms (not-to-equal-nil-list new-terms)))
         new-terms)))))


(mutual-recursion
 (defun insert-iff-to-force (term rule-name iff-flg in-hyps)
   (declare (xargs :guard t))
   (cond ((or (atom term)
              (quotep term))
          term)
         (t
          (case-match term
            (('implies p q)
             `(implies ,(insert-iff-to-force p rule-name t t)
                       ,(insert-iff-to-force q rule-name t in-hyps)))
            (('force x)
             (if in-hyps
                 (if iff-flg
                     `(force$ (if ,(insert-iff-to-force x rule-name iff-flg t) 't
                                'nil)
                              ',rule-name
                              ',term)
                   `(force$ ,(insert-iff-to-force x rule-name iff-flg t)
                            ',rule-name
                            ',term))
               (cons-with-hint
                'force
                (cons-with-hint (insert-iff-to-force x rule-name iff-flg nil) nil (cdr term))
                term)))
            (('if test then else)
             `(if ,(insert-iff-to-force test rule-name t in-hyps)
                  ,(insert-iff-to-force then rule-name iff-flg in-hyps)
                ,(insert-iff-to-force else rule-name iff-flg in-hyps)))
            (&
             (cons-with-hint (car term)
                             (insert-iff-to-force-lst (cdr term) rule-name in-hyps)
                             term))))))
 (defun insert-iff-to-force-lst (lst rule-name in-hyps)
   (if (atom lst)
       nil
     (cons-with-hint (insert-iff-to-force (car lst) rule-name nil in-hyps)
                     (insert-iff-to-force-lst (cdr lst) rule-name in-hyps)
                     lst))))

(defund formulas-to-rules (rune rule-new-synp warning formulas)
  (declare (xargs :guard t))
  (if (atom formulas)
      nil
    (b* ((formula (car formulas))
         
         ((mv flg hyp lhs rhs)
          (custom-rewrite-from-formula formula))
         (hyp (if rule-new-synp
                  `(if (synp 'nil 'nil ',rule-new-synp)
                       ,hyp
                     'nil)
                hyp))
         
         (rule (make custom-rewrite-rule
                     :rune rune
                     :hyp hyp
                     :flg flg
                     :lhs/trig-fnc lhs
                     :rhs/meta-fnc rhs))
         (rest (formulas-to-rules rune rule-new-synp warning (cdr formulas))))
      (if (and (rule-syntaxp rule :warning warning)
               (or (not (include-fnc rhs 'rp))
                   (and warning
                        (cw "(not (include-fnc rhs 'rp)) failed! ~p0 ~%.
 Rhs of  a rule cannot have an 'rp' instance ~%" rhs))))
          (cons rule rest)
        rest))))

(defun custom-rewrite-with-meta-extract (rule-name rule-new-synp warning state)
  (declare (xargs :guard (and (symbolp rule-name))
                  :stobjs (state)
                  :verify-guards t))
  (b* ((formula (meta-extract-formula rule-name state))
       (formula (insert-iff-to-force formula rule-name nil nil))
       #|((when (equal formula ''t))
        nil)||#
       ((when (not (pseudo-termp formula)))
        (hard-error 'custom-rewrite-with-meta-extract
                    "Rule ~p0 does not seem to be pseudo-termp ~%"
                    (list (cons #\0 rule-name))))
       (formulas (make-formula-better formula))
       (rune (get-rune-name rule-name state)))
    (formulas-to-rules rune rule-new-synp warning formulas)))



(defun attach-sc-list-to-rhs (rhs sc-list)
  "input is rhs of the rule and a list of formulas representing the
    side-conditions, and they are expected to be unary functions each."
  (declare (xargs :guard t))
  (if (atom sc-list)
      rhs
    (let ((sc (car sc-list)))
      (case-match sc
        ((sc-type sc-term)
         (if (and (not (quotep sc-term))
                  (is-rp `(rp ',sc-type ,sc-term)))
             (attach-sc-list-to-rhs (attach-sc rhs sc-type sc-term) (cdr sc-list))
           (or (cw
                "WARNING! Side-condition problem ~p0. Skipping this one. ~%"
                (car sc-list))
               (attach-sc-list-to-rhs rhs (cdr sc-list)))))
        (& (or (cw
                "WARNING! Properties in the side-condition should be unary ~
  functions. This happened for ~p0. Skipping this one. ~%" (car sc-list))
               (attach-sc-list-to-rhs rhs (cdr sc-list))))))))





(defund extract-from-force (term)
  (declare (xargs :guard t))
  (case-match term
    (('force$ ('if x ''t ''nil) & &)
     x)
    (('force ('if x ''t ''nil))
     x)
    (('force$ x & &)
     x)
    (('force x)
     x)
    (('if x y z)
     `(if ,(extract-from-force x)
          ,(extract-from-force y)
        ,(extract-from-force z)))
    (& term)))

#|(local
 (defthm true-listp-of-extract-from-force-lst
   (equal (true-listp (extract-from-force-lst lst))
          (true-listp lst))
   :hints (("Goal"
            :induct (extract-from-force-lst lst)
            :do-not-induct t
            :in-theory (e/d (extract-from-force-lst) ())))))||#

(defun attach-sc-to-rule (rule sc-formula)
  (declare (xargs :guard (and (weak-custom-rewrite-rule-p rule)
                              (not (rp-rule-metap rule)))
                  :VERIFY-GUARDS t))
  (b* (#|((when (include-fnc (rp-rhs rule) 'if))
       (or (hard-error 'side-condition-check
       "We do not yet support side conditions for rules that ~
       have if statements on the right handside~%" nil)
       rule))||#)
    (case-match sc-formula
      (('implies scp q)
       (b* (((when (not (subsetp-equal (if-to-and-list (extract-from-force scp))
                                       (if-to-and-list (extract-from-force (rp-hyp rule))))))
             (or (hard-error 'side-condition-check
                             "hypothesis of side-condition rule should be a subset ~
  of the original rule ~%" nil)
                 rule))
            (sc-list (if-to-and-list q))
            (rule-rhs (rp-rhs rule))
            (rhs-updated (attach-sc-list-to-rhs rule-rhs sc-list))
            (rule (change custom-rewrite-rule rule
                          :rhs/meta-fnc rhs-updated)))
         rule))
      (&
       (b* ((sc-list (if-to-and-list sc-formula))
            (rule-rhs (rp-rhs rule))
            (rhs-updated (attach-sc-list-to-rhs rule-rhs sc-list))
            (rule (change custom-rewrite-rule rule
                          :rhs/meta-fnc rhs-updated)))
         rule)))))

(defun update-rule-with-sc-aux (rule sc-rule-names state)
  (declare (xargs :guard (and (symbol-listp sc-rule-names)
                              (rule-syntaxp rule)
                              (not (rp-rule-metap rule)))
                  :verify-guards nil
                  :stobjs (state)))
  (if (atom sc-rule-names)
      rule
    (b* ((sc-formula (meta-extract-formula (car sc-rule-names) state))
;(sc-formula (beta-search-reduce sc-formula 1000)) ;; for psuedo-termp2
         ((when (or (include-fnc sc-formula 'rp)
                    (not (rp-termp sc-formula))))
          (progn$
           (hard-error
            'side-cond-attaching
            "Side condition formula cannot include an instance of rp or there ~
  is something wrong with is syntax ~%" nil)
           (update-rule-with-sc-aux rule (cdr sc-rule-names) state)))
         (rule-tmp (attach-sc-to-rule rule sc-formula))
         ((when (not (rule-syntaxp rule-tmp)))
          (progn$
           (hard-error
            'side-cond-attaching
            "Unknown problem in update-rule-with-sc-aux ~%" nil)
           (update-rule-with-sc-aux rule (cdr sc-rule-names) state))))
      (update-rule-with-sc-aux rule-tmp (cdr sc-rule-names) state))))

(local
 (defthm attach-sc-to-rule-returns-weak-custom-rewrite-rule-p
   (implies (and (rule-syntaxp rule)
                 (not (rp-rule-metap rule)))
            (and (weak-custom-rewrite-rule-p (attach-sc-to-rule rule sc-formula))
                 (not (rp-rule-metap (attach-sc-to-rule rule sc-formula))))))) 

(local
 (defthm rule-syntaxp-implies-weak-custom-rw-rule
   (implies (RULE-SYNTAXP RULE :WARNING nil)
            (weak-custom-rewrite-rule-p rule))
   :hints (("Goal"
            :in-theory (e/d (RULE-SYNTAXP) ())))))

(verify-guards update-rule-with-sc-aux
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :induct (update-rule-with-sc-aux rule sc-rule-names state)
           :in-theory (e/d (rule-syntaxp-implies
                            rule-syntaxp-implies-weak-custom-rw-rule
                            rule-syntaxp-implies-2)
                           (rule-syntaxp
                            rp-rule-metap
                            ;;SYMBOL-LISTP
                            STATE-P
                            WEAK-CUSTOM-REWRITE-RULE-P
                            attach-sc-to-rule
                            rp-termp)))))

(defun symbol-symbol-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (eq alist nil)
    (and (consp (car alist))
         (symbolp (caar alist))
         (symbol-listp (cdar alist))
         (symbol-symbol-alistp (cdr alist)))))

(defun update-rule-with-sc (rule sc-alist state)
  (declare (xargs :guard (and (symbol-symbol-alistp sc-alist)
                              (rule-syntaxp rule)
                              (not (rp-rule-metap rule)))
                  :verify-guards nil
                  :stobjs (state)))
  (b* ((rule-name (rp-rune rule))
       (rule-name (case-match rule-name ((& name . &) name) (& rule-name)))
       (sc-rule-names (assoc-eq rule-name sc-alist))
       ((when (atom sc-rule-names)) rule)
       (sc-rule-names (cdr (assoc-eq rule-name sc-alist))))
    (update-rule-with-sc-aux rule sc-rule-names state)))


(verify-guards update-rule-with-sc
  :otf-flg t
  :hints (("Goal"
           :use ((:instance rule-syntaxp-implies))
           :in-theory (e/d ()
                           (rule-syntaxp
                            no-free-variablep
                            weak-custom-rewrite-rule-p
                            rp-termp
                            FALIST-CONSISTENT
                            IS-IF-RP-TERMP
                            RP-RULE-METAP
                            RP-TERM-LISTP
                            (:TYPE-PRESCRIPTION RP-TERMP)
                            (:TYPE-PRESCRIPTION TRUE-LIST-LISTP)
                            (:TYPE-PRESCRIPTION ALISTP)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC)
                            (:TYPE-PRESCRIPTION SYMBOL-ALISTP)
                            (:DEFINITION QUOTEP)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE DEFAULT-CAR)
                            (:DEFINITION STATE-P)
                            (:DEFINITION RP-HYP$INLINE)   
                            (:DEFINITION RP-LHS$INLINE)
                            (:DEFINITION RP-RHS$INLINE)
                            (:DEFINITION RP-RUNE$INLINE)
                            (:TYPE-PRESCRIPTION EQLABLE-ALISTP))))))


(local
 (defthm rule-list-syntaxp-implies-WEAK-CUSTOM-REWRITE-RULE-LISTP
   (implies (rule-list-syntaxp rules)
            (WEAK-CUSTOM-REWRITE-RULE-LISTP rules))
   :hints (("Goal"
            :induct (rule-list-syntaxp rules) 
            :in-theory (e/d () (RULE-SYNTAXP
                                WEAK-CUSTOM-REWRITE-RULE-P))))))

(local
 (defthm rp-rule-rw-listp-of-conses
   (equal (rp-rule-rw-listp (cons a b))
          (AND (RP-RULE-RWP a)
               (RP-RULE-RW-LISTP b)))))

(local
 (defthm RULE-LIST-SYNTAXP-of-conses
   (equal (RULE-LIST-SYNTAXP (cons a b))
          (AND (RULE-SYNTAXP a)
               (RULE-LIST-SYNTAXP b)))))

(defun update-rules-with-sc (rules sc-alist state)
  (declare (xargs :guard (and (rule-list-syntaxp rules)
                              (rp-rule-rw-listp rules)
                              (symbol-symbol-alistp sc-alist))
                  :guard-hints (("Goal"
                                 :in-theory (e/d ()
                                                 (GET-VARS
                                                  rule-list-syntaxp
                                                  RULE-SYNTAXP
                                                  rp-rule-rw-listp
                                                  WEAK-CUSTOM-REWRITE-RULE-P
                                                  WEAK-CUSTOM-REWRITE-RULE-LISTP
                                                  NO-FREE-VARIABLEP))))
                  :stobjs (state)
                  :verify-guards t))
  (if (atom rules)
      nil
    (cons (update-rule-with-sc (car rules) sc-alist state)
          (update-rules-with-sc (cdr rules) sc-alist state))))

(defun add-rule-to-alist (alist rule)
  (declare (xargs :guard (and (weak-custom-rewrite-rule-p rule)
                              (alistp alist))))
  (b* ((lhs (access custom-rewrite-rule rule :lhs/trig-fnc))
       (key (if (consp lhs) (car lhs) lhs))
       (key (if (symbolp key) key nil))
       (entry (assoc-eq key alist)))
    (if entry
        (put-assoc key (cons rule (cdr entry)) alist)
      (cons (list key rule)
            alist))))

(defund check-if-def-rule-should-be-saved (rule-name state)
  (declare (xargs :guard (symbolp rule-name)
                  :stobjs (state)
                  :verify-guards t))
  "Returns t if the function is not recursive, nil otherwise"
  (and t (b* ((formula (meta-extract-formula rule-name state))
              #|(formula (beta-search-reduce formula *big-number*))||#
              (rhs (case-match formula
                     (('equal & rhs) rhs)
                     (('iff & rhs) rhs)
                     (& (list rule-name))))) ;;unknown format. assign to rule-name so
           ;; that next test fails.  if rule-name exist on the rhs, then it is
           ;; a recursive function. We do not want to have that definition rule
           ;; in the rewriter becasue it would be opened up nonstop.
           (if (rp-termp rhs);;for guard
               (not (include-fnc rhs rule-name))
             nil))))

(defthm UPDATE-RULE-WITH-SC-AUX-returns-rule-list-syntaxp
  (implies (rule-syntaxp rule)
           (rule-syntaxp (update-rule-with-sc-aux rule SC-RULE-NAMES state)))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d () (rule-syntaxp)))))

(defthm update-rules-with-sc-returns-rule-list-syntaxp
  (implies (rule-list-syntaxp rules)
           (rule-list-syntaxp (update-rules-with-sc rules sc-alist state)))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d () (rule-syntaxp)))))

#|(define try-to-add-rule-fnc (rules rule-fnc-alist)
  :guard-hints (("Goal"
           :in-theory (e/d (weak-custom-rewrite-rule-p) ())))
  (if (and (equal (len rules) 1)
           (weak-custom-rewrite-rule-p (car rules)))
      (b* ((rune (rp-rune (car rules)))
           (rule-name (case-match rune ((& n) n)))
           ((Unless rule-name) rules)
           (entry (hons-get rule-name rule-fnc-alist)))
        (if (consp entry)
            (list (change custom-rewrite-rule
                          (car rules)
                          :rule-fnc
                          (cdr entry)))
          rules))
    rules))||#



(defun meta-rune-p (rune)
  (declare (xargs :guard t))
  (case-match rune
    ((':meta meta-fnc . trig-fnc)
     (and meta-fnc
          trig-fnc
          (symbolp meta-fnc)
          (symbolp trig-fnc)))))

(defund make-custom-rule-for-meta (rune)
  (declare (xargs :guard (meta-rune-p rune)))
  (make custom-rewrite-rule
                      :meta-rulep t
                      :hyp ''nil ;; hyp nil will make the rule always correct without
                      ;; having to identify it as a special meta rule.
                      :rune rune
                      :lhs/trig-fnc (cddr rune)  
                      :rhs/meta-fnc (cadr rune)))


(local
 (in-theory (disable RULE-SYNTAXP)))

(local
 (defthm FORMULAS-TO-RULES-returns-RP-RULE-RW-LISTP
   (RP-RULE-RW-LISTP (FORMULAS-TO-RULES RUNE RULE-NEW-SYNP WARNING FORMULAS))
   :hints (("Goal"
            :in-theory (e/d (FORMULAS-TO-RULES)
                            (RULE-SYNTAXP))))))

(local
 (defthm CUSTOM-REWRITE-WITH-META-EXTRACT-returns-RP-RULE-RW-LISTP
   (RP-RULE-RW-LISTP (CUSTOM-REWRITE-WITH-META-EXTRACT RULE-NAME RULE-NEW-SYNP WARNING STATE))))

(defun get-rule-list (runes sc-alist new-synps warning state)
  (declare (xargs :guard (and (symbol-symbol-alistp sc-alist)
                              (alistp new-synps))
                  :guard-hints
                  (("Goal"
                    :in-theory (e/d () (rule-syntaxp
                                        rule-list-syntaxp
                                        RP-RULE-RW-LISTP
                                        update-rules-with-sc
                                        MAKE-FORMULA-BETTER
                                        CUSTOM-REWRITE-WITH-META-EXTRACT
                                        ))))
                  :stobjs (state)
                  :verify-guards t))
  (if (atom runes)
      nil
    (b* ((rest (get-rule-list (cdr runes) sc-alist new-synps warning
                               state))

         (rune (car runes))
         ((mv rule-name given-rule-type)
          (case-match rune
            ((type name . &) (mv name type))
            (& (mv rune nil))))
         ((when (not (symbolp rule-name)))
          (progn$
           (cw "WARNING! Problem reading the rune name. Skipping ~p0 ~%"
               rune)
           rest))
         ;; if the current rune is just a name, then treat that as a rewrite
         ;; rule for only the following tests. 
         (rule-type (mv-nth 0 (get-rune-name rule-name state)))
         (rule-type (if (or (equal given-rule-type ':executable-counterpart)
                            (equal given-rule-type ':e))
                        :executable-counterpart
                      rule-type))
         #|((when (and (equal rule-type ':definition)
                     given-rule-type
                     (or ;(str::strsuffixp "P" (symbol-name rule-name))
                         (acl2::recursivep rule-name nil (w state)))))
          (get-rule-list (cdr runes) sc-alist new-synps rule-fnc-alist state))||#
         #|((when (and (equal given-rule-type ':type-prescription)
                     (or (equal rule-type ':definition))))
          (get-rule-list (cdr runes) sc-alist new-synps rule-fnc-alist
         state))||#
         
         ((when (meta-rune-p rune)) ;; meta runes are (:meta meta-fncs . trig-fncs)
          (cons (make-custom-rule-for-meta rune);; let rhs be the name of the meta function.
                rest))
         ((when (and (not (equal rule-type ':rewrite))
                     (not (equal rule-type ':definition))
                     (not (equal rule-type ':type-prescription))))
          rest)
         (rule-new-synp (cdr (assoc-equal rule-name new-synps)))
         (rules (custom-rewrite-with-meta-extract rule-name rule-new-synp
                                                  warning  state))
         #|(rules (try-to-add-rule-fnc rules rule-fnc-alist))||#
         ((when (not (rule-list-syntaxp rules)))
          (or (cw "Warning a problem with rule-list ~p0 ~%" rules)
              rest))
         (rules (update-rules-with-sc rules sc-alist state)))
      (append rules rest))))

(defun to-fast-alist (alist)
  (declare (xargs :guard t))
  (make-fast-alist alist))
  ;;get a regular alist and convert it to a fast-alist
  #|(if (or (atom alist)
          (atom (car alist)))
      alist
    (hons-acons (caar alist) (cdar alist)
                (to-fast-alist (cdr alist))))||#

(defun rule-list-to-alist (rules)
  (declare (xargs :guard (weak-custom-rewrite-rule-listp rules)
                  :verify-guards nil))
  (if (atom rules)
      nil
    (b* ((rule (car rules))
         (rest (rule-list-to-alist (cdr rules))))
      (add-rule-to-alist rest rule))))

(defthm rule-list-to-alist-returns-alist
  (alistp (rule-list-to-alist rules)))

(verify-guards rule-list-to-alist)


(define get-rules (runes state &key new-synps warning)
  (declare (xargs :guard (alistp new-synps)
                  :stobjs (state)
                  :verify-guards t))
  (declare (ignorable new-synps))
  (b* ((sc-alist (table-alist 'rp-sc (w state)))
       ((when (not (symbol-symbol-alistp sc-alist)))
        (hard-error 'get-rules
                    "Table is broken. Side condition alist is damaged ~%"
                    nil))
       #|(rule-fnc-alist (make-fast-alist (table-alist 'rw-fncs (w state))))||#
       (rule-list (get-rule-list runes
                                 sc-alist
                                 new-synps
                                 warning
                                 #|rule-fnc-alist||#
                                 state))
       ((when (not (weak-custom-rewrite-rule-listp rule-list)))
        (hard-error
         'get-rules
         "Something is wrong with the rewrite rule list format"
         nil))
       #|(- (fast-alist-free rule-fnc-alist))||#
       (rules-alist (rule-list-to-alist rule-list))
       (rules-alist (to-fast-alist rules-alist)))
    rules-alist))

(defmacro rp-attach-sc (rule-name sc-rule-name)
  (declare (xargs :guard (and (symbolp rule-name)
                              (symbolp sc-rule-name))))
  `(make-event
    (if (sc-rule-p (meta-extract-formula ',rule-name state)
                   (meta-extract-formula ',sc-rule-name state))
        (b* ((sc-alist (table-alist 'rp-sc (w state)))
             (entry (assoc-eq ',rule-name sc-alist))
             (val (if entry
                      (cons ',sc-rule-name (cdr entry))
                    (cons ',sc-rule-name nil)))
             (?sc-alist (put-assoc ',rule-name val sc-alist)))
          `(table rp-sc ',',rule-name ',val))
      (value-triple :rule-attaching-failed))))


(progn
  (defund e/d-rp-rules-fn (rules state e/d)
    (declare (xargs :stobjs (state)))
    (if (atom rules)
        nil
      (b* ((rule (car rules))
           (rest (e/d-rp-rules-fn (cdr rules) state e/d))
           ((mv given-type name)
            (case-match rule ((type name . &) (mv type name)) (& (mv nil rule))))
           ((unless (symbolp name))
            (hard-error 'enable-rp-rules
                        "Rule name from ~p0 is not a symbolp ~%"
                        (list (cons #\0 rule))))
           (rune (get-rune-name name state))
           (rune (if given-type rule rune))
           (rest
            (if (not (consp (hons-assoc-equal rune (table-alist 'rp-rules (w state)))))
                (progn$
                 (and (or (atom rune)
                          (and (not (equal (car rune) ':definition))
                               (not (equal (car rune) ':executable-counterpart))))
                      (cw "Warning! ~p0 does not seem to be registered with ~
  rp::add-rp-rule. Will do that now, but be aware that it will have a higher priority. ~%"
                          rune))
                 (if (or (atom rune)
                         (not (equal (car rune) ':executable-counterpart)))
                     (cons `(table rp-rules ',rune '(:inside-out . t)) rest)
                   rest))
              rest))
           (rune-entry-value (cdr (hons-assoc-equal rune (table-alist 'rp-rules
                                                                      (w state)))))
           (both (case-match rune-entry-value
                   ((':both . &) t)
                   (& nil)))
           (outside-in (case-match rune-entry-value
                         ((':outside-in . &) t)
                         (& nil))))
        (case-match rune
          ((':executable-counterpart name)
           (cons (if e/d
                     `(enable-exc-counterpart ,name)
                   `(disable-exc-counterpart ,name))
                 rest))
          (&
           (cons `(table rp-rules ',rune ',(cond
                                            (both `(:both . ,e/d))
                                            (outside-in `(:outside-in . ,e/d))
                                            (t `(:inside-out . ,e/d))))
                 rest))))))

  (defmacro enable-rules (rules)
    `(make-event
      `(with-output
         :off :all
         (progn ,@(e/d-rp-rules-fn ,rules state t)))))

  (defmacro disable-rules (rules)
    `(make-event
      `(with-output
         :off :all
         (progn ,@(e/d-rp-rules-fn ,rules state nil)))))

  (defmacro disable-all-rules ()
    `(make-event
      (b* ((cur-table (table-alist 'rp-rules (w state)))
           (cur-table (loop$ for x in cur-table collect
                             (case-match x
                               ((rune . type)
                                (case-match type
                                  ((direction . &)
                                   (list* rune direction nil))
                                  (& (cons rune nil))))
                               (& x)))))
        `(table rp-rules nil ',cur-table :clear))))

  (defmacro disable-exc-counterpart (fnc)
    (declare (xargs :guard (symbolp fnc)))
    `(table rp-exc-rules ',fnc nil))

  (defmacro enable-exc-counterpart (fnc)
    (declare (xargs :guard (symbolp fnc)))
    `(table rp-exc-rules ',fnc t)))



(xdoc::defxdoc
 rp-ruleset
 :parents (rp-rewriter)
 :short "Functions to manage RP-Rewriter's ruleset"
 :long
 "<p>Users can use 
the functions below to register rules to RP-Rewriter's
 ruleset:</p>

<code> 
@('(rp::add-rp-rule <rule-name> 
                 &key (disabled 'nil)
                      (beta-reduce 'nil)
                      (hints 'nil)
                      (inside-out ':default)
                      (outside-in 'nil))')
</code>
 <p>This macro submits a table event that saves the given rule in the
 ruleset. The time you use submit this event will affect the priority the rule
 will have. If you choose to add the rule as disabled, you may use the
 corresponding key. </p>

<p> The beta-reduce key checks the RHS of the rule to see if it is a lambda
expression. If that is the case, then it calls @(see rp::defthm-lambda) to
create a new rule and save that instead. The name of the new rule will be
printed, and it will be disabled for ACL2. You need to use that new name while
enabling/disabling the added rule for RP-Rewriter. The hints key is only relevant when
defthm-lambda is called. </p>

<p> inside-out and outside-in keys determine whether or not the rule should be
an outside-in, inside-out or both. If you set inside-out to :default and
outside-in to t, then the rule will be an outside-in only. If you set both t,
it will be both; if you set only one of them to t, it will be only one. And,
users are not allowed to set both to nil. You may change the rewrite direction
of an already added rewrite rule by calling add-rp-rule again and by
reassigning the direction with these flags.</p>


<code> @('(rp::def-rp-rule <rule-name> <conjecture> <optional-hints> ...)') </code>
This macro has the
 same signature as defthm. It submits a @(see rp::defthm-lambda) event in case
RHS has a lambda expression. If it doesn't then defthm-lambda translates to defthm. It also submits a
 add-rp-rule event to save the rule in the rule-set. 

<code>
@('(rp::enable-rules <rules>)')
</code>
This macro submits an event to enable a list of
 rules from the given list.

<code> 
@('(rp::disable-rules <rules>)')
</code>
 The opposite of rp::enable-rules.


<code>@('(rp::disable-all-rules)')</code>

This submits an event and disables all the rewrite rules. 

<code> @('(rp::disable-exc-counterpart <fnc-name>)') </code> The executable
 counterparts are enabled by default for all functions and they belong to a
 different rule-set for rp-rewriter. This macro submits an event to disable the
 executable counterpart of given function.

 <code> @('(rp::enable-exc-counterpart <fnc-name>)') </code>
 The opposite of rp::disable-exc-counterpart.


"
 )


(xdoc::defxdoc
 add-rp-rule
 :parents (rp-other-utilities)
 :short "@(see rp::rp-ruleset)")


(xdoc::defxdoc
 rp::def-rp-rule
 :parents (rp-other-utilities)
 :short "Documentation under @(see rp::rp-ruleset).")

(xdoc::defxdoc
 rp::disable-rules
 :parents (rp-other-utilities)
 :short "Documentation under @(see rp::rp-ruleset)")

(xdoc::defxdoc
 rp::enable-rules
 :parents (rp-other-utilities)
 :short "Documentation under @(see rp::rp-ruleset)")

(xdoc::defxdoc
 disable-all-rules
 :parents (rp-other-utilities)
 :short "Documentation under @(see rp::rp-ruleset)")

(xdoc::defxdoc
 rp::disable-exc-counterpart
 :parents (rp-other-utilities)
 :short "Documentation under @(see rp::rp-ruleset)")

(xdoc::defxdoc
 rp::enable-exc-counterpart
 :parents (rp-other-utilities)
 :short "Documentation under @(see rp::rp-ruleset)")


(progn

  (defund get-disabled-exc-rules-from-table (rp-exc-rules)
    (declare (xargs :guard t))
    (if (atom rp-exc-rules)
        nil
      (b* ((rest (get-disabled-exc-rules-from-table (cdr rp-exc-rules))))
        (if (and (consp (car rp-exc-rules))
                 (symbolp (caar rp-exc-rules))
                 (not (cdar rp-exc-rules)))
            (cons (caar rp-exc-rules)
                  rest)
          rest))))



  (defund get-enabled-rules-from-table-aux (rp-rules)
    (declare (xargs :guard t))
    (if (atom rp-rules)
        (mv nil nil)
      (b* (((mv rest-inside-out rest-outside-in)
            (get-enabled-rules-from-table-aux (cdr rp-rules)))
           ((unless (consp (car rp-rules)))
            (mv rest-inside-out rest-outside-in))

           (rule (caar rp-rules))
           (value (cdar rp-rules))
           ((mv inside-out outside-in enabled)
            (case-match value
              ((':outside-in . enabled) (mv nil t enabled))
              ((':inside-out . enabled) (mv t nil enabled))
              ((':both . enabled) (mv t t enabled))
              (& (mv t nil value))))
           ((unless enabled)
            (mv rest-inside-out rest-outside-in)))
        (case-match rule
          ((:executable-counterpart &)
           (mv rest-inside-out rest-outside-in))
          (&
           (mv (if inside-out
                   (cons rule rest-inside-out)
                 rest-inside-out)
               (if outside-in
                   (cons rule rest-outside-in)
                 rest-outside-in)))))))
  
  
  #|(defund get-enabled-rules-from-table-aux (rp-rules-inorder)
    (declare (xargs :guard t))
    (if (atom rp-rules-inorder)
        (mv nil #|nil||# nil)
      (b* ((rule (and (consp (car rp-rules-inorder)) (caar rp-rules-inorder)))
           (rule-enabled (and (consp (car rp-rules-inorder)) (cdar rp-rules-inorder)))
           ((mv rest-rw rest-def)
            (get-enabled-rules-from-table-aux (cdr rp-rules-inorder))))
        (case-match rule
          ((:executable-counterpart &)
           (mv rest-rw rest-def))
          ((:definition . &)
           (if rule-enabled ;;(cdr (hons-get rule rp-rules))
               (mv rest-rw #|rest-ex||# (cons rule rest-def))
             (mv rest-rw #|rest-ex||# rest-def)))
          (& 
           (if rule-enabled ;;(cdr (hons-get rule rp-rules))
               (mv (cons rule rest-rw) #|rest-ex||# rest-def)
             (mv rest-rw #|rest-ex||# rest-def)))))))||#

  (local
   (defthm true-listp-get-enabled-rules-from-table-aux-for-guards
     (b* (((mv rules-rw #|rules-ex||# rules-def)
           (get-enabled-rules-from-table-aux rp-rules-inorder )))
       (and (true-listp rules-rw)
            #|(true-listp rules-ex)||#
            #|(symbol-alistp rules-ex)||#
            (true-listp rules-def)))
     :hints (("Goal"
              :in-theory (e/d (get-enabled-rules-from-table-aux) ())))))


  (define get-enabled-rules-from-table (state)
    (declare (xargs :stobjs (state)
                    :guard t))
    (b* ((world (w state))
         (rp-rules (table-alist 'rp-rules world))
         ((mv rules-inside-out rules-outside-in)
          (get-enabled-rules-from-table-aux rp-rules))
         (rp-exc-rules (table-alist 'rp-exc-rules world))
         (rules-ex (get-disabled-exc-rules-from-table rp-exc-rules)))
      (mv rules-inside-out
          rules-outside-in
          rules-ex)))

  #|(define get-enabled-rules-from-table (state)
    (declare (xargs :stobjs (state)
                    :guard t))
    (b* ((world (w state))
         (rp-rules (table-alist 'rp-rules world))
         (rp-rules-outside-in (table-alist 'rp-rules-outside-in world))
         ((mv rules-rw rules-def)
          (get-enabled-rules-from-table-aux rp-rules))
         ((mv rules-rw-oi rules-def-oi)
          (get-enabled-rules-from-table-aux rp-rules-outside-in))
         (rp-exc-rules (table-alist 'rp-exc-rules world))
         (rules-ex (get-disabled-exc-rules-from-table rp-exc-rules)))
      (mv (append rules-rw rules-def)
          (append rules-rw-oi rules-def-oi)
          rules-ex)))||#)





(define rp-state-init-rules-aux (rules-alist
                                 flg
                                 rp-state)
  (if (atom rules-alist)
      rp-state
    (b* ((rp-state
          (cond ((and (equal flg :inside-out)
                      (consp (car rules-alist))
                      (symbolp (caar rules-alist)))
                 (rules-alist-inside-out-put (caar rules-alist)
                                             (cdar rules-alist)
                                             rp-state))
                ((and (equal flg :outside-in)
                      (consp (car rules-alist))
                      (symbolp (caar rules-alist)))
                 (rules-alist-outside-in-put (caar rules-alist)
                                             (cdar rules-alist)
                                             rp-state))
                ((and (equal flg :exc)
                      (symbolp (car rules-alist)))
                 (disabled-exc-rules-put (car rules-alist)
                                         nil
                                         rp-state))
                (t rp-state))))
      (rp-state-init-rules-aux (cdr rules-alist) flg rp-state))))

(define rp-state-init-rules (runes-inside-out
                             runes-outside-in
                             (new-synps alistp)
                             rp-state
                             state)
  :verify-guards nil
  (b* ((- (and runes-outside-in (not runes-inside-out)
                   (cw "WARNING: You passed some values for runes-outside-in
but did not pass anything for runes. Assigning values to any one of those
values will cause runes to be not retrieved from the table.~%")))


       ((mv runes-inside-out runes-outside-in disabled-exc-rules)
            (if (or runes-inside-out runes-outside-in)
                (mv runes-inside-out runes-outside-in
                    (get-disabled-exc-rules-from-table
                     (table-alist 'rp-exc-rules (w state))))
              (get-enabled-rules-from-table state)))
       
       (rules-alist-inside-out (get-rules runes-inside-out state :new-synps new-synps))
       (rules-alist-outside-in (get-rules runes-outside-in state :new-synps
                                          new-synps))

       (len-disabled-exc-rules (len disabled-exc-rules))
       (rp-state (disabled-exc-rules-init len-disabled-exc-rules
                                          nil nil
                                          rp-state))       
       (len-rules-alist-inside-out (len rules-alist-inside-out))
       (rp-state (rules-alist-inside-out-init len-rules-alist-inside-out
                                              nil
                                              nil
                                              rp-state))
       (len-rules-alist-outside-in (len rules-alist-outside-in))
       (rp-state (rules-alist-outside-in-init len-rules-alist-outside-in
                                              nil
                                              nil
                                              rp-state))
       
       (rule-alist-inside-out (get-rules runes-inside-out state
                                         :new-synps new-synps))
       (rule-alist-outside-in (get-rules runes-outside-in state
                                         :new-synps new-synps))

       (rp-state (rp-state-init-rules-aux rule-alist-inside-out
                                          :inside-out
                                          rp-state))
       (rp-state (rp-state-init-rules-aux rule-alist-outside-in
                                          :outside-in 
                                          rp-state))
       (rp-state (rp-state-init-rules-aux disabled-exc-rules
                                          :exc 
                                          rp-state))

       (- (fast-alist-clean rule-alist-inside-out))
       (- (fast-alist-clean rule-alist-outside-in)))
    rp-state))
       

       
