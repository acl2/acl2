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
 (defun insert-iff-to-force (term iff-flg)
   (declare (xargs :guard t))
   (cond ((or (atom term)
              (quotep term))
          term)
         (t
          (case-match term
            (('implies p q)
             `(implies ,(insert-iff-to-force p t)
                       ,(insert-iff-to-force q t)))
            (('force x)
             (if iff-flg
                 `(force (if ,(insert-iff-to-force x iff-flg) 't 'nil))
               `(force ,(insert-iff-to-force x iff-flg))))
            (('if test then else)
             `(if ,(insert-iff-to-force test t)
                  ,(insert-iff-to-force then iff-flg)
                ,(insert-iff-to-force else iff-flg)))
            (&
             (cons (car term)
                   (insert-iff-to-force-lst (cdr term))))))))
 (defun insert-iff-to-force-lst (lst)
   (if (atom lst)
       nil
     (cons (insert-iff-to-force (car lst) nil)
           (insert-iff-to-force-lst (cdr lst))))))
   

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
                     :lhs lhs
                     :rhs rhs))
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
       (formula (insert-iff-to-force formula nil))
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

(defun attach-sc-to-rule (rule sc-formula)
  (declare (xargs :guard (and (rule-syntaxp rule))
                  :VERIFY-GUARDS t))
  (b* (#|((when (include-fnc (rp-rhs rule) 'if))
       (or (hard-error 'side-condition-check
       "We do not yet support side conditions for rules that ~
       have if statements on the right handside~%" nil)
       rule))||#)
    (case-match sc-formula
      (('implies scp q)
       (b* (((when (not (subsetp-equal (if-to-and-list scp)
                                       (if-to-and-list (rp-hyp rule)))))
             (or (hard-error 'side-condition-check
                             "hypothesis of side-condition rule should be a subset ~
  of the original rule ~%" nil)
                 rule))
            (sc-list (if-to-and-list q))
            (rule-rhs (rp-rhs rule))
            (rhs-updated (attach-sc-list-to-rhs rule-rhs sc-list))
            (rule (change custom-rewrite-rule rule
                          :rhs rhs-updated)))
         rule))
      (&
       (b* ((sc-list (if-to-and-list sc-formula))
            (rule-rhs (rp-rhs rule))
            (rhs-updated (attach-sc-list-to-rhs rule-rhs sc-list))
            (rule (change custom-rewrite-rule rule
                          :rhs rhs-updated)))
         rule)))))

(defun update-rule-with-sc-aux (rule sc-rule-names state)
  (declare (xargs :guard (and (symbol-listp sc-rule-names)
                              (rule-syntaxp rule))
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

(verify-guards update-rule-with-sc-aux
  :hints (("Goal"
           :in-theory (e/d () (rule-syntaxp
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
                              (rule-syntaxp rule))
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

(defun update-rules-with-sc (rules sc-alist state)
  (declare (xargs :guard (and (rule-list-syntaxp rules)
                              (symbol-symbol-alistp sc-alist))
                  :guard-hints (("Goal"
                                 :in-theory (e/d ()
                                                 (GET-VARS
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
  (b* ((lhs (access custom-rewrite-rule rule :lhs))
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

(define try-to-add-rule-fnc (rules rule-fnc-alist)
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
    rules))

(defun get-rule-list (runes sc-alist new-synps warning rule-fnc-alist state)
  (declare (xargs :guard (and (symbol-symbol-alistp sc-alist)
                              (alistp new-synps))
                  :guard-hints
                  (("Goal"
                    :in-theory (e/d () (rule-syntaxp
                                        update-rules-with-sc
                                        MAKE-FORMULA-BETTER
                                        CUSTOM-REWRITE-WITH-META-EXTRACT
                                        ))))
                  :stobjs (state)
                  :verify-guards t))
  (if (atom runes)
      nil
    (b* ((rune (car runes))
         ((mv rule-name given-rule-type)
          (case-match rune
            ((type name . &) (mv name type))
            (& (mv rune nil))))
         ((when (not (symbolp rule-name)))
          (progn$
           (cw "WARNING! Problem reading the rune name. Skipping ~p0 ~%"
               rune)
           (get-rule-list (cdr runes) sc-alist new-synps warning rule-fnc-alist state)))
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
          (get-rule-list (cdr runes) sc-alist new-synps rule-fnc-alist state))||#
         ((when (and (not (equal rule-type ':rewrite))
                     (not (equal rule-type ':definition))
                     (not (equal rule-type ':type-prescription))))
          (get-rule-list (cdr runes) sc-alist new-synps warning rule-fnc-alist state))
         (rule-new-synp (cdr (assoc-equal rule-name new-synps)))
         (rules (custom-rewrite-with-meta-extract rule-name rule-new-synp
                                                  warning  state))
         (rules (try-to-add-rule-fnc rules rule-fnc-alist))
         ((when (not (rule-list-syntaxp rules)))
          (or (cw "Warning a problem with rule-list ~p0 ~%" rules)
              (get-rule-list (cdr runes) sc-alist new-synps warning rule-fnc-alist state)))
         (rules (update-rules-with-sc rules sc-alist state)))
      (append rules (get-rule-list (cdr runes) sc-alist new-synps warning rule-fnc-alist state)))))

(defun to-fast-alist (alist)
  (declare (xargs :guard t))
  ;;get a regular alist and convert it to a fast-alist
  (if (or (atom alist)
          (atom (car alist)))
      alist
    (hons-acons (caar alist) (cdar alist)
                (to-fast-alist (cdr alist)))))

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
       (rule-fnc-alist (make-fast-alist (table-alist 'rw-fncs (w state))))
       (rule-list (get-rule-list runes
                                 sc-alist
                                 new-synps
                                 warning
                                 rule-fnc-alist
                                 state))
       ((when (not (weak-custom-rewrite-rule-listp rule-list)))
        (hard-error
         'get-rules
         "Something is wrong with the rewrite rule list format"
         nil))
       (- (fast-alist-free rule-fnc-alist))
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
            (if (not (consp (hons-assoc-equal rune (table-alist 'rp-rules-inorder (w state)))))
                (progn$
                 (if (or (atom rune)
                         (and (not (equal (car rune) ':definition))
                              (not (equal (car rune) ':executable-counterpart))))
                     (cw "Warning! ~p0 does not seem to be registered with ~
  rp::add-rp-rule. Will do that now, but be aware that it will have a higher priority. ~%"
                         rune)
                   nil)
                 (if (or (atom rune)
                         (not (equal (car rune) ':executable-counterpart)))
                     (cons `(table rp-rules-inorder ',rune nil) rest)
                   rest))
              rest)))
        (case-match rune
          ((':executable-counterpart name)
           (cons (if e/d
                     `(enable-exc-counterpart ,name)
                   `(disable-exc-counterpart ,name))
                 rest))
          (&
           (cons `(table rp-rules ',rune ,e/d) rest))))))

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
    `(table rp-rules nil nil :clear))

  (defmacro disable-exc-counterpart (fnc)
    `(table rp-exc-rules ',fnc nil))

  (defmacro enable-exc-counterpart (fnc)
    `(table rp-exc-rules ',fnc t)))



(xdoc::defxdoc
 rp-ruleset
 :parents (rp-rewriter)
 :short "Functions to manage RP-Rewriter's ruleset"
 :long
 "Users can use 
the functions below to register rules to RP-Rewriter's
 ruleset:

<code> 
@('(rp::add-rp-rule <rule-name> 
                 &optional (disabled 'nil))')
</code>
 This macro submits a table event that saves the given rule in the
 ruleset. The time you use submit this event will affect the priority the rule
 will have. If you choose to add the rule as disabled, you may use the
 corresponding key.

<code> @('(rp::def-rp-rule <rule-name> <conjecture> <optional-hints> ...)') </code>
This macro has the
 same signature as defthm, and it submits a defthm event. It also submits a
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
 :short "@(see rp::rp-ruleset)")


(xdoc::defxdoc
 rp::def-rp-rule
 :short "Documentation under @(see rp::rp-ruleset).")

(xdoc::defxdoc
 rp::disable-rules
 :short "Documentation under @(see rp::rp-ruleset)")

(xdoc::defxdoc
 rp::enable-rules
 :short "Documentation under @(see rp::rp-ruleset)")

(xdoc::defxdoc
 disable-all-rules
 :short "Documentation under @(see rp::rp-ruleset)")

(xdoc::defxdoc
 rp::disable-exc-counterpart
 :short "Documentation under @(see rp::rp-ruleset)")

(xdoc::defxdoc
 rp::enable-exc-counterpart
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
            (hons-acons (caar rp-exc-rules) nil
                        rest)
          rest))))

  
  
  (defund get-enabled-rules-from-table-aux (rp-rules-inorder rp-rules)
    (declare (xargs :guard t))
    (if (atom rp-rules-inorder)
        (mv nil #|nil||# nil)
      (b* ((rule (and (consp (car rp-rules-inorder)) (caar rp-rules-inorder)))
           ((mv rest-rw #|rest-ex||# rest-def)
            (get-enabled-rules-from-table-aux (cdr rp-rules-inorder)
                                              rp-rules)))
        (case-match rule
          ((:executable-counterpart &)
           (mv rest-rw #|rest-ex||# rest-def)
           #|(b* ((rp-rules-entry (hons-get rule rp-rules)))
           (if (or (and rp-rules-entry ;
           (not (cdr rp-rules-entry))) ;
           (not (symbolp name))) ;
           (mv rest-rw rest-ex rest-def) ;
           (mv rest-rw (hons-acons name nil rest-ex) rest-def)))||#)
          ((:definition . &)
           (if (cdr (hons-get rule rp-rules))
               (mv rest-rw #|rest-ex||# (cons rule rest-def))
             (mv rest-rw #|rest-ex||# rest-def)))
          (& 
           (if (cdr (hons-get rule rp-rules))
               (mv (cons rule rest-rw) #|rest-ex||# rest-def)
             (mv rest-rw #|rest-ex||# rest-def)))))))

  (local
   (defthm true-listp-get-enabled-rules-from-table-aux-for-guards
     (b* (((mv rules-rw #|rules-ex||# rules-def)
           (get-enabled-rules-from-table-aux rp-rules-inorder rp-rules)))
       (and (true-listp rules-rw)
            #|(true-listp rules-ex)||#
            #|(symbol-alistp rules-ex)||#
            (true-listp rules-def)))
     :hints (("Goal"
              :in-theory (e/d (get-enabled-rules-from-table-aux) ())))))


  (defund get-enabled-rules-from-table (state)
    (declare (xargs :stobjs (state)
                    :guard t))
    (b* ((world (w state))
         (rp-rules-inorder (table-alist 'rp-rules-inorder world))
         (rp-rules (make-fast-alist (table-alist 'rp-rules world)))
         ((mv rules-rw #|rules-ex||# rules-def)
          (get-enabled-rules-from-table-aux rp-rules-inorder rp-rules))
         (- (fast-alist-free rp-rules))

         (rp-exc-rules (table-alist 'rp-exc-rules world))
         (rules-ex (get-disabled-exc-rules-from-table rp-exc-rules)))
      (mv (append rules-rw rules-def) rules-ex))))

