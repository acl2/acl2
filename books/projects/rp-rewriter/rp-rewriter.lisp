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

;; The file that includes the main rewriter functions.
;; The mutually recursing rewriter function is "rp-rw"
;; rp-rw-aux is a preprocessor called prior to rp-rw

(in-package "RP")

(include-book "macros")
(include-book "aux-functions")

(include-book "rp-state-functions")

(include-book "eval-functions")

(local
 (include-book "proofs/local-lemmas"))

(local
 (include-book "proofs/aux-function-lemmas"))

(local
 (in-theory (disable state-p)))

(local
 (in-theory (disable RP-STATEP)))

(local
 (in-theory (enable rule-syntaxp)))

(defconst *rp-hard-error-returns-nilp* t)

(encapsulate
  nil

  (defun remove-rp-from-bindings (bindings)
    (declare (xargs  :mode :logic
                     :guard (alistp bindings)))
    (if (atom bindings)
        nil
      (b* ((binding (car bindings))
           (val (cdr binding)))
        (cons-with-hint
         (cons-with-hint (car binding)
                         (ex-from-rp val)
                         binding)
         (remove-rp-from-bindings (cdr bindings))
         bindings)))))

(defun quote-listp (subterm)
  (declare (xargs  :mode :logic
                   :guard t))
  ;; checks whether all the subterms are quotep's
  (if (atom subterm)
      t
    (and (consp (car subterm))
         (acl2::fquotep (car subterm))
         (quote-listp (cdr subterm)))))

(mutual-recursion

 (defun rp-apply-bindings (term bindings )
   (declare (xargs  :mode :logic
                    :guard (and #|(rp-termp term)||#
                            (alistp bindings))))
   ;; apply the given bindings to the given term
   ;; That term can be anything but it is expected to be hyp or rhs of a rule.
   ;; Lambda expressions are not supported and it is enforced by rp-termp
   (cond ((acl2::variablep term)
          (b* ((binding (assoc-equal term bindings))
               (res (if (consp binding)
                        (cdr binding)
                      (progn$ (cw "warning binding problem! ~p0 ~%" term)
                              term))))
            res))
         ((acl2::fquotep term) term)
         ((is-synp term) ''t)
         (t
          (cons-with-hint (car term)
                          (rp-apply-bindings-subterms (cdr term) bindings )
                          term))))

 (defun rp-apply-bindings-subterms (subterms bindings )
   (declare (xargs  :mode :logic
                    :guard (and #|(rp-term-listp subterms)||#
                            (alistp bindings))))
   (if (atom subterms)
       subterms
     (cons-with-hint (rp-apply-bindings (car subterms) bindings )
                     (rp-apply-bindings-subterms (cdr subterms) bindings )
                     subterms))))

(encapsulate
  nil

  (local
   (in-theory (enable is-rp-implies)))

  (defconst *match-lhs-rp-equal-cnt*
    2)

  (mutual-recursion
   (defun rp-match-lhs (term rule-lhs context acc-bindings)
     (declare (xargs :measure (acl2::acl2-count rule-lhs)
                     :guard (and (alistp acc-bindings)
                                 (rp-termp term)
                                 (rp-termp rule-lhs))
                     #|(and (rp-termp term)
                     (bindings-alistp acc-bindings) ;
                     (rp-termp rule-lhs) ;
                     )||#
                     :verify-guards nil
                     :mode :logic))
     "Matches the term to rule-lhs. Put the bindings in the accumulator
   acc-bindings, and also grows the given context with the rp terms that might
   be encountered while matching. Returns (mv context bindings bindings-valid)"

     (if (atom rule-lhs) ;; it is a variable bind it.
         (b* ((other-binding (assoc-eq rule-lhs acc-bindings))
              (other-entry (if (consp other-binding) (cdr other-binding)
                             nil))
              (equiv (and other-entry
                          (or ;(equal term other-entry)
                           (rp-equal-cnt term other-entry
                                         *match-lhs-rp-equal-cnt*)))))
           (cond
            (equiv ;; duplicate but equiv
             (mv context acc-bindings t))
            (other-entry ;;duplicate but not equiv
             (mv context acc-bindings nil))
            (t ;; no duplicate
             (mv context (acons rule-lhs term
                                acc-bindings)
                 t))))
       (b* ((term (ex-from-falist term))
            ((mv context term-w/o-rp)
             ;; if term is wrapped in rp; take it out and add type to the
             ;; new context
             ;; no need to expand the context when (atom rule-lhs) because check
             ;; that check is made with a different function
             ;; (check-if-relieved-with-rp) in rp-rw
             (extract-from-rp-with-context term context)))
         (cond
          ((acl2::fquotep rule-lhs) ;; rule is quoted should be the same as the term.
           (mv context acc-bindings (equal rule-lhs term-w/o-rp)))
          ((should-term-be-in-cons rule-lhs term-w/o-rp) ;; if the rule-lhs is of
           ;; the form (cons x y) while the term is quoted like '(first rest); rewrite the term as
           ;; (cons 'first 'rest) so that we can match the rule to the term
           (let ((term-in-cons (put-term-in-cons term-w/o-rp)))
             (rp-match-lhs-subterms (cdr term-in-cons) (cdr rule-lhs) context
                                    acc-bindings)))
          ((consp term-w/o-rp) ;; both term and rule is consp,
           (cond
            ((eq (car rule-lhs) (car term-w/o-rp))
             ;; if their function name be the same, keep on matching.
             (rp-match-lhs-subterms (cdr term-w/o-rp) (cdr rule-lhs) context
                                    acc-bindings))
            (t (mv context acc-bindings nil))))
          (t ;; rule is consp but term isn't. then we cannot match this rule to
           ;; the tem.
           (mv context acc-bindings nil))))))

   (defun rp-match-lhs-subterms (subterms sublhs context acc-bindings)
     (declare (xargs :measure (acl2::acl2-count sublhs)
                     :guard (and (alistp acc-bindings)
                                 (rp-term-listp subterms)
                                 (rp-term-listp sublhs))
                     #|(and (rp-term-listp subterms)
                     (bindings-alistp acc-bindings) ;
                     (rp-term-listp sublhs))||#
                     :verify-guards nil
                     :mode :logic))
     (cond
      ((or (atom sublhs)
           (atom subterms))
       (mv context acc-bindings (and (atom sublhs)
                                     (atom subterms))))
      (t
       (b* (((mv context1 acc-bindings1 valid)
             (rp-match-lhs (car subterms) (car sublhs) context acc-bindings))
            ((when (not valid)) ;; stop trying if not valid.
             (mv context acc-bindings1 nil)))
         (rp-match-lhs-subterms (cdr subterms) (cdr sublhs) context1
                                acc-bindings1))))))

  (mutual-recursion
   (defun rp-does-lhs-match (term rule-lhs)
     (declare (xargs :measure (acl2::acl2-count rule-lhs)
                     :guard (and #|(rp-termp term)||#
                             (rp-termp rule-lhs))
                     :mode :logic))
     "Optional check for rule matching before attempting to bind the variable
   with rp-match-lhs. It is used to save from unnecessary consing and increase
   the performance. Checks if all the function symbol from term matches rule-lhs"
     (cond
      ((atom rule-lhs) t)
      ((acl2::fquotep rule-lhs)
       (let ((term-w/o-rp (ex-from-rp-loose term)))
         (equal rule-lhs term-w/o-rp)))
      (t
       (b* ((term (ex-from-falist term))
            (term-w/o-rp (ex-from-rp-loose term)))
         (and (consp term-w/o-rp)
              (b* ((term- (if (should-term-be-in-cons rule-lhs term-w/o-rp)
                              (put-term-in-cons term-w/o-rp)
                            term-w/o-rp)))
                (and (eq (car rule-lhs) (car term-))
                     (rp-does-lhs-match-subterms (cdr term-) (cdr rule-lhs)))))))))

   (defun rp-does-lhs-match-subterms (subterms sublhs )
     (declare (xargs :measure (acl2::acl2-count sublhs)
                     :guard (and #|(rp-term-listp subterms)||#
                             (rp-term-listp sublhs))
                     :mode :logic))
     (cond
      ((or (atom sublhs)
           (atom subterms))
       (and (atom sublhs)
            (atom subterms)))
      (t
       (and
        (rp-does-lhs-match (car subterms) (car sublhs))
        (rp-does-lhs-match-subterms (cdr subterms) (cdr sublhs)))))))

  (define rp-match-lhs-precheck (term rule-lhs)
    :inline t
    :guard (and (consp term)
                (consp rule-lhs)
                (not (eq (car rule-lhs) 'quote))
                (rp-termp rule-lhs)
                (not (eq (car term) 'quote)))
    (rp-does-lhs-match-subterms (cdr term) (cdr rule-lhs)))

  (defmacro rp-get-rules-for-term (fn-name rules)
    `(cdr (hons-get ,fn-name ,rules))))

(defun rp-check-context (term context iff-flg)
  (declare (xargs :mode :logic
                  :guard (and #|(context-syntaxp context)||#
                          (booleanp iff-flg))
                  :verify-guards nil))
  ;; Check if the term simplifies with given context.
  ;; Argument "context" is expected to have only clauses that define type or of the
  ;; form (equal x y)
  (if (atom context)
      term
    (let ((c (car context)))
      (cond ((case-match c (('equal m &) (rp-equal m term)) (& nil))
             (caddr c))
            ((and iff-flg (case-match c (('if m ''nil ''t) (rp-equal m term))))
             ''nil)
            ((and iff-flg (rp-equal-cnt c term 1))
             ''t)
            (t
             (rp-check-context term (cdr context) iff-flg))))))

(mutual-recursion

 (defun rp-get-dont-rw (term)
   (declare (xargs :mode :logic
                   :measure (acl2-count term)
                   :guard t))
   ;; the variable name should be changed to term.
   ;; from using the raw rhs/lhs of the rule, get the locations of the variables and
   ;; mark them with t, the rest will be nil.
   ;; for example if term is (b+ a (b+ b c)),
   ;; returned value is going to be (nil t (nil t t)) so that a b and c won't be
   ;; rewritten again but new terms starting with b+ will be.
   (cond ((or (atom term)
              (acl2::fquotep term))
          t)
         (t (cons nil
                  (rp-get-dont-rw-subterm (cdr term))))))

 (defun rp-get-dont-rw-subterm (subterm)
   (declare (xargs :mode :logic
                   :measure (acl2-count subterm)
                   :guard t))
   (if (atom subterm)
       nil
     (cons (rp-get-dont-rw (car subterm))
           (rp-get-dont-rw-subterm (cdr subterm))))))

(progn
  ;; Executable counterpart related functions.
  (defun unquote-all (lst)
    (declare (xargs :guard t))
    (if (atom lst)
        lst
      (cons-with-hint
       (if (and (quotep (car lst))
                (consp (cdar lst)))
           (unquote (car lst))
         (car lst))
       (unquote-all (cdr lst))
       lst)))

  (defun magic-ev-fncall-wrapper (ACL2::FN ARGS STATE
                                           ACL2::HARD-ERROR-RETURNS-NILP ACL2::AOK)
    (declare (xargs :mode :logic
                    :guard t
                    :stobjs (state)))
    (magic-ev-fncall ACL2::FN ARGS STATE
                     ACL2::HARD-ERROR-RETURNS-NILP ACL2::AOK))

  (defun rp-ex-counterpart (term rp-state state)
    (declare (xargs  :mode :logic
                     :guard (rp-termp term)
                     :stobjs (state rp-state)))
    ;; if the term can be simplified using executable counterpart, do that.
    ;; rp-ex-cp-fnc is a function defined in macros.lisp.
    ;; it supports only the given functions.

    ;; returns (mv term-changed term)
    (cond
     ((or (atom term)
          (eq (car term) 'quote)
          (eq (car term) 'list)
          (not (quote-listp (cdr term)))
          (disabled-exc-rules-boundp (car term) rp-state))
      (mv term rp-state))
     ((case-match term ((fn ('quote &)) (or (equal fn 'car)
                                            (equal fn 'cdr)
                                            (equal fn 'natp)
                                            (equal fn 'not)
                                            (equal fn 'bitp)
                                            (equal fn 'zp)
                                            (equal fn 'integerp))))
      (b* ((fn (car term))
           (val (unquote (cadr term)))
           (res (case fn
                  (car (if (consp val) (car val) nil))
                  (cdr (if (consp val) (cdr val) nil))
                  (not (not val))
                  (zp (if (integerp val) (<= val 0) t))
                  (natp (natp val))
                  (bitp (bitp val))
                  (integerp (integerp val))))
           (rp-state (rp-stat-add-to-rules-used fn nil t rp-state))
           (rp-state (increment-rw-stack-size rp-state)))
        (mv (list 'quote res) rp-state)))
     (t
      (b* ((fn (car term))
           ((unless (and (symbolp fn)
                         (acl2::logicp fn (w state))))
            (progn$
             (hard-error
              'rp-ex-counterpart
              "Error with ex. counterpart: not a logic-mode function: ~p0 ~%"
              (list (cons #\0 fn)))
             (mv term rp-state)))
           #|(term (if (equal fn 'list) (rp-untrans term) term))||#
           ((mv err val)
            (magic-ev-fncall-wrapper fn (unquote-all (cdr term)) state *rp-hard-error-returns-nilp* nil))
           (rp-state (rp-stat-add-to-rules-used fn nil t rp-state))
           (rp-state (increment-rw-stack-size rp-state)))
        (mv (if err
                (progn$
                 (fmt-to-comment-window "Error with ex. counterpart: ~p0 for term: ~p1 ~%"
                                        (pairlis2 acl2::*base-10-chars* (list val term))
                                        0
                                        '(nil 8 10 nil)
                                        NIL)
                 term)
              (list 'quote val))
            rp-state))))))

(defun rp-extract-context (term)
  (declare (xargs  :mode :logic
                   :guard t))
  ;; get an "if" statement as a term and return it into a list of assumptions
  ;; if possible.
  ;; For example (if (if a (if b nil) nil) nil) will return (a b c)
  ;; used by rp-rw-if
  (case-match
    term
    (('if a b ''nil)
     (append (rp-extract-context a)
             (rp-extract-context b)))
    ;; NOTE !!!!!!!!!!!!!!!!!!!!!!!!!!!!
    ;; here there could be another case for ('if a ''nil b) and extract context
    ;; for (negate a) and b. Will implement later...
    (('if & & &)
     (progn$
      ;; do not print this warning in case of "not" 
      (case-match term
          (('if & ''nil ''t) nil)
          (& (cw "WARNING! (if a b c) unsupported case-split may be required. ~%")))
      (cons term nil)))
    (&
     (cons term nil))))

(encapsulate
  nil

  ;; Events for synp relief.

  (defun rp-ev-fncall (fn-name params var-bindings  state)
    (declare (xargs  :stobjs state
                     :guard (and
                             #|(rp-term-listp params)||#
                             (alistp var-bindings))
                     :mode :logic))
    (b* ((params (rp-apply-bindings-subterms params var-bindings))
         ((mv err val)
          (magic-ev-fncall fn-name (unquote-all params) state *rp-hard-error-returns-nilp* nil)))
      (if err
          (progn$ (hard-error 'rp-ev-fncall
                              "Magic-ev-fncall error for syntaxp check. val: ~p0 for term: ~p1 ~%"
                              (list (cons #\0 val)
                                    (cons #\1 (cons fn-name params))))
                  ''nil)
        (list 'quote val))))

  (mutual-recursion

   (defun rp-exc-all (term var-bindings state)
     (declare (xargs  :stobjs state
                      :guard (and
                              (alistp var-bindings)
                              #|(rp-termp term)||#
                              )
                      :verify-guards nil
                      :mode :logic))
     ;; dives into subterms and executes everything.
     ;; guard should be that the term is executable.
     ;; term could be a bunch of different functions nested within each other.
     (cond
      ((atom term)
       term)
      ((acl2::fquotep term) term)
      ((case-match term (('if & & &) t) (& nil))
       ;; if we don't ckeck the if statement and run everything:
       ;; 1. the performance could be bad.
       ;; 2. guards may fail for one of the branches
       (b* ((cond-rw (rp-exc-all (cadr term) var-bindings  state))
            ((when (equal cond-rw ''nil))
             (rp-exc-all (cadddr term) var-bindings  state))
            ((when (nonnil-p cond-rw))
             (rp-exc-all (caddr term) var-bindings  state)))
         (progn$ (cw "Error in executing an if statement: ~%~p0~%" term)
                 term)))
      (t
       (rp-ev-fncall (car term)
                     (rp-exc-all-subterms (cdr term) var-bindings state)
                     var-bindings
                     state))))

   (defun rp-exc-all-subterms (subterms var-bindings  state)
     (declare (xargs  :stobjs state
                      :guard (and
                              (alistp var-bindings)
                              #|(rp-term-listp subterms)||#
                              )
                      :verify-guards nil
                      :mode :logic))
     (cond
      ((atom subterms)
       subterms)
      (t
       (cons-with-hint (rp-exc-all (car subterms) var-bindings  state)
                       (rp-exc-all-subterms (cdr subterms) var-bindings  state)
                       subterms)))))
  (local
   (encapsulate
     nil

     (set-state-ok t)
     (make-flag rp-exc-all :defthm-macro-name defthm-rp-exc-all)

     (defthm-rp-exc-all
       (defthm pseudo-termp-rp-exc-all
         (implies (rp-termp term)
                  (rp-termp (rp-exc-all term var-bindings  state)))
         :flag rp-exc-all)
       (defthm pseudo-termp-rp-exc-all-subterms
         (implies (rp-term-listp subterms)
                  (rp-term-listp (rp-exc-all-subterms subterms var-bindings  state)))
         :flag rp-exc-all-subterms))))

  (verify-guards rp-exc-all)

  (defun check-synp-syntax-aux (term)
    (declare (xargs :guard (case-match term (('synp & & ('quote &)) t) (&
                                                                        nil))))
    ;;our synp syntax check while proving the theorems are too weak and does
    ;;not make sure that (unquote (cadddr term)) is rp-termp where term is
    ;;a (synp & & &). So we need to run that check before extracting the
    ;;function call from synp. This check can get a little expensive when we do
    ;;it repeatedly with the same lemma so we wrap this check with
    ;;check-synp-syntax-aux and memoize that.
    (rp-termp (unquote (cadddr term))))

  #|(memoize 'check-synp-syntax-aux)||#

  (mutual-recursion

   (defun rp-rw-relieve-synp (term bindings  state)
     (declare (xargs  :stobjs state
                      :guard (and #|(rp-termp term)||#
                              (alistp bindings)
                              )
                      :mode :logic))
     "Relieve syntaxp by binding the variables and executing all the function
      calls in syntaxp. returns t if syntaxp test passes, nil otherwise"
     (cond
      ((atom term) t)
      ((acl2::fquotep term) t)
      ((and (case-match term (('synp & & ('quote &)) t) (& nil))
            #|(check-synp-syntax-aux term)||#)
       (b* ((hyp (unquote (cadddr term)))
            (exc (rp-exc-all hyp bindings state))
            (res (nonnil-p exc)))
         res))
      (t (rp-rw-relieve-synp-subterms (cdr term) bindings  state))))

   (defun rp-rw-relieve-synp-subterms (subterms bindings  state)
     (declare (xargs  :stobjs state
                      :guard (and #|(rp-term-listp subterms)||#
                              (alistp bindings)
                              )
                      :mode :logic))
     (if (atom subterms)
         t
       (and (rp-rw-relieve-synp (car subterms) bindings  state)
            (rp-rw-relieve-synp-subterms (cdr subterms) bindings
                                         state)))))

  (defund rp-rw-relieve-synp-wrap (term  bindings  state)
    (declare (xargs  :stobjs (state)
                     :guard (and #|(rp-termp term)||#
                             (alistp bindings)
                             )
                     :verify-guards nil))
    (or
     (not (include-fnc term 'synp))
     (rp-rw-relieve-synp term
                         bindings
                         state)))

  (defund remove-rp-from-bindings-for-synp (rule var-bindings)
    (declare (xargs :guard (and (rule-syntaxp rule)
                                (not (rp-rule-metap rule))
                                (alistp var-bindings))))
    ;; remove the first rp wrapper from bindings if the hypotheses of the rule
    ;; includes syntaxp.
    (if (include-fnc (rp-hyp rule) 'synp)
        (remove-rp-from-bindings var-bindings)
      var-bindings)))

(progn
  (encapsulate
    ((rp-rw-meta-rule (term meta-fnc-name dont-rw context rp-state state)
                      (mv t t rp-state)
                      :guard (rp-termp term)
                      :stobjs (state rp-state))
     (rp-rw-preprocessor (term context rp-state state)
                         t
                         :guard (rp-termp term)
                         :stobjs (state rp-state))
     (rp-rw-postprocessor (term context rp-state state)
                          t
                          :guard (rp-termp term)
                          :stobjs (state rp-state))
     (rp-formula-checks (state) t :stobjs (state)))
    (local
     (defun rp-rw-meta-rule (term meta-fnc-name dont-rw context rp-state state)
       (declare (ignorable term meta-fnc-name dont-rw context rp-state state)
                (xargs :guard (rp-termp term))
                (xargs :stobjs (state rp-state)))
       (mv term nil rp-state)))

    (local
     (defun rp-rw-preprocessor (term  context rp-state state)
       (declare (ignorable term  context rp-state state)
                (xargs :guard (rp-termp term))
                (xargs :stobjs (state rp-state)))
       term))

    (local
     (defun rp-rw-postprocessor (term  context rp-state state)
       (declare (ignorable term  context rp-state state)
                (xargs :guard (rp-termp term))
                (xargs :stobjs (state rp-state)))
       term))

    (local
     (defun rp-formula-checks (state)
       (declare (xargs :stobjs (state))
                (ignorable state))
       t))

    (defthm rp-rw-meta-rule-valid-eval
      (implies (and (rp-termp term)
                    (rp-term-listp context)
                    (valid-sc term a)
                    (valid-sc-subterms context a)
                    (rp-evl-meta-extract-global-facts)
                    (rp-formula-checks state)
                    (rp-statep rp-state))
               (b* (((mv res-term ?dont-rw ?res-rp-state)
                     (rp-rw-meta-rule term meta-fnc-name dont-rw context rp-state state)))
                 (and (valid-sc res-term a)
                      (equal (rp-evlt res-term a)
                             (rp-evlt term a))))))

    (defthm rp-rw-meta-rule-rp-state-preservedp
      (implies (rp-statep rp-state)
               (b* (((mv ?res-term ?dont-rw res-rp-state)
                     (rp-rw-meta-rule term meta-fnc-name dont-rw context rp-state state)))
                 (rp-state-preservedp rp-state res-rp-state))))

    (defthm rp-rw-meta-rule-valid-rp-termp
      (implies (rp-termp term)
               (b* (((mv res-term ?dont-rw ?rp-state)
                     (rp-rw-meta-rule term meta-fnc-name dont-rw context rp-state state)))
                 (rp-termp res-term))))

    (defthm rp-rw-preprocessor-valid-eval
      (implies (and (rp-termp term)
                    (rp-term-listp context)
                    (valid-sc term a)
                    (valid-sc-subterms context a)
                    (rp-evl-meta-extract-global-facts)
                    (rp-formula-checks state)
                    (rp-statep rp-state))
               (b* ((res-term (rp-rw-preprocessor term context rp-state state)))
                 (and (valid-sc res-term a)
                      (iff (rp-evlt res-term a)
                           (rp-evlt term a))))))

    (defthm rp-rw-preprocessor-valid-rp-termp
      (implies (rp-termp term)
               (b* ((res-term (rp-rw-preprocessor term context rp-state state)))
                 (rp-termp res-term))))

    (defthm rp-rw-postprocessor-valid-eval
      (implies (and (rp-termp term)
                    (rp-term-listp context)
                    (valid-sc term a)
                    (valid-sc-subterms context a)
                    (rp-evl-meta-extract-global-facts)
                    (rp-formula-checks state)
                    (rp-statep rp-state))
               (b* ((res-term
                     (rp-rw-postprocessor term context rp-state state)))
                 (and (valid-sc res-term a)
                      (iff (rp-evlt res-term a)
                           (rp-evlt term a))))))

    (defthm rp-rw-postprocessor-valid-rp-termp
      (implies (rp-termp term)
               (b* ((res-term
                     (rp-rw-postprocessor term context rp-state state)))
                 (rp-termp res-term)))))

  (defund rp-rw-meta-rule-main (term rule dont-rw context rp-state state)
    (declare (xargs  :stobjs (rp-state state)
                     :verify-guards nil
                     :guard (and (rp-termp term)
                                 (rule-syntaxp rule)
                                 (rp-rule-metap rule))))
    (b* (((mv res-term dont-rw rp-state)
          (rp-rw-meta-rule term (rp-rule-meta-fnc rule) dont-rw context
                           rp-state state))
         (term-changed (not (equal res-term term)))
         (rp-state (rp-stat-add-to-rules-used rule (if term-changed nil 'failed) nil
                                              rp-state))
         (rp-state (if term-changed
                       (rp-state-push-meta-to-rw-stack rule term res-term ;
                                                       rp-state)          ;
                     rp-state)))
      (mv term-changed res-term dont-rw rp-state))))

(defun rp-rw-rule-aux (term rules-for-term context iff-flg state)
  (declare (xargs :mode :logic
                  :verify-guards nil
                  :stobjs (state)
                  :guard (and
                          (rp-termp term)
                          (consp term)
                          (not (equal (car term) 'quote))
                          (rule-list-syntaxp rules-for-term)
                          #|(context-syntaxp context)||#)))
  ;; if rules-for-term-rest is not nil, the first element is the applied ruled.
  ;; rules-for-term-rest is always subsetp of rules-for-term.
  "Search the rules for the term and try to find a matching one.
returns (mv rule rules-rest bindings rp-context)"
  (if (atom rules-for-term)
      (mv nil nil nil context)
    (b* ((rule (car rules-for-term))
         ((when (rp-rule-metap rule))
          (mv rule (cdr rules-for-term)  nil context))
         ;; if rule has is an iff relation and iff-flg is not set, then keep searching.
         ((when (and (rp-iff-flag rule)
                     (not iff-flg)))
          (rp-rw-rule-aux term (cdr rules-for-term) context iff-flg state))
         (lhs (rp-lhs rule))
         ((mv rp-context bindings bindings-valid)
          (if (rp-match-lhs-precheck term lhs) ;(rp-does-lhs-match term lhs)
              (rp-match-lhs term lhs context nil)
            (mv context nil nil))))
      (if bindings-valid
          (mv rule (cdr rules-for-term)  bindings rp-context)
        (rp-rw-rule-aux term (cdr rules-for-term) context iff-flg state)))))

(encapsulate
  nil

  (local
   (in-theory (enable is-rp)))

  (defund check-if-relieved-with-rp-aux (fnc param)
    (declare (xargs
              :verify-guards nil
              :guard (rp-termp param)))
    (cond
     ((mbe :logic (is-rp param)
           :exec (is-rp-loose param))
      (or (equal fnc (cadr (cadr param)))
          (check-if-relieved-with-rp-aux fnc (caddr param))))
     (t nil)))

  ;; if we encounter a term like (evenp (rp 'evenp x)), we want to return ''t
  ;; when iff-flg=t
  ;; similarly it should work for cases where rp wrappers are in a chain.
  ;; (evenp (rp 'integerp (rp 'evenp x))) should return ''t.

  (defund check-if-relieved-with-rp (term)
    (declare (xargs
              :verify-guards nil
              :guard (rp-termp term)))
    (case-match term
      ((fnc param) ;; if a function with single parameter.
       (if (eq fnc 'quote)
           nil
         (check-if-relieved-with-rp-aux fnc param)))
      (& nil))))

(encapsulate
  nil
  (defun rp-rw-fix-hard-error-alist (alist)
    (declare (xargs :guard t))
    (case-match alist
      (('cons ('cons ('quote a) b) rest)
       (cons (cons a b)
             (rp-rw-fix-hard-error-alist rest)))
      (('cons ('quote x) rest)
       (cons x
             (rp-rw-fix-hard-error-alist rest)))
      (('quote x)
       x)
      (''nil
       nil)
      (& alist)))

  (defun rp-rw-fix-cw-list (list)
    (declare (xargs :guard t))
    (case-match list
      (('cons a rest)
       (cons a
             (rp-rw-fix-cw-list rest)))
      (''nil
       nil)
      (& nil)))

  (local
   (defthm true-listp-rp-rw-fix-cw-list
     (true-listp (rp-rw-fix-cw-list list))))

  (defun rp-rw-check-hard-error-or-cw (term rp-state)
    (declare (xargs :stobjs (rp-state )))
    (case-match term
      (('hard-error ('quote ctx) ('quote str) alist)
       (progn$
        (rp-state-print-rules-used rp-state)
        (hard-error ctx str (rp-rw-fix-hard-error-alist alist))))
      (('fmt-to-comment-window ('quote &) ('quote &)
                               ('quote &) ('quote &) ('quote &))
       ;; if all arguments are quoted, then executable counterpart will be
       ;; triggered anyways, so dont do anything.
       nil)
      (('fmt-to-comment-window ('quote str) ('acl2::pairlis2 ''(#\0 #\1 #\2 #\3 #\4
                                                                #\5 #\6 #\7 #\8 #\9)
                                                             list)
                               ('quote col)
                               ('quote evisc)
                               ('quote print-base))
       (progn$
        ;;(cw "here1 ~p0 ~%" term)
        (fmt-to-comment-window
         str
         (acl2::pairlis2 acl2::*base-10-chars* (rp-rw-fix-cw-list list))
         col evisc print-base)))
      (('fmt-to-comment-window ('quote str) alist
                               ('quote col) ('quote evisc) ('quote print-base))
       (progn$
        ;;(cw "here2 ~p0 ~%" term)
        (fmt-to-comment-window
         str (rp-rw-fix-hard-error-alist alist) col evisc print-base)))
      (& nil))))

(local
 (in-theory (disable
             rp-ex-counterpart
             unquote-all
             w)))

(progn
  (defund-inline dont-rw-car (dont-rw)
    (declare (xargs :guard t))
    (if (consp dont-rw)
        (car dont-rw)
      (if dont-rw
          dont-rw
        nil)))

  (defund-inline dont-rw-cdr (dont-rw)
    (declare (xargs :guard t))
    (if (consp dont-rw)
        (cdr dont-rw)
      (if dont-rw
          dont-rw
        nil)))

  (mutual-recursion
   ;; for outside-in rules
   (defund match-lhs-for-dont-rw (lhs dont-rw acc-bindings)
     (declare (xargs :guard (alistp acc-bindings)
                     :verify-guards nil))
     (cond ((atom lhs)
            (cons (cons lhs dont-rw) acc-bindings))
           ((quotep lhs)
            acc-bindings)
           (t (match-lhs-for-dont-rw-lst (cdr lhs) (dont-rw-cdr dont-rw)
                                         acc-bindings))))
   (defund match-lhs-for-dont-rw-lst (lhs-lst dont-rw acc-bindings)
     (declare (xargs :guard (alistp acc-bindings)))
     (cond ((atom lhs-lst)
            acc-bindings)
           (t (let* ((acc-bindings (match-lhs-for-dont-rw (car lhs-lst)
                                                          (dont-rw-car dont-rw)
                                                          acc-bindings)))
                (match-lhs-for-dont-rw-lst (cdr lhs-lst)
                                           (dont-rw-cdr dont-rw)
                                           acc-bindings))))))

  (mutual-recursion
   (defun apply-bindings-for-dont-rw (term bindings )
     (declare (xargs  :mode :logic
                      :guard (and #|(rp-termp term)||#
                              (alistp bindings))))
     ;; apply the given bindings to the given term
     ;; That term can be anything but it is expected to be hyp or rhs of a rule.
     ;; Lambda expressions are not supported and it is enforced by rp-termp
     (cond ((acl2::variablep term)
            (b* ((binding (assoc-equal term bindings))
                 (res (if (consp binding)
                          (cdr binding)
                        (progn$ (cw "warning binding problem for dont-rw! ~p0 ~%" term)
                                term))))
              res))
           ((acl2::fquotep term) t)
           (t
            (cons nil
                  (apply-bindings-for-dont-rw-lst (cdr term) bindings)))))

   (defun apply-bindings-for-dont-rw-lst (lst bindings )
     (declare (xargs  :mode :logic
                      :guard (and (alistp bindings))))
     (if (atom lst)
         nil
       (cons (apply-bindings-for-dont-rw (car lst) bindings )
             (apply-bindings-for-dont-rw-lst (cdr lst) bindings )))))

  (defund-inline calculate-dont-rw (rule rhs/hyp dont-rw outside-in-flg)
    (declare (xargs :guard (and (weak-custom-rewrite-rule-p rule)
                                (not (rp-rule-metap rule)))
                    :verify-guards nil))
    (cond (outside-in-flg
           (b* (((when (not dont-rw))
                 dont-rw)
                (bindings (match-lhs-for-dont-rw (rp-lhs rule) dont-rw nil))
                (new-dont-rw (apply-bindings-for-dont-rw rhs/hyp bindings)))
             new-dont-rw))
          (t rhs/hyp))))

(mutual-recursion

 ;; The big, main 4 mutually recursive functions that calls the above functions
 ;; to perform rewriting.

 (defun rp-rw-rule (term dont-rw rules-for-term context iff-flg outside-in-flg  limit rp-state state)
   (declare (type (unsigned-byte 58) limit))
   (declare (ignorable dont-rw))
   (declare (xargs :measure (nfix limit)
                   :guard (and
                           (rp-termp term)
                           (rp-term-listp context)
                           (booleanp iff-flg)
                           (natp limit)
                           (VALID-RP-STATE-SYNTAXP RP-STATE)
                           (rule-list-syntaxp rules-for-term))
                   :stobjs (state
                            rp-state)
                   :verify-guards nil
                   :mode :logic))
   ;; returns (mv rule-rewritten-flg term dont-rw rp-state)
   (cond
    ((or (atom rules-for-term)
         (atom term)
         (acl2::fquotep term)
         (zp limit))
     (mv nil (rp-check-context term context iff-flg) dont-rw rp-state));))
    (t
     (b* (
          ((mv rule rules-for-term-rest var-bindings rp-context)
           (rp-rw-rule-aux term rules-for-term context iff-flg state))
          ((when (not rule)) ;; no rules found
           (mv nil (rp-check-context term context iff-flg) dont-rw rp-state))

          ((when (rp-rule-metap rule))
           (b* (((mv term-changed term dont-rw rp-state)
                 (rp-rw-meta-rule-main term rule dont-rw context rp-state state)))
             (if term-changed
                 (mv term-changed term dont-rw rp-state)
               (rp-rw-rule term dont-rw rules-for-term-rest context iff-flg outside-in-flg
                           (1- limit) rp-state state))))

          ((mv stack-index rp-state)
           (rp-state-push-to-try-to-rw-stack rule var-bindings
                                             rp-context rp-state))
          (synp-relieved
           (rp-rw-relieve-synp-wrap (rp-hyp rule)
                                    var-bindings ;no-rp-var-bindings
                                    state))
          ((when (not synp-relieved))
           (b* ((rp-state (rp-stat-add-to-rules-used rule 'failed-synp nil
                                                     rp-state))
                (rp-state (rp-state-push-to-result-to-rw-stack rule stack-index
                                                               'failed-synp nil nil rp-state)))
             (rp-rw-rule term dont-rw rules-for-term-rest context iff-flg
                         outside-in-flg  (1- limit) rp-state state)))
          (hyp (rp-apply-bindings (rp-hyp rule) var-bindings))

          ((mv hyp-rewritten rp-state)
           (rp-rw hyp
                  (calculate-dont-rw rule (rp-hyp rule) dont-rw outside-in-flg)
                  rp-context t t
                  (1- limit) rp-state state))

          (hyp-relieved (nonnil-p hyp-rewritten))
          ((when (not hyp-relieved))
           (b* ((rp-state (rp-stat-add-to-rules-used rule 'failed  nil rp-state))
                (rp-state (rp-state-push-to-result-to-rw-stack rule
                                                               stack-index 'failed nil nil
                                                               rp-state)))
             (rp-rw-rule
              term dont-rw rules-for-term-rest context iff-flg outside-in-flg
              (1- limit) rp-state state)))
          (term-res (rp-apply-bindings (rp-rhs rule) var-bindings))
          (rp-state (rp-stat-add-to-rules-used rule nil nil rp-state))
          (rp-state (rp-state-push-to-result-to-rw-stack rule stack-index
                                                         'success term
                                                         term-res rp-state))
          (dont-rw (calculate-dont-rw rule (rp-rhs rule) dont-rw outside-in-flg)))
       (mv t term-res dont-rw rp-state)))))

 (defun rp-rw-if (term dont-rw context iff-flg hyp-flg limit rp-state state)
   (declare (type (unsigned-byte 58) limit))
   (declare (xargs
             :measure (+ (nfix limit))
             :stobjs (state
                      rp-state)
             :guard (and
                     (rp-termp term)
                     (natp limit)
                     (valid-rp-state-syntaxp rp-state)
                     (rp-term-listp context)
                     (booleanp iff-flg)
                     )
             :verify-guards nil
             :mode :logic))
   ;; if a term is in the form
   ;; '(if a b c)
   ;; returns (mv term-changed t)
   (cond
    ((zp limit)
     (mv term rp-state))
    ((is-if term)
     (b* ((dont-rw (dont-rw-if-fix dont-rw)) ;;for guard
          ;; rewrite the condition first.
          ((mv cond-rw rp-state)
           (rp-rw (cadr term) (cadr dont-rw)
                  context t nil
                  (1- limit)
                  rp-state state))
          ;; if the cond is ''nil, then the 3rd subterm

          ((when (equal cond-rw ''nil))
           (rp-rw (cadddr term) (cadddr dont-rw)
                  context iff-flg hyp-flg
                  (1- limit) rp-state state))
          ;; if the cond is ''t then return the rewritten 2nd subterm
          ((when (nonnil-p cond-rw))
           (rp-rw (caddr term) (caddr dont-rw)
                  context iff-flg hyp-flg
                  (1- limit) rp-state state))
          ;; cond is something other than ''t or ''nil
          ;; if in hyp-flg=1 (meaning a hyp is being rewritten), then stop
          ;; trying to rewrite.
          ((when (and hyp-flg
                      ;; If this comes from a rule that resembles anything
                      ;; other than "and", then keep on rewriting.
                      (not (equal (cadr dont-rw)
                                  (caddr dont-rw)))
                      ;; if the context has an instance of "if", then stopping
                      ;; rewriting with the if-flg might prevent a rewrite.
                      (not (include-fnc-subterms context 'if))))
           (mv `(if ,cond-rw ,(caddr term) ,(cadddr term)) rp-state))

          ;; add to the
          ;; context to each subterm and simply them.
          (extra-context1 (rp-extract-context cond-rw))
          (?r1-context (append extra-context1 context))
          ((mv r1 rp-state)
           (rp-rw (caddr term) (caddr dont-rw)
                  r1-context iff-flg hyp-flg
                  (1- limit) rp-state state))
          (extra-context2
           (rp-extract-context (dumb-negate-lit2 cond-rw)))
          (r2-context (append extra-context2 context))
          ((mv r2 rp-state)
           (rp-rw (cadddr term) (cadddr dont-rw)
                  r2-context iff-flg hyp-flg
                  (1- limit) rp-state state))
          ;; if the two subterms are equal, return them
          ((when (equal r1 r2)) (mv r1 rp-state)))
       ;; could not simplify, return the rewritten term.
       (mv `(if ,cond-rw ,r1 ,r2) rp-state)))
    (t (mv term rp-state))))

 (defun rp-rw (term dont-rw context iff-flg hyp-flg limit rp-state state)
   (declare (type (unsigned-byte 58) limit))
   (declare (xargs :measure (+
                             (nfix limit))
                   :stobjs (state rp-state)
                   :verify-guards nil
                   :guard (and
                           (rp-termp term)
                           (natp limit)
                           (rp-term-listp context)
                           (booleanp iff-flg)
                           (valid-rp-state-syntaxp rp-state))
                   :mode :logic))
   ;; term: term to be rewritten.

   ;; dont-rw:  either nil or has the same cons structure as t.
   ;; when an element of it is t, then we do not try to rewrite that term.
   ;; That is set to t by a previously applied rule. When we apply a rule, we do
   ;; not need to dive into the variables that's just moved around.

   ;; limit is just a really big number to prove termination.

   ;; context is assumed conditions. Its format is not certain yet but it can
   ;; be a list of clauses e.g., ((booleanp a) (booleanp b) (equal (f a) (g
   ;; a)))

   ;; returns (mv term-changed term)
   (cond
    ((atom term)
     (mv
      (if (should-not-rw dont-rw) term (rp-check-context term context iff-flg))
      rp-state))
    ((eq (car term) 'quote)
     (mv term rp-state))
    ((zp limit)
     (progn$
      (rp-state-print-rules-used rp-state)
      (hard-error 'rp-rewriter "Step limit of ~x0 exhausted! Either run
(rp::set-rw-step-limit new-limit) or
(rp::update-rp-brr t rp::rp-state) to save the rewrite stack and see it with
(rp::pp-rw-stack :omit '()
                 :evisc-tuple (evisc-tuple 10 10 nil nil)
                 :frames 100). ~%"
                  (list (cons #\0 (rw-step-limit rp-state))))
      (mv term rp-state)))
    (t
     (b* (;; exit right away if said to not rewrite
          ((when (should-not-rw dont-rw))
           (mv term rp-state))
          ;; update the term to see if it simplifies with respect to the
          ;; context
          ((when (and iff-flg
                      (check-if-relieved-with-rp term)))
           (mv ''t rp-state))

          #|(term
          (rp-check-context term context iff-flg))||#

          ((mv rule-rewritten-flg term dont-rw rp-state)
           (rp-rw-rule term dont-rw
                       (rules-alist-outside-in-get (car term) rp-state)
                       context iff-flg t
                       (1- limit) rp-state state))

          ((when rule-rewritten-flg)
           (rp-rw term dont-rw context iff-flg hyp-flg (1- limit) rp-state state))

          ;; if simplified to a constant, then exit.
          ((when (or (atom term)
                     (eq (car term) 'quote)
                     (eq (car term) 'falist)))
           (mv term rp-state))
          ;; if the term is an "if" statement don't try to rewrite but branch.
          ((when (is-if term))
           (b* (((mv if-res rp-state)
                 (rp-rw-if term dont-rw context iff-flg hyp-flg
                                  (1-  limit) rp-state state)))
             (mv (rp-check-context if-res context iff-flg) rp-state)))
             

          ;; rewrite the subterm
          ((mv subterms rp-state)
           (if (is-hide term)
               (mv (cdr term) rp-state)
             (rp-rw-subterms (cdr term) (dont-rw-cdr dont-rw)
                             context hyp-flg (1- limit) rp-state state)))

          ;; put back the term together after subterm is rewritten
          (term (cons-with-hint (car term) subterms term))

          ;; check if it is a cw or hard-error statements.
          (- (rp-rw-check-hard-error-or-cw term rp-state))

          ;; if the subterm is only a list of quotep's, then run ex-counterpart
          ((mv term rp-state)
           (rp-ex-counterpart term rp-state state))
          ((when (or (atom term)
                     (eq (car term) 'quote)))
           (mv term rp-state))

          ((mv rule-rewritten-flg term dont-rw rp-state)
           (rp-rw-rule term dont-rw
                       (rules-alist-inside-out-get (car term) rp-state)
                       context iff-flg nil
                       (1- limit) rp-state state))
          ((when (not rule-rewritten-flg))
           (mv term rp-state)))
       (rp-rw term dont-rw context iff-flg hyp-flg (1- limit) rp-state state)))))

 (defun rp-rw-subterms (subterms dont-rw context hyp-flg limit rp-state state)
   ;; call the rewriter on subterms.
   (declare (type (unsigned-byte 58) limit))
   (declare (xargs :measure (nfix limit)
                   :stobjs (state rp-state)
                   :guard (and
                           (rp-term-listp subterms)
                           (rp-term-listp context)
                           (natp limit)
                           (valid-rp-state-syntaxp rp-state))
                   :verify-guards nil
                   :mode :logic))
   (cond
    ((or (atom subterms)
         (zp limit))
     (mv subterms rp-state))
    (t
     (b* (((mv car-subterms rp-state)
           (rp-rw (car subterms)
                  (dont-rw-car dont-rw)
                  context
                  nil
                  hyp-flg (1- limit)
                  rp-state
                  state))
          ((mv rest rp-state)
           (rp-rw-subterms (cdr subterms)
                           (dont-rw-cdr dont-rw)
                           context hyp-flg
                           (1- limit)
                           rp-state state)))
       (mv (cons-with-hint
            car-subterms
            rest
            subterms)
           rp-state))))))

(encapsulate
  nil
  (local
   (include-book "proofs/measure-lemmas"))
  (local
   (use-measure-lemmas t))
  (local
   (in-theory (enable is-if)))
  (mutual-recursion
   (defun attach-sc (term sc-type sc-term)
     (declare (xargs :guard t
                     :measure (cons-count term)))
     (cond
      ((atom term)
       (if (equal term sc-term)
           `(rp ',sc-type ,term)
         term))
      ((equal (car term) 'quote)
       term)
      ((equal term sc-term)
       `(rp ',sc-type ,term))
      ((is-if term) ;; only here for induction schemes
       `(if ,(attach-sc (cadr term) sc-type sc-term)
            ,(attach-sc (caddr term) sc-type sc-term)
          ,(attach-sc (cadddr term) sc-type sc-term)))
      (t (cons (car term)
               (attach-sc-lst (cdr term) sc-type sc-term)))))

   (defun attach-sc-lst (lst sc-type sc-term)
     (declare (xargs :guard t
                     :measure (cons-count lst)))
     (if (atom lst)
         lst
       (cons (attach-sc (car lst) sc-type sc-term)
             (attach-sc-lst (cdr lst) sc-type sc-term))))))

(define attach-sc-from-context (context term)
  :returns res-term

  (cond ((atom context)
         term)
        ((include-fnc term 'falist)
         term)
        (t (b* ((cur (car context)))
             (cond
              ((and (consp cur)
                    (consp (cdr cur))
                    (not (cddr cur))
                    ;;(atom (ex-from-rp (cadr cur)))  ;; only do it for vars
                    ;;(not (is-rp (cadr cur)))
                    (is-rp (list 'rp
                                 (list 'quote (car cur))
                                 (cadr cur))))
               (b* ((term (attach-sc term (car cur) (ex-from-rp (cadr cur)))))
                 (attach-sc-from-context (cdr context) term)))

              (t (attach-sc-from-context (cdr context) term)))))))

(defund attach-sc-from-context-lst (context terms)
  (declare (xargs :guard t))
  (if (atom terms)
      nil
    (cons-with-hint (attach-sc-from-context context (car terms))
                    (attach-sc-from-context-lst context (cdr terms))
                    terms)))

(defun preprocess-then-rp-rw (term rp-state state)
  ;; term can have lambda expressions.
  ;; rules-alist is expected to be a fast-alist
  ;; this is the function that is called by the clause processor.
  (declare (xargs :stobjs (state rp-state)
                  :guard (and
                          (rp-termp term)
                          (valid-rp-state-syntaxp rp-state))
                  :verify-guards nil))
  (b* ((step-limit (rw-step-limit rp-state))
       ((when (include-fnc term 'list))
        (progn$ (hard-error 'preprocess-then-rp-rw
                            "unexpected term is given to preprocess-then-rp-rw. The term contains a list instance: ~p0 ~%"
                            (list (cons #\0 term)))
                (mv term rp-state)))

       ((mv res- rp-state)
        (case-match
          term
          (('implies p q)
           (b* (((mv p rp-state)
                 (rp-rw p nil nil
                        t nil step-limit rp-state state))
                (context (rp-extract-context p))
                (q (attach-sc-from-context context q))
                (context (attach-sc-from-context-lst context context))

                (q (rp-rw-preprocessor q context rp-state state))
                ((mv q rp-state)
                 (rp-rw q nil context t nil step-limit rp-state state))
                (q (rp-rw-postprocessor q context rp-state state)))
             (mv (if (nonnil-p q)
                     q
                   `(implies ,p ,q))
                 rp-state)))
          (&
           (b* ((term (rp-rw-preprocessor term nil rp-state state))
                ((mv term rp-state)
                 (rp-rw term nil nil t nil step-limit rp-state state))
                (term
                 (rp-rw-postprocessor term nil rp-state state)))
             (mv term rp-state)))))

       (- (rp-state-print-rules-used rp-state))
       (- (if (not (nonnil-p res-))
              (b* ((action (not-simplified-action rp-state)))
                (cond ((equal action ':error)
                       (hard-error
                        'preprocess-then-rp-rw
                        "Error! rp-rewriter did not reduce the term to t! To supress this error run:
(set-not-simplified-action :warning) or (set-not-simplified-action :none)
Resulting  term is:~% ~p0 ~%"
                        (list (cons #\0 res-))))
                      ((equal action ':none)
                       nil)
                      (t
                       (cw "--- WARNING! --- Term was not reduced to 't. To throw an error instead, run:
(set-not-simplified-action :error) ~% ~%" ))))
            nil)))
    (mv (rp-trans res-) rp-state)))
