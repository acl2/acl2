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
         ;;((is-synp term) term)
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

  (memoize 'ex-from-rp-all2)

  (defconst *match-lhs-rp-equal-cnt*
    2)

  (mutual-recursion
   (defun rp-match-lhs (term rule-lhs context acc-bindings)
     (declare (xargs :measure (acl2::acl2-count rule-lhs)
                     :guard (and (alistp acc-bindings)
                                 (rp-termp term)
                                 (rp-termp rule-lhs)
                                 )
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
                          (rp-equal-cnt term other-entry
                                        *match-lhs-rp-equal-cnt*))))
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
             (b* ((term-w/o-rp
                   (cond ((is-if term-w/o-rp)
                          ;; if it is an "if" instance, remove the side
                          ;; conditions from the then and ele branches but not test.
                          (cons-with-hint
                           'if
                           (cons-with-hint
                            (cadr term-w/o-rp)
                            (cons-with-hint
                             (ex-from-rp-all2 (caddr term-w/o-rp))
                             (cons-with-hint (ex-from-rp-all2 (cadddr term-w/o-rp))
                                             nil
                                             (cdddr term-w/o-rp))
                             (cddr term-w/o-rp))
                            (cdr term-w/o-rp))
                           term-w/o-rp))
                         ((equal (car rule-lhs) 'if) ;; only to make the
                          ;; proofs easy
                          (ex-from-rp-all2 term-w/o-rp))
                         (t term-w/o-rp))))
               (rp-match-lhs-subterms (cdr term-w/o-rp) (cdr rule-lhs) context

                                      acc-bindings)))
            (t (mv context acc-bindings nil))))
          (t ;; rule is consp but term isn't. then we cannot match this rule to
           ;; the tem.
           (mv context acc-bindings nil))))))

   (defun rp-match-lhs-subterms (subterms sublhs context  acc-bindings)
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
             (rp-match-lhs (car subterms) (car sublhs) context  acc-bindings))
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

(define rp-check-context (term dont-rw context
                               &key
                               (iff-flg 'iff-flg)
                               (rw-context-flg 'nil))
  (declare (ignorable rw-context-flg)
           (xargs :mode :logic
                  :guard (and #|(context-syntaxp context)||#
                          (rp-termp term)
                          (rp-term-listp context)
                          (booleanp iff-flg)
                          (booleanp rw-context-flg))
                  :verify-guards nil))
  ;; Check if the term simplifies with given context.
  ;; Argument "context" is expected to have only clauses that define type or of the
  ;; form (equal x y)
  (if (atom context)
      (mv term dont-rw)
    (let* ((c (car context))
           ;;(rw-context-flg nil)
           )
      (cond ((and (case-match c ((& m) (rp-equal-cnt m term 1)) (& nil))
                  (not rw-context-flg))
             (b* ((new-term `(rp ',(car c) ,term))
                  ((mv new-term dont-rw)
                   (if (is-rp new-term)
                       (mv new-term `(nil t ,dont-rw))
                     (mv term dont-rw))))
               (rp-check-context new-term dont-rw (cdr context) :rw-context-flg rw-context-flg)))
            ((and (case-match c
                    (('equal m &) (rp-equal-cnt m term 1))
                    (('iff m &) (and iff-flg (rp-equal-cnt m term 1)))
                    (& nil))
                  (implies rw-context-flg
                           (<= (cons-count (caddr c)) (cons-count (cadr c)))))
             (mv (caddr c) t))
            ((and iff-flg (case-match c (('if m ''nil else)
                                         (and (nonnil-p else)
                                              (rp-equal-cnt m term 1)))))
             (mv ''nil t))
            ((and iff-flg (rp-equal-cnt c term 1))
             (mv ''t t))
            (t
             (rp-check-context term dont-rw (cdr context) :rw-context-flg rw-context-flg))))))

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
    (('dont-rw-context a)
     (rp-extract-context a))
    (('if a b ''nil)
     (append (rp-extract-context a)
             (rp-extract-context b)))
    ;; NOTE !!!!!!!!!!!!!!!!!!!!!!!!!!!!
    ;; here there could be another case for ('if a ''nil b) and extract context
    ;; for (negate a) and b. Will implement later...
    (('if a ''nil b)
     (cons
      (b* (((mv a &) (dumb-negate-lit2 a))
           (a (case-match a (('not a) `(if ,a 'nil 't)) (& a))))
        a)
      (rp-extract-context b)))
    (('if & & &)
     (progn$
      ;; do not print this warning in case of "not"
      (case-match term
        (('if & ''nil ''t) nil)
        (& (and nil (cw "WARNING! (if a b c) unsupported case-split may be required. ~%"))))
      (cons term nil)))
    (''t
     nil)
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
          (if (equal fn-name 'quotep)
              (magic-ev-fncall fn-name params state nil t)
            (magic-ev-fncall fn-name (unquote-all params) state nil t))))
      (if err
          (progn$ (hard-error 'rp-ev-fncall
                              "Magic-ev-fncall error for syntaxp check. val: ~p0 for term: ~p1 ~%"
                              (list (cons #\0 val)
                                    (cons #\1 (cons fn-name params))))
                  ''nil)
        (list 'quote val))))

  (mutual-recursion

   (defun rp-exc-all (term var-bindings rp-state state)
     (declare (xargs  :stobjs (state rp-state)
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
      ((acl2::fquotep term)
       (cond ((equal term '':rewriting-main-term)
              (list 'quote (backchaining-just-started rp-state)))
             ((equal term '':rewriting-hyp)
              (list 'quote
                    (and (not (backchaining-just-started rp-state))
                         (backchaining-rule rp-state)
                         )))
             (t term)))
      ((case-match term (('if & & &) t) (& nil))
       ;; if we don't ckeck the if statement and run everything:
       ;; 1. the performance could be bad.
       ;; 2. guards may fail for one of the branches
       (b* ((cond-rw (rp-exc-all (cadr term) var-bindings rp-state state))
            ((when (equal cond-rw ''nil))
             (rp-exc-all (cadddr term) var-bindings rp-state  state))
            ((when (nonnil-p cond-rw))
             (rp-exc-all (caddr term) var-bindings rp-state state)))
         (progn$ (cw "Error in executing an if statement: ~%~p0~%" term)
                 term)))
      (t
       (rp-ev-fncall (car term)
                     (rp-exc-all-subterms (cdr term) var-bindings rp-state state)
                     var-bindings
                     state))))

   (defun rp-exc-all-subterms (subterms var-bindings rp-state  state)
     (declare (xargs  :stobjs (state rp-state)
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
       (cons-with-hint (rp-exc-all (car subterms) var-bindings rp-state state)
                       (rp-exc-all-subterms (cdr subterms) var-bindings rp-state state)
                       subterms)))))
  #|(local
   (encapsulate
     nil

     (set-state-ok t)
     (make-flag rp-exc-all :defthm-macro-name defthm-rp-exc-all)

     (defthm-rp-exc-all
       (defthm pseudo-termp-rp-exc-all
         (implies (rp-termp term)
                  (rp-termp (rp-exc-all term var-bindings rp-state state)))
         :flag rp-exc-all)
       (defthm pseudo-termp-rp-exc-all-subterms
         (implies (rp-term-listp subterms)
                  (rp-term-listp (rp-exc-all-subterms subterms var-bindings rp-state state)))
         :flag rp-exc-all-subterms))))|#

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

   (defun rp-rw-relieve-synp (term bindings rp-state  state)
     (declare (xargs  :stobjs (state rp-state)
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
            (exc (rp-exc-all hyp bindings rp-state state))
            (res (nonnil-p exc)))
         res))
      (t (rp-rw-relieve-synp-subterms (cdr term) bindings rp-state  state))))

   (defun rp-rw-relieve-synp-subterms (subterms bindings rp-state state)
     (declare (xargs  :stobjs (state rp-state)
                      :guard (and #|(rp-term-listp subterms)||#
                              (alistp bindings)
                              )
                      :mode :logic))
     (if (atom subterms)
         t
       (and (rp-rw-relieve-synp (car subterms) bindings rp-state  state)
            (rp-rw-relieve-synp-subterms (cdr subterms) bindings rp-state
                                         state)))))

  (defund rp-rw-relieve-synp-wrap (term  bindings rp-state state)
    (declare (xargs  :stobjs (state rp-state)
                     :guard (and #|(rp-termp term)||#
                             (alistp bindings)
                             )
                     :verify-guards nil))
    (or
     (not (include-fnc term 'synp))
     (rp-rw-relieve-synp term
                         bindings rp-state
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
    ((rp-rw-meta-rule (term meta-fnc-name dont-rw context limit rp-state state)
                      (mv t t rp-state)
                      :guard (and (rp-termp term)
                                  (symbolp meta-fnc-name)
                                  (natp limit)
                                  (rp-term-listp context)
                                  (valid-rp-state-syntaxp rp-state))
                      :stobjs (state rp-state))
     (rp-rw-preprocessor (term context rp-state state)
                         t
                         :guard (and (rp-termp term)
                                     (valid-rp-state-syntaxp rp-state))
                         :stobjs (state rp-state))
     (rp-rw-postprocessor (term context rp-state state)
                          t
                          :guard (and (rp-termp term)
                                      (valid-rp-state-syntaxp rp-state))
                          :stobjs (state rp-state))
     (rp-formula-checks (state) t :stobjs (state)))
    (local
     (defun rp-rw-meta-rule (term meta-fnc-name dont-rw context limit rp-state state)
       (declare (ignorable term meta-fnc-name dont-rw context limit rp-state state)
                (xargs :guard (and (rp-termp term)
                                   (rp-term-listp context)
                                   (valid-rp-state-syntaxp rp-state)
                                   (symbolp meta-fnc-name)
                                   (natp limit)))
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
                    (eval-and-all context a)
                    (rp-evl-meta-extract-global-facts)
                    (rp-formula-checks state)
                    (rp-statep rp-state))
               (b* (((mv res-term ?dont-rw ?res-rp-state)
                     (rp-rw-meta-rule term meta-fnc-name dont-rw context limit rp-state state)))
                 (and (valid-sc res-term a)
                      (equal (rp-evlt res-term a)
                             (rp-evlt term a))))))

    (defthm rp-rw-meta-rule-rp-state-preservedp
      (implies (rp-statep rp-state)
               (b* (((mv ?res-term ?dont-rw res-rp-state)
                     (rp-rw-meta-rule term meta-fnc-name dont-rw context limit rp-state state)))
                 (rp-state-preservedp rp-state res-rp-state))))

    (defthm rp-rw-meta-rule-valid-rp-termp
      (implies (and (rp-termp term)
                    (rp-term-listp context)
                    (rp-statep rp-state))
               (b* (((mv res-term ?dont-rw ?rp-state)
                     (rp-rw-meta-rule term meta-fnc-name dont-rw context limit rp-state state)))
                 (rp-termp res-term))))

    (defthm rp-rw-preprocessor-valid-eval
      (implies (and (rp-termp term)
                    (rp-term-listp context)
                    (valid-sc term a)
                    (valid-sc-subterms context a)
                    (rp-evl-meta-extract-global-facts)
                    (rp-formula-checks state)
                    (eval-and-all context a)
                    (rp-statep rp-state))
               (b* ((res-term (rp-rw-preprocessor term context rp-state state)))
                 (and (valid-sc res-term a)
                      (iff (rp-evlt res-term a)
                           (rp-evlt term a))))))

    (defthm rp-rw-preprocessor-valid-rp-termp
      (implies (and (rp-termp term)
                    (rp-term-listp context)
                    (rp-statep rp-state))
               (b* ((res-term (rp-rw-preprocessor term context rp-state state)))
                 (rp-termp res-term))))

    (defthm rp-rw-postprocessor-valid-eval
      (implies (and (rp-termp term)
                    (rp-term-listp context)
                    (valid-sc term a)
                    (valid-sc-subterms context a)
                    (eval-and-all context a)
                    (rp-evl-meta-extract-global-facts)
                    (rp-formula-checks state)
                    (rp-statep rp-state))
               (b* ((res-term
                     (rp-rw-postprocessor term context rp-state state)))
                 (and (valid-sc res-term a)
                      (iff (rp-evlt res-term a)
                           (rp-evlt term a))))))

    (defthm rp-rw-postprocessor-valid-rp-termp
      (implies (and (rp-termp term)
                    (rp-term-listp context)
                    (rp-statep rp-state))
               (b* ((res-term
                     (rp-rw-postprocessor term context rp-state state)))
                 (rp-termp res-term)))))

  (defund rp-rw-meta-rule-main (term rule dont-rw context limit rp-state state)
    (declare (xargs  :stobjs (rp-state state)
                     :verify-guards nil
                     :guard (and (rp-termp term)
                                 (natp limit)
                                 (rule-syntaxp rule)
                                 (rp-rule-metap rule)
                                 (rp-term-listp context)
                                 (valid-rp-state-syntaxp rp-state))))
    (b* (((mv res-term dont-rw rp-state)
          (rp-rw-meta-rule term (rp-rule-meta-fnc rule) dont-rw context
                           limit
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

  (defun rp-rw-fix-cw-list (list context)
    (declare (xargs :guard t))
    (case-match list
      (('cons a rest)
       (cons (if (and (symbolp a) (equal (symbol-name a) "@CONTEXT")) context a)
             (rp-rw-fix-cw-list rest context)))
      (''nil
       nil)
      (& nil)))

  (local
   (defthm true-listp-rp-rw-fix-cw-list
     (true-listp (rp-rw-fix-cw-list list context))))

  (defun rp-rw-check-hard-error-or-cw (term context rp-state)
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
      (('fmt-to-comment-window ('quote str) ('acl2::pairlis2 &
                                                             list)
                               ('quote col)
                               ('quote evisc)
                               ('quote print-base))
       (progn$
        ;;(cw "here1 ~p0 ~%" term)
        (fmt-to-comment-window
         str
         (acl2::pairlis2 acl2::*base-10-chars* (rp-rw-fix-cw-list list context))
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
          (t rhs/hyp)))

  (defund-inline calculate-dont-rw-lst (rule rhs/hyp-lst dont-rw outside-in-flg)
    (declare (xargs :guard (and (weak-custom-rewrite-rule-p rule)
                                (not (rp-rule-metap rule)))
                    :verify-guards nil))
    (cond (outside-in-flg
           (b* (((when (not dont-rw))
                 dont-rw)
                (bindings (match-lhs-for-dont-rw (rp-lhs rule) dont-rw nil))
                (new-dont-rw (apply-bindings-for-dont-rw-lst rhs/hyp-lst bindings)))
             new-dont-rw))
          (t rhs/hyp-lst))))

(define limit-reached-action (rp-state)
  :stobjs (rp-state)
  :Returns (res-rp-state)
  (b* ((backchaining-rule (backchaining-rule rp-state))

       (rp-state (if (weak-custom-rewrite-rule-P backchaining-rule)
                     (rp-state-push-to-result-to-rw-stack backchaining-rule -1
                                                          :backchain-limit-reached
                                                          nil nil rp-state)
                   rp-state))
       (rw-limit-throws-error (rw-limit-throws-error rp-state))
       ((unless rw-limit-throws-error) rp-state)
       (- (rp-state-print-rules-used rp-state))
       (-
        (if backchaining-rule
            (hard-error 'rp-rewriter "Backchain limit of ~x0 exhausted when ~
relieving the hypothesis for ~x1! You can disable this error by running:
(rp::set-rp-backchain-limit-throws-error nil). You can change the backchain-limit:
(rp::set-rp-backchain-limit new-limit). Or you can run:
(rp::update-rp-brr t rp::rp-state) to save the rewrite stack and see it with
(rp::pp-rw-stack :omit '()
                 :evisc-tuple (evisc-tuple 10 10 nil nil)
                 :frames 100). ~%"
                        (list (cons #\0 (rw-backchain-limit rp-state))
                              (cons #\1
                                    (if (weak-custom-rewrite-rule-P backchaining-rule)
                                        (rp-rune backchaining-rule)
                                      backchaining-rule))))
          (hard-error 'rp-rewriter "Step limit of ~x0 exhausted! Either run
(rp::set-rw-step-limit new-limit) or
(rp::update-rp-brr t rp::rp-state) to save the rewrite stack and see it with
(rp::pp-rw-stack :omit '()
                 :evisc-tuple (evisc-tuple 10 10 nil nil)
                 :frames 100). ~%"
                      (list (cons #\0 (rw-step-limit rp-state)))))))
    rp-state))

(define get-limit-for-hyp-rw ((limit natp)
                              rule
                              rp-state)
  :stobjs (rp-state)
  :returns (mv (res-limit)
               (backchain-starts booleanp :hyp (rp-statep rp-state))
               (old-limit-error-setting booleanp :hyp (rp-statep rp-state))
               (res-rp-state rp-statep :hyp (rp-statep rp-state)))
  :prepwork ((local
              (in-theory (e/d (rp-statep) ()))))
  (b* ((backchain-limit (rw-backchain-limit rp-state))
       (backchain-limit (mbe :exec backchain-limit :logic (nfix backchain-limit)))
       (existing-backchaining-rule (backchaining-rule rp-state))
       (rp-state (update-backchaining-just-started nil rp-state))
       (limit (1- limit))
       ((when (or (> backchain-limit limit)
                  existing-backchaining-rule))
        (progn$
         (mv limit nil nil rp-state)))
       (old-limit-error-setting (rw-limit-throws-error rp-state))
       (rp-state (update-rw-limit-throws-error (rw-backchain-limit-throws-error rp-state) rp-state))
       (rp-state (update-backchaining-rule rule rp-state))
       (rp-state (update-backchaining-just-started t rp-state)))
    (mv backchain-limit t old-limit-error-setting rp-state))
  ///

  (defret smaller-limit-of-<fn>
    (implies (not (zp limit))
             (and (natp res-limit)
                  (< res-limit limit)))))

(define post-backchain-ops (backchain-ends
                            (old-limit-error-setting booleanp)
                            rp-state)
  :stobjs (rp-state)
  :returns (res-rp-state)
  (b* ((rp-state (update-backchaining-just-started nil rp-state))
       ((unless backchain-ends) rp-state)
       (rp-state (update-backchaining-rule nil rp-state))
       (rp-state (update-rw-limit-throws-error old-limit-error-setting
                                               rp-state)))
    rp-state))

(define create-if-instance (test r1 r2 &key negated-test)
  :inline t
  :verify-guards nil
  (cond ((equal test ''nil)
         r2)
        ((nonnil-p test)
         r1)
        ((equal negated-test ''nil)
         r1)
        ((nonnil-p negated-test)
         r2)
        ((rp-equal-cnt r1 r2 2)
         (ex-from-rp-all2 r1))
        (t `(if ,test ,r1 ,r2))))

(progn
  (defthm min-of-limit
    (implies (and (natp other)
                  (not (zp limit)))
             (and (< (min other (1- limit))
                     limit)
                  (< (min (1- limit) other)
                     limit)

                  (natp (min other (1- limit)))
                  (natp (min (1- limit) other))))
    :hints (("Goal"
             :in-theory (e/d (min) ()))))
  (local
   ;; disable for quick measure
   (in-theory (disable min
                       DUMB-NEGATE-LIT2$INLINE
                       NONNIL-P
                       RP-EQUAL-CNT
                       RP-EXTRACT-CONTEXT
                       quotep))))

(define rp-rw-dont-rw-or (cond y)
  (or (if cond t nil)  y))

(defconst *and-pattern-flip-cons-count-limit*
  100)

(mutual-recursion
 (defun rw-only-with-context (term dont-rw context iff-flg limit rp-state
                                   state)
   (declare (type (unsigned-byte 58) limit))
   (declare (ignorable dont-rw))
   (declare (xargs :measure (acl2::nat-list-measure (list limit 0))
                   :guard (and
                           (rp-termp term)
                           (rp-term-listp context)
                           (booleanp iff-flg)
                           (natp limit)
                           ;;(valid-rp-state-syntaxp RP-STATE)
                           ;;(rule-list-syntaxp rules-for-term)
                           )
                   :stobjs (state rp-state)
                   :verify-guards nil
                   :mode :logic))
   (b* (((when (quotep term)) (mv term rp-state))
        ((when (or (zp limit) (atom term) (equal (car term) 'list)))
         (mv (if (should-not-rw dont-rw)
                 term
               (b* (((mv new-term &)
                     (rp-check-context term dont-rw context :rw-context-flg nil)))
                 new-term))
             rp-state))
        ((mv term dont-rw)
         (rp-check-context term dont-rw context :rw-context-flg nil))

        ((when (or (atom term)
                   (should-not-rw dont-rw)
                   (equal (car term) 'quote)
                   (equal (car term) 'falist)))
         (mv term rp-state))

        ((when (is-rp$ term)) ;; to make the proofs go easily
         (b* (((mv subterm rp-state)
               (rw-only-with-context (caddr term)
                                     (dont-rw-car
                                      (dont-rw-cdr
                                       (dont-rw-cdr dont-rw)))
                                     context nil (1- limit)
                                     rp-state state)))
           (mv (cons-with-hint (car term)
                               (cons-with-hint (cadr term)
                                               (cons-with-hint subterm nil (cddr
                                                                            term))
                                               (cdr term))
                               term)
               rp-state)))

        ((when (is-if term))
         (rw-only-with-context-if term dont-rw context iff-flg (1- limit)
                                  rp-state state))
        ((mv subterms rp-state)
         (rw-only-with-context-subterms (cdr term)
                                        (dont-rw-cdr dont-rw)
                                        context
                                        (1- limit)
                                        rp-state state))
        (term (cons-with-hint (car term) subterms term))
        ((mv term &)
         (rp-check-context term t context :rw-context-flg nil))
        ((mv term rp-state)
         (rp-ex-counterpart term rp-state state)))
     (mv term rp-state)))

 (defun rw-only-with-context-if (term dont-rw context iff-flg limit rp-state
                                      state)
   (declare (type (unsigned-byte 58) limit))
   (declare (ignorable dont-rw))
   (declare (xargs :measure (acl2::nat-list-measure (list limit 0))
                   :guard (and
                           (is-if term)
                           (rp-termp term)
                           (rp-term-listp context)
                           (booleanp iff-flg)
                           (natp limit)
                           ;;(valid-rp-state-syntaxp RP-STATE)
                           ;;(rule-list-syntaxp rules-for-term)
                           )
                   :stobjs (state rp-state)
                   :verify-guards nil
                   :mode :logic))
   (b* (((when (zp limit)) (mv term rp-state))
        ((mv cond then else)
         (mv (cadr term) (caddr term) (cadddr term)))
        ((mv cond-dont-rw then-dont-rw else-dont-rw)
         (mv (dont-rw-car (dont-rw-cdr dont-rw))
             (dont-rw-car (dont-rw-cdr (dont-rw-cdr dont-rw)))
             (dont-rw-car (dont-rw-cdr (dont-rw-cdr (dont-rw-cdr dont-rw))))))
        ((mv cond rp-state)
         (rw-only-with-context cond cond-dont-rw context t (1- limit)
                               rp-state state))
        ((when (nonnil-p cond))
         (rw-only-with-context then then-dont-rw context iff-flg (1- limit)
                               rp-state state))
        ((when (equal cond ''nil))
         (rw-only-with-context else else-dont-rw context iff-flg (1- limit)
                               rp-state state))
        ((mv then rp-state)
         (rw-only-with-context then then-dont-rw context iff-flg (1- limit)
                               rp-state state))
        ((mv else rp-state)
         (rw-only-with-context else else-dont-rw context iff-flg (1- limit)
                               rp-state state))
        ((when (equal then else))
         (mv then rp-state))
        ((when (and*e iff-flg (nonnil-p then) (nonnil-p else)))
         (mv ''t rp-state)))
     (mv (create-if-instance cond then else) rp-state)))

 (defun rw-only-with-context-subterms (lst dont-rw context limit rp-state state)
   (declare (type (unsigned-byte 58) limit))
   (declare (ignorable dont-rw))
   (declare (xargs :measure (acl2::nat-list-measure (list limit (acl2-count lst)))
                   :guard (and
                           (rp-term-listp lst)
                           (rp-term-listp context)
                           (natp limit))
                   :stobjs (state rp-state)
                   :verify-guards nil
                   :mode :logic))
   (if (atom lst)
       (mv lst rp-state)
     (b* (((mv cur rp-state)
           (rw-only-with-context (car lst) (dont-rw-car dont-rw) context
                                 nil limit rp-state state))
          ((mv rest rp-state)
           (rw-only-with-context-subterms (cdr lst) (dont-rw-cdr dont-rw) context
                                          limit rp-state state)))
       (mv (cons-with-hint cur rest lst) rp-state)))))

(defun clear-context-for-rw-only-with-context (context)
  (declare (xargs :guard t))
  (if (atom context)
      nil
    (If (include-fnc (car context) 'if)
        (clear-context-for-rw-only-with-context (cdr context))
        (cons-with-hint (car context)
                        (clear-context-for-rw-only-with-context (cdr context))
                        context))))

(defun rw-only-with-context-lst$iff-flg=t (lst dont-rw context limit rp-state
                                               state)
  (declare (type (unsigned-byte 58) limit))
  (declare (xargs :measure (acl2-count lst)
                  :guard (and
                          (rp-term-listp lst)
                          (rp-term-listp context)
                          (natp limit))
                  :stobjs (state rp-state)
                  :verify-guards nil
                  :mode :logic))
  (if (atom lst)
      (mv lst rp-state)
    (b* (((mv cur rp-state)
          (rw-only-with-context (car lst) (dont-rw-car dont-rw) context
                                t limit rp-state state))
         ((when (equal cur ''nil))
          (mv (list cur) rp-state))
         ((mv rest rp-state)
          (rw-only-with-context-lst$iff-flg=t (cdr lst) (dont-rw-cdr dont-rw) context
                                              limit rp-state state)))
      (mv (if (nonnil-p cur) rest (cons-with-hint cur rest lst)) rp-state))))

(defund rp-remove-equal (x l)
  (declare (xargs :guard t))
  (if (atom l)
      nil
    (if (rp-equal-cnt x (car l) 2)
        (rp-remove-equal x (cdr l))
      (cons-with-hint (car l)
                      (rp-remove-equal x (cdr l))
                      l))))

(defund end-of-if-p (term)
  (declare (xargs :guard t))
  (case-match term
    (('if & then else)
     (and (quotep then)
          (quotep else)
          (implies (equal then ''nil)
                   (not (equal else ''t)))))
    (& t)))

(progn
  (define calc-dw-negated-cond-rw (cond-rw-is-a-constant then else
                                                         negated-cond-rw-dont-rw)
    
    :inline t
    (rp-rw-dont-rw-or
     (or** cond-rw-is-a-constant
           (and** (or** (equal then ''nil)
                        (nonnil-p then))
                  (or** (equal else ''nil)
                        (nonnil-p else))))
     negated-cond-rw-dont-rw))

  (define calc-conds-for-rp-rw-if-1 (&optional
                                     (negated-cond-rw-is-a-constant
                                      'negated-cond-rw-is-a-constant)
                                     (cond-rw-is-a-constant 'cond-rw-is-a-constant)
                                     
                                     (rp-state 'rp-state)
                                     
                                     
                                     (then 'then)
                                     (dont-rw 'dont-rw)
                                     (else 'else))
    :guard (and (consp dont-rw)
                (consp (cdr dont-rw))
                (consp (cddr dont-rw))
                (consp (cdddr dont-rw)))
    
    :inline t
    (mv (if** (or** negated-cond-rw-is-a-constant
                    cond-rw-is-a-constant
                    
                    (backchaining-rule rp-state)
                    (rw-context-disabled rp-state)
                    (cons-count-compare then 2000))
              (second (cdr dont-rw))
              nil)
        (if** (or** negated-cond-rw-is-a-constant
                    cond-rw-is-a-constant
                    
                    (backchaining-rule rp-state)
                    (rw-context-disabled rp-state)
                    (cons-count-compare else 2000))
              (third (cdr dont-rw))
              nil))))

(mutual-recursion

 ;; The main mutually recursive functions
 ;; to perform rewriting.

 (defun rp-rw-rule (term dont-rw rules-for-term context iff-flg outside-in-flg  limit rp-state state)
   (declare (type (unsigned-byte 58) limit))
   (declare (ignorable dont-rw))
   (declare (xargs :measure (acl2::nat-list-measure (list limit 0))
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
         (acl2::fquotep term))
     (b* (((mv new-term dont-rw) (rp-check-context term dont-rw context
                                                   :rw-context-flg (rw-context-disabled rp-state)))
          ;;(dont-rw (if (not (equal new-term term)) t dont-rw))
          )
       (mv nil new-term dont-rw rp-state))) ;))
    ((zp limit)
     (b* ((rp-state (limit-reached-action rp-state)))
       (mv nil term dont-rw rp-state)))
    (t
     (b* (((mv rule rules-for-term-rest var-bindings rp-context)
           (rp-rw-rule-aux term rules-for-term context iff-flg state))
          ((when (not rule)) ;; no rules found
           (b* (((mv new-term dont-rw) (rp-check-context term dont-rw context
                                                         :rw-context-flg (rw-context-disabled rp-state)))
                ;;(dont-rw (if (not (equal new-term term)) t dont-rw))
                )
             (mv nil new-term dont-rw rp-state)))

          ((when (rp-rule-metap rule))
           (b* (((mv term-changed term dont-rw rp-state)
                 (rp-rw-meta-rule-main term rule dont-rw context limit rp-state state)))
             (if term-changed
                 (mv term-changed term dont-rw rp-state)
               (rp-rw-rule term dont-rw rules-for-term-rest context iff-flg outside-in-flg
                           (1- limit) rp-state state))))

          ((mv stack-index rp-state)
           (rp-state-push-to-try-to-rw-stack rule var-bindings
                                             rp-context rp-state))

          (hyp (rp-apply-bindings-subterms (rp-hyp rule) var-bindings))

          ((mv hyp-limit backchain-starts old-limit-error-setting rp-state)
           (get-limit-for-hyp-rw limit rule rp-state))

          ((mv hyp-relieved rp-state)
           (rp-rw-relieve-hyp hyp
                              (calculate-dont-rw-lst rule (rp-hyp rule) dont-rw outside-in-flg)
                              rp-context rule stack-index var-bindings hyp-limit
                              rp-state state))

          (rp-state (post-backchain-ops backchain-starts old-limit-error-setting rp-state))

          ((when (not hyp-relieved))
           (rp-rw-rule
            term dont-rw rules-for-term-rest context iff-flg outside-in-flg
            (1- limit) rp-state state))
          (term-res (rp-apply-bindings (rp-rhs rule) var-bindings))
          (rp-state (rp-stat-add-to-rules-used rule nil nil rp-state))
          (rp-state (rp-state-push-to-result-to-rw-stack rule stack-index
                                                         :success term
                                                         term-res rp-state))
          (dont-rw (calculate-dont-rw rule (rp-rhs rule) dont-rw outside-in-flg)))
       (mv t term-res dont-rw rp-state)))))

 (defun rp-rw-relieve-hyp (term-lst dont-rw context rule stack-index var-bindings limit rp-state state)
   (declare (type (unsigned-byte 58) limit))
   (declare (xargs
             :measure (acl2::nat-list-measure (list limit (acl2-count term-lst)))
             :stobjs (state rp-state)
             :guard (and
                     (rp-term-listp term-lst)
                     (natp limit)
                     (valid-rp-state-syntaxp rp-state)
                     (rp-term-listp context)
                     (integerp stack-index)
                     (weak-custom-rewrite-rule-p rule)
                     (alistp var-bindings))
             :verify-guards nil
             :mode :logic))
   (b* (((when (zp limit))
         (mv nil rp-state))
        ((when (atom term-lst))
         (mv t rp-state))
        (term (car term-lst))
        (synp-relieved (or (not (and (consp term) (equal (car term) 'synp)))
                           (rp-rw-relieve-synp-wrap term var-bindings rp-state state)))
        ((unless synp-relieved)
         (b* ((rp-state (rp-stat-add-to-rules-used rule :failed-synp nil rp-state))
              (rp-state (rp-state-push-to-result-to-rw-stack rule stack-index
                                                             :failed-synp nil nil rp-state)))
           (mv nil rp-state)))
        ((mv eval1 rp-state)
         (rp-rw term (dont-rw-car dont-rw) context t (1- limit) rp-state
                state))
        ((unless (nonnil-p eval1))
         (b* ((rp-state (rp-stat-add-to-rules-used rule :failed  nil rp-state))
              (rp-state (rp-state-push-to-result-to-rw-stack rule
                                                             stack-index :failed nil nil
                                                             rp-state)))
           (mv nil rp-state))))
     (rp-rw-relieve-hyp (cdr term-lst) (dont-rw-cdr dont-rw)
                        context rule stack-index var-bindings limit rp-state state)))

 (defun rp-rw-if (term dont-rw context iff-flg limit rp-state state)
   (declare (type (unsigned-byte 58) limit))
   (declare (xargs
             :measure (acl2::nat-list-measure (list limit 1))
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
     (b* ((?current-rw-limit-throws-error (rw-limit-throws-error rp-state))
          (?current-rw-context-disabled (rw-context-disabled rp-state))

          (dont-rw (dont-rw-if-fix dont-rw)) ;;for guard
          ;; rewrite the condition first.

          ((mv cond then else)
           (mv (first (cdr term)) (second (cdr term)) (third (cdr term))))
          (cond-dont-rw (first (cdr dont-rw)))

          ;; simplify it for "or" pattern.
          ;;(then (if (and iff-flg (rp-equal-cnt then cond 2)) ''t then))
          
          ((mv cond-rw rp-state)
           (rp-rw cond cond-dont-rw
                  context t 
                  (1- limit)
                  rp-state state))
          

          #|((when (and* (is-if cond-rw)
                      (equal (third (cdr cond-rw)) ''nil)
                      (equal else ''nil)
                      #|(not (cw "and of and pattern: triggered by: ~p0 ~%"
                               term))|#
                      #|(not (cw "result ~p0 ~%" `(if ,(cadr cond-rw) (if ,(caddr cond-rw) ,then 'nil) 'nil)))|#))
           (rp-rw `(if ,(cadr cond-rw) (if ,(caddr cond-rw) ,then 'nil) 'nil)
                  `(nil t (nil t ,(second (cdr dont-rw)) t) t)
                  context iff-flg hyp-flg
                  (1- limit) rp-state state))|#
          
          ;; if the cond is ''nil, then the 3rd subterm

          ;; ((when (equal cond-rw ''nil))
          ;;  (rp-rw else else-dont-rw
          ;;         context iff-flg hyp-flg
          ;;         (1- limit) rp-state state))
          ;; ;; if the cond is ''t then return the rewritten 2nd subterm
          ;; ((when (nonnil-p cond-rw))
          ;;  (rp-rw then then-dont-rw
          ;;         context iff-flg hyp-flg
          ;;         (1- limit) rp-state state))

          ((mv negated-cond-rw negated-cond-rw-dont-rw)
           (dumb-negate-lit2 cond-rw))

          (cond-rw-is-a-constant (or** (nonnil-p cond-rw)
                                       (equal cond-rw ''nil)))

          ((mv negated-cond-rw rp-state)
           (rp-rw negated-cond-rw
                  (calc-dw-negated-cond-rw cond-rw-is-a-constant
                                           then else negated-cond-rw-dont-rw)
                  #|(rp-rw-dont-rw-or 
                                    (or** cond-rw-is-a-constant
                                          (and** (or** (equal then ''nil)
                                                       (nonnil-p then))
                                                 (or** (equal else ''nil)
                                                       (nonnil-p else))))
                                    negated-cond-rw-dont-rw)|#
                  context t  (1- limit)
                  rp-state state))

          (negated-cond-rw-is-a-constant (or** (nonnil-p negated-cond-rw)
                                               (equal negated-cond-rw ''nil)))

          ((mv cond-rw &)
           (if (and** negated-cond-rw-is-a-constant
                      (not** cond-rw-is-a-constant))
               (dumb-negate-lit2 negated-cond-rw)
             (mv cond-rw nil)))


          ((mv then-dont-rw else-dont-rw)
           (calc-conds-for-rp-rw-if-1)
           #|(mv (if** (or** negated-cond-rw-is-a-constant
                           cond-rw-is-a-constant
                           hyp-flg
                           (backchaining-rule rp-state)
                           (rw-context-disabled rp-state)
                           (cons-count-compare then 2000))
                     (second (cdr dont-rw))
                     nil)
               (if** (or** negated-cond-rw-is-a-constant
                           cond-rw-is-a-constant
                           hyp-flg
                           (backchaining-rule rp-state)
                           (rw-context-disabled rp-state)
                           (cons-count-compare else 2000))
                     (third (cdr dont-rw))
                     nil))|#)

          #|((when (and** hyp-flg
                        (not** cond-rw-is-a-constant)
                        (not** negated-cond-rw-is-a-constant)
                        (or** (equal then ''nil)
                              (equal else ''nil))))
           ;; hyp-flg means stop rewriting if you are sure that the term won't
           ;; become ''t.
           ;; When  simplifying   a  hypothesis,  cond  did   not  simplify  to
           ;; nil/nonnil. Same for negated-cond. We now  rely on r1 and r2 both
           ;; being  rewritten to  a nonnil.  If r2  is already  nil, or  if r1
           ;; doesn't simplify  to a nonnil or  simplifies to a nil,  then just
           ;; return the term
           (mv term rp-state))|#

          
          
          ((mv r1 r1-context-has-nil rp-state)
           (rp-rw-if-branch cond-rw then then-dont-rw context
                            iff-flg  limit rp-state state)
           #|(b* (((mv r1-context rp-state)
                 (rp-rw-context-main cond-rw context
                                     ;;r1-rp-rw-context-main-enabled
                                     (and** (not* (equal cond-rw ''nil))
                                            ;;(not* (is-dont-rw-context cond))
                                            (end-of-if-p then)
                                            (not* (nonnil-p then))
                                            ;;(not* (equal else ''nil)) ;; if
                                            ;; rewriting an 'and' pattern, then
                                            ;; don't try to rewrite the context
                                            (not* (equal then ''nil))

                                            ;;(not* (rw-context-disabled rp-state))
                                            ;;(not* (backchaining-rule rp-state))
                                            )
                                     ;;r1-rp-rw-context-main-quick-enabled
                                     (and** (not* (equal cond-rw ''nil))
                                            ;;(not* (is-dont-rw-context cond))
                                            (not* (nonnil-p then))
                                            ;;(not* (equal else ''nil)) ;; if
                                            ;; rewriting an 'and' pattern, then
                                            ;; don't try to rewrite the context
                                            (not* (equal then ''nil)))
                                     (1- limit) rp-state state))
                (r1-context-has-nil (member-equal ''nil r1-context))
                
                ((mv r1 rp-state)
                 (rp-rw then
                        (rp-rw-dont-rw-or (or** (equal cond-rw ''nil)
                                                r1-context-has-nil)
                                          then-dont-rw)
                        r1-context iff-flg hyp-flg
                        (1- limit) rp-state state)))
             (mv r1 r1-context-has-nil rp-state))|#)

          #|((when (and** hyp-flg
                        (not** negated-cond-rw-is-a-constant)
                        (not** cond-rw-is-a-constant)
                        (or** (equal r1 ''nil)
                              (equal else ''nil)
                              (not* (nonnil-p r1)))))
           ;; When  simplifying   a  hypothesis,  cond  did   not  simplify  to
           ;; nil/nonnil. We  now rely on r1  and r2 both being  rewritten to a
           ;; nonnil. If  r2 is  already nil,  or if r1  doesn't simplify  to a
           ;; nonnil or simplifies to a nil, then just return the term
           (mv term rp-state))|#

          ((mv r2 r2-context-has-nil rp-state)
           (rp-rw-if-branch negated-cond-rw else else-dont-rw context
                            iff-flg  limit rp-state state)
           #|(b* (((mv r2-context rp-state)
                 (rp-rw-context-main negated-cond-rw context
                                     (and** (not* (nonnil-p cond-rw))
                                            ;;(not* (is-dont-rw-context cond))
                                            (end-of-if-p else)
                                            (not* (nonnil-p else))
                                            (not* (equal else ''nil)))
                                     (and** (not* (nonnil-p cond-rw))
                                            ;;(not* (is-dont-rw-context cond))
                                            (not* (nonnil-p else))
                                            (not* (equal else ''nil)))
                                     (1- limit) rp-state state))
                (r2-context-has-nil (member-equal ''nil r2-context))
                ((mv r2 rp-state)
                 (rp-rw else
                        ;; to minimize casesplit, use a dont-rw trick:
                        (rp-rw-dont-rw-or (or** (nonnil-p cond-rw)
                                                r2-context-has-nil)
                                          else-dont-rw)
                        r2-context iff-flg hyp-flg
                        (1- limit) rp-state state)))
             (mv r2 r2-context-has-nil rp-state))|#)

          ;; if the  two subterms  are equal, return  them cannot  use rp-equal
          ;; because  they may  have  different side-conditions,  which is  not
          ;; allowed.  their rp-equal case  is handled in create-if-instance by
          ;; removing all side-conditions
          ((when (equal r1 r2))
           (mv r1 rp-state))
          
          ((when r1-context-has-nil)
           (mv r2 rp-state))
          ((when r2-context-has-nil)
           (mv r1 rp-state))

          ((unless iff-flg)
           (mv (create-if-instance cond-rw r1 r2 :negated-test negated-cond-rw) rp-state))

          ;; only do things with iff-flg from here and on.
          ((when (and*e (nonnil-p r1) (equal r2 ''nil)))
           (mv cond-rw rp-state))
          ((when (and*e (nonnil-p r2) (equal r1 ''nil)))
           (mv negated-cond-rw rp-state))
          ((when (and*e  (nonnil-p r2) (nonnil-p r1)))
           (mv ''t rp-state))

          ((when (and*e ;;iff-flg
                  (equal r2 ''nil)
                  (and** (not** cond-rw-is-a-constant)
                         (not** (cons-count-compare cond-rw (* 3 *and-pattern-flip-cons-count-limit*)))
                         (not** (cons-count-compare r1 (* 3 *and-pattern-flip-cons-count-limit*))))))
           (rp-rw-and cond-rw r1 context  (1- limit) rp-state state))

          ((when (and*e ;;iff-flg
                  (equal r1 ''nil)
                  (and** (not** negated-cond-rw-is-a-constant)
                         (not** (cons-count-compare cond-rw (* 3 *and-pattern-flip-cons-count-limit*)))
                         (not** (cons-count-compare r2 (* 3 *and-pattern-flip-cons-count-limit*)))))) ; ;
           (rp-rw-and negated-cond-rw r2 context  (1- limit) rp-state state)))

       ;; could not simplify, return the rewritten term.
       (mv (create-if-instance cond-rw r1 r2 :negated-test negated-cond-rw) rp-state)))
    (t (mv term rp-state))))


 (defun rp-rw-if-branch (cond-rw then then-dont-rw
                                 context
                                 iff-flg  limit rp-state state)
   (declare (type (unsigned-byte 58) limit))
   
   (declare (xargs :measure (acl2::nat-list-measure (list limit
                                                          0))
                   :stobjs (state rp-state)
                   :verify-guards nil
                   :guard (and
                           (rp-termp cond-rw)
                           (rp-termp then)
                           (booleanp iff-flg)
                           (rp-term-listp context)
                           (natp limit)
                           (valid-rp-state-syntaxp rp-state))
                   :mode :logic))
   (b* (((when (zp limit))
         (mv then nil rp-state))
        ((mv r1 r1-context-has-nil rp-state)
         (b* (((mv r1-context rp-state)
               (rp-rw-context-main cond-rw context
                                   ;;r1-rp-rw-context-main-enabled
                                   (and** (not* (equal cond-rw ''nil))
                                          ;;(not* (is-dont-rw-context cond))
                                          (end-of-if-p then)
                                          (not* (nonnil-p then))
                                          ;;(not* (equal else ''nil)) ;; if
                                          ;; rewriting an 'and' pattern, then
                                          ;; don't try to rewrite the context
                                          (not* (equal then ''nil))

                                          (not* (rw-context-disabled rp-state))
                                          (not* (backchaining-rule rp-state))
                                          )
                                   ;;r1-rp-rw-context-main-quick-enabled
                                   (and** (not* (equal cond-rw ''nil))
                                          ;;(not* (is-dont-rw-context cond))
                                          (not* (nonnil-p then))
                                          ;;(not* (equal else ''nil)) ;; if
                                          ;; rewriting an 'and' pattern, then
                                          ;; don't try to rewrite the context
                                          (not* (equal then ''nil)))
                                   (1- limit) rp-state state))
              (r1-context-has-nil (member-equal ''nil r1-context))
              ((when (or r1-context-has-nil
                         (equal cond-rw ''nil)))
               (mv ''t t rp-state))
                
              ((mv r1 rp-state)
               (rp-rw then then-dont-rw
                      #|(rp-rw-dont-rw-or (or** (equal cond-rw ''nil)
                                              r1-context-has-nil)
                                        then-dont-rw)|#
                      r1-context iff-flg 
                      (1- limit) rp-state state)))
           (mv r1 r1-context-has-nil rp-state))))
     (mv r1 r1-context-has-nil rp-state)))

 (defun rp-rw-and (term1 term2 context  limit rp-state state)
   ;; Rewrite again the (if term1 term2 'nil) pattern by swapping term1 and
   ;; term2. To be called only under iff flag.
   (declare (type (unsigned-byte 58) limit))
   
   (declare (xargs :measure (acl2::nat-list-measure (list limit
                                                          0))
                   :stobjs (state rp-state)
                   :verify-guards nil
                   :guard (and
                           (rp-termp term1)
                           (rp-termp term2)
                           (rp-term-listp context)
                           (natp limit)
                           (valid-rp-state-syntaxp rp-state))
                   :mode :logic))
   ;; if we have an "and" pattern: (if cond r1 nil)
   ;; then add r1 to the context, and try to rewrite cond again with a
   ;; small limit.
   ;; since we are flipping things around valid-sc gets messy, so keep
   ;; things small so we can extract side-conds later.
   ;; Explanation: if everything evaluated to nil. we'd lose some hyps
   ;; in inductive cases since context will have nil eval'ed
   ;; values. Cases:
   ;; 1. Say r1 evals to nil, then rewriting cond-rw with r1 in the
   ;; context can cause cond-rw to attain false side-conditions, so we
   ;; return a version without any side-conditons;
   ;; 2. Say cond-rw evals to nil, then r1 might have false
   ;; side-conditions, then rewriting cond-rw again with r1 in the
   ;; context might cause cond-rw to become nonnil, so we remove
   ;; side-conditions from r1 when rewriting cond-rw.
   ;; For the same reason, if cond-rw becomes nonnil, it will now
   ;; return r1 and we don't know anything about the correctness of its
   ;; side conditions and they may be incorrect, so we extract it all.
   (b* (((when (or (zp limit)
                   (backchaining-rule rp-state);; if working on relieving the hyp of a rule, then don't bother
                   (rw-context-disabled rp-state)))
         (mv (create-if-instance term1 term2 ''nil) rp-state))

        (rp-state (update-rw-context-disabled t rp-state))
        (current-rw-limit-throws-error (rw-limit-throws-error rp-state))
        (rp-state (update-rw-limit-throws-error nil rp-state))
        (if-rw-limit *and-pattern-flip-cons-count-limit*)
        (term2-orig term2)
        (term2 (ex-from-rp-all2 term2))
        (term1-context (append (rp-extract-context term2)
                               context))
        (term1-orig term1)
        ((mv term1 rp-state)
         (rp-rw term1 term1 ;; pass this as dont-rw to not rw the atoms
                term1-context t 
                (min (1- limit) if-rw-limit)
                rp-state state))
        (rp-state (update-rw-context-disabled nil rp-state))
        (rp-state (update-rw-limit-throws-error current-rw-limit-throws-error
                                                rp-state)))
     (mv (if (rp-equal-cnt term1 term1-orig 2)
             (create-if-instance term1-orig term2-orig ''nil)
           (create-if-instance (ex-from-rp-all2 term1)
                               term2 ''nil))

         rp-state)))

 (defun rp-rw-context-main (term context enabled quick-enabled limit rp-state state)
   (declare (type (unsigned-byte 58) limit))

   (declare (xargs :measure (acl2::nat-list-measure (list limit 0))
                   :stobjs (state rp-state)
                   :verify-guards nil
                   :guard (and
                           (rp-term-listp context)
                           (natp limit)
                           (rp-termp term)
                           (valid-rp-state-syntaxp rp-state))
                   :mode :logic))
   (b* (((when (zp limit)) (mv context rp-state))
        (context-from-term (rp-extract-context term))
        ;; try to apply the new context without any rewrite rule.
        ((mv context rp-state)
         (if (and** quick-enabled
                    (rw-context-disabled rp-state)
                    (not (backchaining-rule rp-state)))
             (b* ((extra-context1-cleaned
                   (clear-context-for-rw-only-with-context context-from-term)))
               (if extra-context1-cleaned
                   (rw-only-with-context-lst$iff-flg=t context nil extra-context1-cleaned
                                                       (* 5 *and-pattern-flip-cons-count-limit*)
                                                       rp-state state)
                 (mv context rp-state)))
           (mv context rp-state)))
        ((when (or**
                ;; if already rewriting a context, then don't try to rewrite
                ;; the context with inner ifs to save performance
                (rw-context-disabled rp-state)
                ;; if working on relieving a hyp,
                ;; then don't bother.
                (backchaining-rule rp-state)
                (not enabled)))
         (mv (append context-from-term context) rp-state))

        ;; ;; if already rewriting a context, then don't try to rewrite
        ;; ;; the context with inner ifs to save performance
        ;; ((when (rw-context-disabled rp-state))
        ;;  (mv (append (rp-extract-context term) context) rp-state))

        (& (FMT-TO-COMMENT-WINDOW "Rewriting the context with term: ~p0 ~%"
                                  (PAIRLIS2 ACL2::*BASE-10-CHARS* (LIST TERM))
                                  0 '(nil 6 7 nil) NIL))
        (& (FMT-TO-COMMENT-WINDOW "Current context: ~p0 ~%"
                                  (PAIRLIS2 ACL2::*BASE-10-CHARS* (LIST context))
                                  0 '(nil 6 7 nil) NIL))

        (current-rw-limit-throws-error (rw-limit-throws-error rp-state))
        (rp-state (update-rw-limit-throws-error nil rp-state))
        (rp-state (update-rw-context-disabled t rp-state))
        (limit (min (1- limit) *and-pattern-flip-cons-count-limit*))
        (new-context (append context-from-term context))
        #|((mv context-rw ?changed rp-state)
         (rp-rw-context context new-context limit rp-state state))
        (new-context (append context-from-term context-rw))|#

        ((mv new-context rp-state)
         (rp-rw-context-loop new-context limit 8 rp-state state))
        
        (rp-state (update-rw-limit-throws-error current-rw-limit-throws-error rp-state))
        (rp-state (update-rw-context-disabled nil rp-state)))
     (mv new-context rp-state)))

 (defun rp-rw-context-loop (context limit loop-limit rp-state state)
   (declare (type (unsigned-byte 58) limit))
   (declare (type (unsigned-byte 58) loop-limit))
   (declare (xargs :measure (acl2::nat-list-measure (list limit
                                                          loop-limit))
                   :stobjs (state rp-state)
                   :verify-guards nil
                   :guard (and
                           (natp limit)
                           (natp loop-limit) 
                           (rp-term-listp context)
                           (valid-rp-state-syntaxp rp-state))
                   :mode :logic))
   (if (or (zp limit)
           (zp loop-limit)
           (atom context))
       (mv context rp-state)
     (b* (((mv context changed rp-state)
           (rp-rw-context context context (1- limit) rp-state state)))
       (if changed
           (rp-rw-context-loop context limit (1- loop-limit) rp-state state)
         (mv context rp-state)))))
          
   
 
 (defun rp-rw-context (old-context new-context limit rp-state state)
   (declare (type (unsigned-byte 58) limit))
   (declare (xargs :measure (acl2::nat-list-measure (list limit
                                                          (acl2-count old-context)))
                   :stobjs (state rp-state)
                   :verify-guards nil
                   :guard (and
                           (rp-term-listp old-context)
                           (natp limit)
                           (rp-term-listp new-context)
                           (valid-rp-state-syntaxp rp-state))
                   :mode :logic))
   ;; returns (mv context-rw changed rp-state)
   (if (or (zp limit)
           (atom old-context))
       (mv old-context nil rp-state)
     (b* (((mv cur rp-state)
           (if (cons-count-compare (car old-context)
                                   (* 20 *and-pattern-flip-cons-count-limit*))
               (mv (car old-context) rp-state)
             (rp-rw (car old-context) nil
                    (rp-remove-equal (car old-context) new-context)
                    t  (1- limit) rp-state state)))
          ((mv rest rest-changed rp-state)
           (rp-rw-context (cdr old-context) new-context limit rp-state
                          state))
          (cur (if (equal cur ''t) (car old-context) cur))
          )
       (mv (cons-with-hint cur
                           rest
                           old-context)
           (or** rest-changed
                 (not** (rp-equal-cnt cur (car old-context) 1)))
           rp-state))))

 (defun rp-rw (term dont-rw context iff-flg  limit rp-state state)
   (declare (type (unsigned-byte 58) limit))
   
   (declare (xargs :measure (acl2::nat-list-measure (list limit 0))
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
      (if (should-not-rw dont-rw) term
        (b* (((mv term &)
              (rp-check-context term dont-rw context
                                :rw-context-flg (rw-context-disabled rp-state))))
          term))
      rp-state))
    ((or (eq (car term) 'quote)
         (eq (car term) 'list)) ;; a list instance is created by a meta rule,
     ;; do not try to rewrite it again.
     (mv term rp-state))
    ((should-not-rw dont-rw);; exit right away if said to not rewrite
     (mv term rp-state))
    ((zp limit)
     (b* ((rp-state (limit-reached-action rp-state)))
       (mv term rp-state)))
    ((is-rp$ term)
     (b* ((dont-rw (dont-rw-car
                    (dont-rw-cdr
                     (dont-rw-cdr dont-rw))))
          ((mv new-term rp-state)
           (rp-rw (caddr term)
                  dont-rw context nil  (1- limit) rp-state state))
          ((when (quotep new-term))
           (mv new-term rp-state)))
       (mv (cons-with-hint (car term)
                           (cons-with-hint (cadr term)
                                           (cons-with-hint new-term
                                                           nil
                                                           (cddr term))
                                           (cdr term))
                           term)
           rp-state)))
    #|((is-dont-rw-context term)
     (b* ((dont-rw (dont-rw-car (dont-rw-cdr dont-rw)))
          (current-rw-context-disabled (rw-context-disabled rp-state))
          (rp-state (update-rw-context-disabled t rp-state))
          ((mv term rp-state)
           (rp-rw (cadr term) dont-rw
                  context iff-flg hyp-flg (1- limit) rp-state state))
          (rp-state (update-rw-context-disabled current-rw-context-disabled
                                                  rp-state)))
       (mv term rp-state)))|#
    (t
     (b* (
          ;; update the term to see if it simplifies with respect to the
          ;; context
          ((when (and*e iff-flg
                       (check-if-relieved-with-rp term)))
           (mv ''t rp-state))

          #|((mv term dont-rw)
          (rp-check-context term dont-rw context iff-flg))|#

          ((mv rule-rewritten-flg term dont-rw rp-state)
           (rp-rw-rule term dont-rw
                       (rules-alist-outside-in-get (car term) rp-state)
                       context iff-flg t
                       (1- limit) rp-state state))

          ((when rule-rewritten-flg)
           (rp-rw term dont-rw context iff-flg  (1- limit) rp-state state))

          ;; if simplified to a constant, then exit.
          ((when (or (atom term)
                     (eq (car term) 'quote)
                     (eq (car term) 'falist)))
           (mv term rp-state))

          ((mv term rp-state)
           (cond ((is-if term)
                  ;; if the term is an "if" statement, rewrite branches accordingly.
                  (b* (((mv if-res rp-state)
                        (rp-rw-if term dont-rw context iff-flg 
                                  (1-  limit) rp-state state)))
                    (mv if-res rp-state)))
                 ((is-hide term)
                  (mv term rp-state))
                 (t (b* (((mv subterms rp-state)
                          (rp-rw-subterms (cdr term) (dont-rw-cdr dont-rw)
                                          context (1- limit) rp-state
                                          state))
                         (term (cons-with-hint (car term) subterms term))
                         ;; check if it is a cw or hard-error statements.
                         (- (rp-rw-check-hard-error-or-cw term context rp-state)))
                      (mv term rp-state)))))

          ;; if the subterms are  quotep's, then run ex-counterpart
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
          ((when (and*e iff-flg
                       (check-if-relieved-with-rp term)))
           (mv ''t rp-state))
          ((when (not rule-rewritten-flg))
           (mv term rp-state)))
       (rp-rw term dont-rw context iff-flg  (1- limit) rp-state state)))))

 (defun rp-rw-subterms (subterms dont-rw context  limit rp-state state)
   ;; call the rewriter on subterms.
   (declare (type (unsigned-byte 58) limit))
   
   (declare (xargs :measure (acl2::nat-list-measure (List limit
                                                          (acl2-count subterms)))
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
                   (1- limit)
                  rp-state
                  state))
          ((mv rest rp-state)
           (rp-rw-subterms (cdr subterms)
                           (dont-rw-cdr dont-rw)
                           context 
                           limit;;(1- limit)
                           rp-state state)))
       (mv (cons-with-hint car-subterms rest subterms)
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
                        t step-limit rp-state state))
                (context (rp-extract-context p))
                ;;(q (attach-sc-from-context context q))
                ;;(context (attach-sc-from-context-lst context context))

                (q (rp-rw-preprocessor q context rp-state state))
                (q `(casesplit-from-context-trig ,q))
                ((mv q rp-state)
                 (rp-rw q nil context t step-limit rp-state state))
                (q (rp-rw-postprocessor q context rp-state state)))
             (mv (if (nonnil-p q)
                     q
                   `(implies ,p ,q))
                 rp-state)))
          (&
           (b* ((term (rp-rw-preprocessor term nil rp-state state))
                ((mv term rp-state)
                 (rp-rw term nil nil t step-limit rp-state state))
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
