; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; simplify-defuns.lisp  --  see simplify-defuns.txt for documentation

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; TABLE OF CONTENTS
;;; -----------------
;;; Term Simplification
;;; Creating/Destroying % Symbols
;;; Definition and Lemma Generation (except lemmas for mutual-recursion)
;;; Lemma Generation for Mutual-recursion
;;; Translating Lemmas
;;; Top Level Routines
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(program)
(set-state-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Term Simplification
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun simplify-term1 (ttree term hyps equiv thints prove-assumptions ctx wrld
                             state)

; Adapted from tool2-fn in books/misc/expander.lisp.

  (prog2$
   (initialize-brr-stack state)
   (let* ((ens (ens state))
          (saved-pspv (make-pspv ens wrld state
                                 :displayed-goal term ; from, e.g., thm-fn
                                 :user-supplied-term term ;from, e.g., prove
                                 :orig-hints thints)) ;from, e.g., prove
          (new-lit (fcons-term* 'equal (fcons-term* 'hide 'xxx) term))
          (current-clause (add-literal new-lit
                                       (dumb-negate-lit-lst hyps) t)))
     (er-let* ;from waterfall1
      ((pair
        (find-applicable-hint-settings
         *initial-clause-id*
         current-clause
         nil saved-pspv ctx
         thints wrld nil state)))
      (let ((hint-settings (car pair))
            (thints (cdr pair)))
        (mv-let
         (hint-settings state)
         (cond ((null hint-settings)
                (mv nil state))
               (t (thanks-for-the-hint nil hint-settings nil state))) ;BB
         (er-let* ((pspv (load-hint-settings-into-pspv
                          t hint-settings saved-pspv nil wrld ctx state)))
           (cond
            ((intersectp-eq
              '(:do-not-induct :do-not :induct :use :cases :by)
              (strip-cars hint-settings))
             (er soft ctx
                 "It makes no sense for SIMPLIFY-TERM to be given hints for ~
                  \"Goal\" that include any of :do-not-induct, :do-not, ~
                  :induct, :use, :cases, or :by.  The hint ~p0 is therefore ~
                  illegal."
                 (cons "Goal" hint-settings)))
            (t (pprogn
                (initialize-proof-tree ;from waterfall
                 *initial-clause-id*
                 (list (list (implicate (conjoin hyps) term)))
                 ctx
                 state)
                (let* ;from simplify-clause1
                    ((rcnst
                      (change rewrite-constant
                              (access prove-spec-var pspv :rewrite-constant)
                              :force-info
                              (if (ffnnamep-lst 'if current-clause)
                                  'weak
                                t)))
                     (pts nil))
                  (mv-let
                   (contradictionp type-alist fc-pair-lst)
                   (forward-chain current-clause
                                  pts
                                  (access rewrite-constant
                                          rcnst :force-info)
                                  nil wrld ens
                                  (access rewrite-constant
                                          rcnst :oncep-override)
                                  state)
                   (declare (ignore fc-pair-lst))
                   (cond
                    (contradictionp
                     (er soft ctx
                         "Contradiction found in hypotheses using type-set ~
                          reasoning!"))
                    (t
                     (sl-let ;from simplify-clause1
                      (contradictionp simplify-clause-pot-lst)
                      (setup-simplify-clause-pot-lst current-clause
                                                     (pts-to-ttree-lst
                                                      pts)
                                                     nil ;; RBK: fc-pair-lst
                                                     type-alist
                                                     rcnst
                                                     wrld state
                                                     (initial-step-limit
                                                      wrld state))
                      (cond
                       (contradictionp
                        (er soft ctx
                            "Contradiction found in hypotheses using linear ~
                             reasoning!"))
                       (t

; We skip the call of process-equational-polys in simplify-clause1; I think
; that we can assume that by the time this is called, that call wouldn't have
; any effect anyhow.  By the way, we skipped remove-trivial-equivalence
; earlier.

; Now we continue as in rewrite-clause.

                        (let ((local-rcnst
                               (change rewrite-constant rcnst
                                       :current-literal
                                       (make current-literal
                                             :not-flg nil
                                             :atm term)))
                              (gstack (initial-gstack 'simplify-clause
                                                      nil
                                                      current-clause)))
                          (sl-let
                           (rewritten-term ttree)
                           (rewrite-entry
                            (rewrite term nil 1)
                            :rdepth (rewrite-stack-limit wrld)
                            :obj '?
                            :fnstack nil
                            :ancestors nil
                            :step-limit step-limit
                            :pre-dwp nil
                            :backchain-limit 500
                            :geneqv
                            (cadr (car (last (getprop
                                              equiv
                                              'congruences
                                              nil
                                              'current-acl2-world
                                              wrld))))
                            :pequiv-info nil)
                           (sl-let
                            (bad-ass ttree)
                            (resume-suspended-assumption-rewriting
                             ttree
                             nil
                             gstack
                             simplify-clause-pot-lst
                             local-rcnst
                             wrld
                             state
                             step-limit)
                            (cond
                             (bad-ass
                              (er soft ctx
                                  "Generated false assumption, ~p0!  So, ~
                                   rewriting is aborted, just as it would be ~
                                   in the course of a regular ACL2 proof."
                                  bad-ass))
                             (prove-assumptions
                              (mv-let
                               (pairs pspv state)
                               (process-assumptions
                                0
                                (change prove-spec-var saved-pspv
                                        :tag-tree
                                        (set-cl-ids-of-assumptions
                                         ttree *initial-clause-id*))
                                wrld state)
                               (er-let*
                                   ((ttree
                                     (accumulate-ttree-and-step-limit-into-state
                                      (access prove-spec-var pspv :tag-tree)
                                      step-limit
                                      state))
                                    (thints (value thints)))
                                 (er-let*
                                 ((new-ttree
                                   (prove-loop1 1 nil pairs pspv
                                                thints ens wrld ctx state)))
                                 (value (cons rewritten-term
                                              (cons-tag-trees
                                               ttree
                                               new-ttree)))))))
                             (t
                              (value (cons rewritten-term
                                           ttree))))))))))))))))))))))))

(defun simplify-term* (remaining-iters ttree term hyps equiv thints
                                       prove-assumptions ctx wrld state)
  (if (zp remaining-iters)
      (value (list* term t ttree))
    (er-let*
     ((term-ttree (simplify-term1 ttree term hyps equiv thints
                                  prove-assumptions ctx wrld state)))
     (if (equal term (car term-ttree))
         (value (list* term nil ttree))
       (simplify-term* (1- remaining-iters) (cdr term-ttree) (car term-ttree)
                       hyps equiv thints prove-assumptions ctx wrld state)))))

(defun simplify-term
  (repeat-limit translate-flg inhibit-output form hyps equiv hints
                prove-assumptions ctx wrld state)
  (state-global-let*
   ((inhibit-output-lst
     (if inhibit-output
         (union-eq '(proof-tree prove) (@ inhibit-output-lst))
       (@ inhibit-output-lst))))
   (let ((name-tree 'simplify-term))
     (er-let*
      ((thints (translate-hints name-tree hints ctx wrld state))
       (thyps (if translate-flg
                  (translate-term-lst hyps t t t ctx wrld state)
                (value hyps)))
       (term (if translate-flg
                 (translate form t t t ctx wrld state)
               (value form))))
      (simplify-term* repeat-limit nil term hyps equiv thints prove-assumptions
                      ctx wrld state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Creating/Destroying % Symbols
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; All the code for dealing with % should be in this section.  So, it should be
; easy enough to modify the code to use other naming schemes.

(defun strip-leading-percent-from-symbol (sym)
  (let* ((name (symbol-name sym))
         (len (length name)))
    (if (and (not (int= len 0))
             (eq (char name 0) #\%))
        (intern-in-package-of-symbol (subseq name 1 len) sym)
      sym)))

(defun strip-leading-percent-from-symbol-list (sym-list acc)

; NOTE:  Reverses the list.

  (if (endp sym-list)
      acc
    (strip-leading-percent-from-symbol-list
     (cdr sym-list)
     (cons (strip-leading-percent-from-symbol (car sym-list))
           acc))))

(mutual-recursion

(defun strip-percents (term)
  (cond
   ((variablep term) term)
   ((fquotep term) term)
   ((flambdap (ffn-symb term))

; ((lambda (vars) body) . args)

    (let ((vars (lambda-formals (ffn-symb term)))
          (body (lambda-body (ffn-symb term)))
          (args (fargs term)))
      (fcons-term (make-lambda vars (strip-percents body))
                  (strip-percents-lst args nil))))
   (t
    (fcons-term (strip-leading-percent-from-symbol (ffn-symb term))
                (strip-percents-lst (fargs term) nil)))))

(defun strip-percents-lst (x acc)
  (cond ((endp x) (reverse acc))
        (t (strip-percents-lst (cdr x) (cons (strip-percents (car x)) acc)))))

)

(defun percentify (name)
  (concatenate 'string "%" name))

(defconst *%%p* "%%P")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Definition and Lemma Generation (except lemmas for mutual-recursion)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun sublis-fn! (alist term)
  (mv-let (erp new-term)
          (sublis-fn alist term nil)
          (assert$ (null erp)
                   new-term)))

(defun %f-is-f-lemmas-rev (%f f formals-decls orig-body
                              untranslated-new-body
                              translated-new-body
                              counter old-theory wrld)

; Conses, in reverse order, all new lemmas for proving %f-is-f.  This should
; not be called for mutually recursive functions.

  (let* ((%f-name (symbol-name %f))
         (f-name (symbol-name f))
         (%%f-name (percentify %f-name))
         (%%f (intern-in-package-of-symbol %%f-name %f))
         (f-body-is-%f-body_s
          (intern-in-package-of-symbol
           (concatenate 'string f-name "-BODY-IS-" %f-name "-BODY_S")
           %f))
         (%%f-is-f
          (intern-in-package-of-symbol
           (concatenate 'string %%f-name "-IS-" f-name)
           %f))
         (f-is-%f
          (intern-in-package-of-symbol
           (concatenate 'string f-name "-IS-" %f-name)
           %f))
         (new-theory
          (intern (concatenate 'string "THEORY-"
                               (coerce (explode-atom (1+ counter) 10)
                                       'string))
                  "ACL2"))
         (recp

; We use %f below even though f might be slightly better, because that way only
; the input defs need to be included.

          (getprop %f 'recursivep nil 'current-acl2-world wrld))
         (formals (car formals-decls))
         (%%f-formals (cons %%f formals))
         ( %f-formals (cons  %f formals))
         (  f-formals (cons   f formals))
         (equal-bodies (and (not recp)
                            (equal untranslated-new-body orig-body))))

; The lemmas below are in reverse order.

    `((local
       (deftheory ,new-theory
         (union-theories '(,f-is-%f)
                         (theory ',old-theory))))

      (defthm ,f-is-%f
        (equal ,f-formals
               ,%f-formals)
        :hints (,(if recp
                     `("Goal"
                       :by
                       (:functional-instance
                        ,%%f-is-f
                        (,%%f ,%f))
                       :do-not '(preprocess) ; avoid dumb clausifier
                       :expand (,%f-formals))
                   `("Goal" :expand

; Uh oh: simplification can replace a formal with a constant.  Since %f and f
; are non-recursive, it is safe to cause all calls to be expanded.

                     ((:free ,formals ,%f-formals)
                      (:free ,formals ,f-formals))
                     :in-theory (theory ',old-theory)
                     :do-not '(preprocess) ; avoid dumb clausifier
                     ,@(and (not equal-bodies)
                            `(:use ,f-body-is-%f-body_s))))))

      ,@(cond
         (recp `((local
                  (defthm ,%%f-is-f
                    (equal ,%%f-formals
                           ,f-formals)
                    :hints (("Goal"
                             :in-theory
                             (union-theories
                              '((:induction ,%%f))
                              (theory ',old-theory))
                             :do-not '(preprocess) ; avoid dumb clausifier
                             :expand (,%%f-formals ,f-formals)
                             :induct t))))
                 (local
                  (defun ,%%f ,formals
                    ,@(cdr formals-decls) ; to include original measure etc.
                    ,(untranslate (sublis-fn! (list (cons %f %%f))
                                              translated-new-body)
                                  nil wrld)))))
         (equal-bodies nil)
         (t `((local
               (defthm ,f-body-is-%f-body_s

; Presumably the same simplification that created %body_s from %body should
; prove this theorem.

                 (equal ,untranslated-new-body ,orig-body)
                 :hints (("Goal" :do-not '(preprocess) ; avoid dumb clausifier
                          ))
                 :rule-classes nil))))))))

(defun get-state-value (sym state)
  (if (f-boundp-global sym state)
      (f-get-global sym state)
    nil))

(defun simplify-repeat-limit (state)

; This supplies the number of iterations of our calls to the rewriter.

  (or (get-state-value 'simplify-repeat-limit state)

; We could play with this limit.  But see the comment about
; simplify-repeat-limit in f-is-%f-induction-step-lemmas.

      3))

(defun simplify-inhibit (state)
  (let ((val (get-state-value 'simplify-inhibit state)))
    (case val
      ((t) nil)
      ((nil) '(prove proof-tree warning observation event summary))
      (otherwise val))))

(defun simplify-defun (info def lemmas counter old-theory ens wrld state)

; Def is (defun %foo ...) or (defund %foo ...).

; We return (mv erp new-def lemmas-out counter latest-theory state), where
; lemmas-out extends lemmas but is equal to lemmas if info is 'mut-rec.
; Except, if def is not intended to be simplified, new-def is nil.

; WARNING: This function does not modify the declare forms of def, even if %f
; is mentioned in those declare forms.

  (let* ((fn (cadr def))
         (new-fn (strip-leading-percent-from-symbol fn))
         (orig-body (car (last def))))
    (if (eq new-fn fn)
        (mv nil nil lemmas counter old-theory state)
      (mv-let
       (erp simp state)
       (pprogn
        (fms "~x0" (list (cons #\0 (cadr def))) *standard-co* state nil)
        (simplify-term (simplify-repeat-limit state)
                       t ; translate-flg
                       (simplify-inhibit state)
                       orig-body
                       nil ;hyps
                       'equal ; equiv
                       nil ; hints
                       t ; prove-assumptions
                       'simplify-defun wrld state))
       (if erp
           (mv-let (erp val state)
                   (er soft 'simplify-defun
                       "Simplification failed for the definition of ~x0."
                       fn)
                   (declare (ignore erp val))
                   (mv t nil nil counter old-theory state))
         (let* ((new-body (car simp))
                (untranslated-new-body
                 (untranslate new-body nil wrld))
                (new-body-stripped (strip-percents new-body))
                (untranslated-new-body-stripped
                 (untranslate new-body-stripped nil wrld))
                (formals-decls (butlast (cddr def) 1))
                (new-lemmas
                 (if (eq info 'mut-rec)
                     nil
                   (%f-is-f-lemmas-rev fn new-fn formals-decls
                                       orig-body
                                       untranslated-new-body
                                       new-body
                                       counter old-theory wrld)))
                (first-new-lemma (car new-lemmas))
                (new-theory-p
                 (case-match first-new-lemma
                   (('local ('deftheory . &))
                    t)
                   (& nil)))
                (new-theory
                 (if new-theory-p
                     (cadr (cadr first-new-lemma))
                   old-theory))
                (new-counter (if new-theory-p (1+ counter) counter)))
           (mv nil
               `(,(if (enabled-runep (list :definition fn) ens wrld)
                      'defun
                    'defund)
                 ,new-fn
                 ,@formals-decls
                 ,untranslated-new-body-stripped)
               (append new-lemmas lemmas)
               new-counter
               new-theory
               state)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Lemma Generation for Mutual-recursion
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun mut-rec-formals (defs formals)

; We return a list containing the unique formal parameter common to all the
; defs (each of the form (defun ...)) if there is one, else nil.

  (if (endp defs)
      formals
    (let* ((def (car defs))
           (new-formals (and (true-listp def) (caddr def)))
           (formals-okp (if formals
                            (equal formals new-formals)
                          (and (consp new-formals)
                               new-formals
                               (null (cdr new-formals))))))
      (and formals-okp
           (mut-rec-formals (cdr defs) new-formals)))))

(defun f-is-%f-list (defs formals acc)

; Returns a list of (equal (f . formals) (%f . formals)) in forward order.

  (if (endp defs)
      acc
    (f-is-%f-list (cdr defs)
                  formals
                  (let* ((%f (cadar defs))
                         (f (strip-leading-percent-from-symbol %f)))
                    (if (eq %f f)
                        acc
                      (cons `(equal (,f ,@formals)
                                    (,%f ,@formals))
                            acc))))))

(defun f-is-%f-base-lemmas (f-is-%f-list formals zp-formals acc)

; Result is in correct order if f-is-%f-list is in reverse order.

  (if (endp f-is-%f-list)
      acc
    (f-is-%f-base-lemmas
     (cdr f-is-%f-list)
     formals zp-formals
     (cons (let* ((equality (car f-is-%f-list))
                  ( f (car (cadr equality)))
                  (%f (car (caddr equality)))
                  (lemma-name
                   (intern (concatenate 'string
                                        (symbol-name f)
                                        "-IS-"
                                        (symbol-name %f)
                                        "-BASE")
                           "ACL2")))
             `(local
               (defthm ,lemma-name
                 (implies ,zp-formals
                          ,equality)

; Experimentation shows that it can be valuable first to expand without doing
; any real simplification, and then to rewrite.  We have seen assumptions get
; generated when we allow the current-theory in "Goal".

                 :hints (("Goal" :expand (( ,f ,@formals)
                                          (,%f ,@formals))))
#|
                 :hints (("Goal" :expand (( ,f ,@formals)
                                          (,%f ,@formals))
                          :do-not '(preprocess)
                          :in-theory (theory 'minimal-theory))
                         '(:computed-hint-replacement
                           t
                           :in-theory (current-theory :here)))
|#
                 )))
           acc))))

(defun f-is-%f-induction-step-lemmas (f-is-%f-list formals hyp acc)

; Result is in correct order if %f-is-f-list is in reverse order.

  (if (endp f-is-%f-list)
      acc
    (f-is-%f-induction-step-lemmas
     (cdr f-is-%f-list)
     formals hyp
     (cons (let* ((equality (car f-is-%f-list))
                  ( f (car (cadr equality)))
                  (%f (car (caddr equality)))
                  (lemma-name
                   (intern (concatenate 'string
                                        (symbol-name f)
                                        "-IS-"
                                        (symbol-name %f)
                                        "-INDUCTION_STEP")
                           "ACL2"))
                  (f-formals (cons f formals))
                  (%f-formals (cons %f formals)))
             `(local
               (defthm ,lemma-name
                 (implies ,hyp
                          (equal ,f-formals ,%f-formals))
                 :instructions
                 (:promote
                  (:dv 1)
                  :x-dumb :nx :x-dumb :top
                  (:s :normalize nil :backchain-limit 1000
                      :expand :lambdas
                      :repeat

; Probably 3 is enough, because of simplify-repeat-limit.  At any rate, we need
; at least 1 in order to apply the earlier such lemmas to the body of f.

                      4)))))
           acc))))

(defun f-is-%f-lemmas-mut-rec (f-is-%f-list formals acc)

; Result is in correct order if f-is-%f-list is in reverse order.

  (if (endp f-is-%f-list)
      acc
    (f-is-%f-lemmas-mut-rec
     (cdr f-is-%f-list)
     formals
     (cons (let* ((equality (car f-is-%f-list))
                  ( f (car (cadr equality)))
                  (%f (car (caddr equality)))
                  (lemma-name
                   (intern (concatenate 'string
                                        (symbol-name f)
                                        "-IS-"
                                        (symbol-name %f))
                           "ACL2")))
             `(defthm ,lemma-name
                (equal (,f ,@formals) (,%f ,@formals))
                :hints (("Goal" :do-not '(preprocess)))))
           acc))))

(defun mutual-recursion-lemmas (formals f-is-%f-list counter old-theory)

; The lemmas need to be returned in reverse order.

  (let* ((%%p-name (concatenate 'string
                                *%%p*
                                (coerce (explode-atom counter 10)
                                        'string)))
         (%%p (intern %%p-name "ACL2"))
         (%%p-formals (cons %%p formals))
         (%%p-property (intern (concatenate 'string %%p-name "-PROPERTY")
                               "ACL2"))
         (%%p-base (intern (concatenate 'string
                                        %%p-name
                                        "-BASE")
                           "ACL2"))
         (%%p-induction-step (intern (concatenate 'string
                                                  %%p-name
                                                  "-INDUCTION_STEP")
                                     "ACL2"))
         (not-zp-formal `(not (zp ,@formals)))
         (formal (car formals))
         (%%p-formal-minus-1 `(,%%p (1- ,formal)))
         (induction-hyp `(and ,not-zp-formal ,%%p-formal-minus-1))
         (%%p-holds (intern (concatenate 'string
                                         %%p-name
                                         "-HOLDS")
                            "ACL2"))
         (%%p-implies-f-is-%f-theory
          (intern (concatenate 'string
                               %%p-name
                               "-IMPLIES-F-IS-%F-THEORY")
                  "ACL2"))
         (new-theory
          (intern (concatenate 'string "THEORY-"
                               (coerce (explode-atom (1+ counter) 10)
                                       'string))
                  "ACL2")))
    `((local
       (deftheory ,new-theory
         (union-theories (set-difference-theories
                          (current-theory :here)
                          (current-theory ',%%p-holds))
                         (theory ',old-theory))))

      (encapsulate
       ()
       (local (in-theory (union-theories
                          '(,%%p-holds)
                          (theory ',%%p-implies-f-is-%f-theory))))
       ,@(f-is-%f-lemmas-mut-rec f-is-%f-list formals nil))

      (local
       (defthm ,%%p-holds
         ,%%p-formals
         :hints (("Goal" :induct (%%sub1-induction ,@formals)
                  :do-not '(preprocess)
                  :in-theory (union-theories '(,%%p-base
                                               ,%%p-induction-step
                                               (:induction %%sub1-induction))
                                             (theory 'minimal-theory))))))

      (local
       (encapsulate
        ()

        (local (in-theory (disable ,%%p
                                   ,%%p-base ; just an optimization
                                   )))

        (local (deflabel %%induction-start))

        ,@(f-is-%f-induction-step-lemmas f-is-%f-list formals induction-hyp
                                         nil)

        (defthm ,%%p-induction-step
          (implies ,induction-hyp
                   ,%%p-formals)
          :instructions
          (:promote :x-dumb (:s :normalize nil)))
        ))

      (local
       (encapsulate
        ()

        (local
         (in-theory (disable ,%%p-property)))

        ,@(f-is-%f-base-lemmas f-is-%f-list formals `(zp ,@formals) nil)

        (defthm ,%%p-base
          (implies (zp ,@formals)
                   ,%%p-formals)
          :instructions
          (:promote :x-dumb (:s :normalize nil)))
        ))

      (local
       (deftheory ,%%p-implies-f-is-%f-theory
         (union-theories (set-difference-theories (current-theory :here)
                                                  (current-theory ',%%p))
                         (theory 'minimal-theory))))

      (local
       (defthm ,%%p-property
         (implies (,%%p ,@formals)
                  (%%and-tree ,@f-is-%f-list))
         :HINTS
         (("Goal"
           :in-theory (union-theories '(,%%p) (theory 'minimal-theory))))))

      (local
       (defun ,%%p ,formals
         (declare (xargs :normalize nil))
         (%%and-tree ,@f-is-%f-list))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Translating Lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun my-translate-rule-class-alist (token alist seen orig-name corollary ctx
                                            wrld state)
  (cond
   ((null alist)
    (value (alist-to-keyword-alist seen nil)))
   (t
    (er-let*
     ((val (case (car alist)
             (:COROLLARY
              (value corollary))
             (:HINTS
              (value nil))
             (:INSTRUCTIONS
              (value nil))
             (:OTF-FLG
              (value (cadr alist)))
             (:TRIGGER-FNS
              (value (reverse (strip-leading-percent-from-symbol-list
                               (cadr alist) nil))))
             (:TRIGGER-TERMS
              (er-let*
               ((terms (translate-term-lst (cadr alist)
                                           t t t ctx wrld state)))
               (value (strip-percents-lst terms nil))))
             (:TYPED-TERM
              (er-let*
               ((term (translate (cadr alist) t t t ctx wrld state)))
               (value (strip-percents term))))
             (:BACKCHAIN-LIMIT-LST
              (value (cadr alist)))
             (:MATCH-FREE
              (value (cadr alist)))
             (:CLIQUE
              (let ((clique (cond ((null (cadr alist)) nil)
                                  ((atom (cadr alist))
                                   (strip-leading-percent-from-symbol
                                    (cadr alist)))
                                  (t (strip-leading-percent-from-symbol-list
                                      (cadr alist) nil)))))
                (value clique)))
             (:TYPE-SET
              (value (cadr alist)))
             #|
             (:CONTROLLER-ALIST
              (value (cadr alist)))
             (:LOOP-STOPPER
              (value (cadr alist)))
             (:PATTERN
              (er-let*
               ((term (translate (cadr alist) t t t ctx wrld state)))
; known-stobjs = t (stobjs-out = t)
               (value term)))
             (:CONDITION
              (er-let*
               ((term (translate (cadr alist) t t t ctx wrld state)))
; known-stobjs = t (stobjs-out = t)
               (value term)))
             (:SCHEME
              (er-let*
               ((term (translate (cadr alist) t t t ctx wrld state)))
; known-stobjs = t (stobjs-out = t)
               (value term)))
|#
             (otherwise
              (er soft ctx
                  "The key ~x0 is not yet implemented for rule class ~
                   translation."
                  (car alist))))))
     (my-translate-rule-class-alist
      token
      (cddr alist)
      (if val
          (let ((new-seen (cons (cons (car alist) val) seen)))
            (if (eq (car alist) :COROLLARY)
                (cons (cons :HINTS `(("Goal"
                                      :use

; !! This is dicey, because the original rule may have more than one
; :type-prescription corollary.  But if that is the case, we will get an error
; when we try to prove this theorem, and we should see the error.

                                      (,token ,orig-name))))
                      new-seen)
              new-seen))
        seen)
      orig-name corollary
      ctx wrld state)))))

(defun my-translate-rule-class1 (name class ctx wrld state)
  (let ((orig-corollary (cadr (assoc-keyword :corollary (cdr class)))))
    (er-let*
     ((corollary
       (cond (orig-corollary
              (translate orig-corollary t t t ctx wrld state))
             (t (value nil))))
; known-stobjs = t (stobjs-out = t)
      (alist
       (my-translate-rule-class-alist (car class)
                                      (cdr class)
                                      nil
                                      name
                                      (and corollary
                                           (untranslate
                                            (strip-percents corollary)
                                            t wrld))
                                      ctx wrld state)))
     (value (cons (car class) alist)))))

(defun my-translate-rule-class (name x ctx wrld state)
  (cond
   ((symbolp x) (value x))
   (t (my-translate-rule-class1 name x ctx wrld state))))

(defun my-translate-rule-classes1 (name classes ctx wrld state)
  (cond
   ((atom classes)
    (value nil))
   (t (er-let*
       ((class (my-translate-rule-class name (car classes) ctx wrld state))
        (rst (my-translate-rule-classes1 name (cdr classes) ctx wrld state)))
       (value (cons class rst))))))

(defun my-translate-rule-classes (name classes ctx wrld state)
  (cond ((atom classes) (value classes))
        (t (my-translate-rule-classes1 name classes ctx wrld state))))

(defun strip-percents-from-lemma (lemma ctx wrld state)
  (case-match lemma
    ((defthm name formula . other)
     (cond
      ((member-eq defthm '(defthm defthmd))
       (let ((new-name (strip-leading-percent-from-symbol name)))
         (if (eq name new-name)
             (value nil)
           (let ((rcs (cadr (assoc-keyword :rule-classes other))))
             (er-let*
              ((term (translate formula t t t ctx wrld state))
               (classes (my-translate-rule-classes name rcs ctx wrld state)))
              (value `(,defthm ,new-name
                        ,(untranslate (strip-percents term) t wrld)
                        :hints (("Goal" :use ,name))
                        ,@(and classes
                               (list :rule-classes
                                     classes)))))))))
      (t (value nil))))
    (& (value nil))))

(defun strip-percents-from-lemmas (lemmas acc ctx wrld state)
  (if (endp lemmas)
      (value (reverse acc))
    (er-let* ((new-lemma (strip-percents-from-lemma (car lemmas) ctx wrld
                                                    state)))
             (strip-percents-from-lemmas
              (cdr lemmas)
              (if new-lemma (cons new-lemma acc) acc)
              ctx wrld state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Top Level Routines
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun simplify-defuns (defs all-defs acc lemmas counter old-theory ens wrld
                         state)
  (cond
   ((endp defs)
    (let ((formals (mut-rec-formals all-defs nil)))
      (if formals
          (let* ((new-lemmas ; ((local (deftheory new-theory ...)) ...)
                  (mutual-recursion-lemmas formals
                                           (f-is-%f-list all-defs formals nil)
                                           counter
                                           old-theory))
                 (new-deftheory (cadr (car new-lemmas))))
            (mv nil
                (cons 'mutual-recursion (reverse acc))
                (append new-lemmas lemmas)
                (1+ counter)
                (cadr new-deftheory)
                state))
        (mv-let (erp val state)
                (er soft 'simplify-defuns
                    "Did not find a unique singleton list of formals for the ~
                     mutual-recursion nest starting with:~%~x0."
                    (car all-defs))
                (declare (ignore erp val))
                (mv t nil nil counter old-theory state)))))
   (t (mv-let
       (erp def new-lemmas counter new-theory state)
       (simplify-defun 'mut-rec (car defs) lemmas counter old-theory ens wrld
                       state)
       (if erp
           (mv t nil nil counter new-theory state)
         (simplify-defuns (cdr defs) all-defs
                          (if def (cons def acc) acc)
                          new-lemmas counter
                          new-theory ens wrld state))))))

(defun simplify-form (form lemmas counter old-theory ens wrld state)
  (let ((car-form (and (consp form) (car form))))
    (case car-form
      ((defun defund) (simplify-defun nil form lemmas counter old-theory ens
                                      wrld state))
      (mutual-recursion
       (simplify-defuns (cdr form) (cdr form) nil lemmas counter old-theory
                        ens wrld state))
      (defuns (mv-let (erp val state)
                      (er soft 'simplify-form
                          "Simplify-form does not yet handle DEFUNS, but it ~
                           could.")
                      (declare (ignore erp val))
                      (mv t nil nil counter old-theory state)))
      (otherwise (mv nil nil lemmas counter old-theory state)))))

(defun simplify-forms (forms defs lemmas counter old-theory ens wrld state)
  (cond ((endp forms)
         (pprogn
          (newline *standard-co* state)
          (mv nil
              (reverse defs)
              (case-match lemmas
                ((('local ('deftheory . &))
                  . &)
                 (cdr lemmas))
                (& lemmas))
              state)))
        (t (mv-let (erp simp-form lemmas new-counter new-theory state)
                   (simplify-form (car forms) lemmas counter old-theory ens
                                  wrld state)
                   (cond
                    (erp (mv t nil nil state))
                    (simp-form (simplify-forms
                                (cdr forms) (cons simp-form defs) lemmas
                                new-counter new-theory ens wrld state))
                    (t (simplify-forms (cdr forms) defs lemmas new-counter
                                       new-theory ens wrld state)))))))

(defun final-deftheory-1 (lemmas acc)
  (cond
   ((endp lemmas)
    acc)
   ((eq (caar lemmas) 'defthm)
    (final-deftheory-1 (cdr lemmas) (cons (cadar lemmas) acc)))
   ((eq (caar lemmas) 'encapsulate)
    (final-deftheory-1 (cdr lemmas)
                       (final-deftheory-1 (cddar lemmas) acc)))
   (t
    (final-deftheory-1 (cdr lemmas) acc))))

(defun final-deftheory (lemmas)
  `(deftheory %-removal-theory
     (union-theories
      ',(final-deftheory-1 lemmas nil)
      (theory 'minimal-theory))))

(defun initial-equality-events (in-defs out-defs)

; Returns an initial list of events, in forward order, for the f-is-%f lemmas.
; Matt K. mod for v2-9.1:  Remove support for pre-v2-7.

  (declare (ignore out-defs))
  (list (car in-defs) ; first out-def is in-package
        '(local
          (defun %%sub1-induction (n)
            (if (zp n)
                n
              (%%sub1-induction (1- n)))))
        '(local
          (defun %%and-tree-fn (args len)
            (declare (xargs :mode :program))
            (if (< len 20)
                (cons 'and args)
              (let* ((len2 (floor len 2)))
                (list 'and
                      (%%and-tree-fn (take len2 args) len2)
                      (%%and-tree-fn (nthcdr len2 args) (- len len2)))))))
        '(local
          (defmacro %%and-tree (&rest args)
            (%%and-tree-fn args (length args))))))

(include-book "file-io")

(defun write-lemma-file (infile outfile initial-events ctx state)
  (er-let*
   ((in-lemmas (read-list infile ctx state))
    (out-lemmas (strip-percents-from-lemmas in-lemmas nil ctx (w state)
                                            state)))
   (write-list (cons (car in-lemmas) ; in-package form
                     (append initial-events out-lemmas))
               outfile ctx state)))

(defun write-lemma-files (thm-file-pairs erp ctx state)
  (if (endp thm-file-pairs)
      (mv erp nil state)
    (mv-let (erp val state)
            (write-lemma-file (caar thm-file-pairs)
                              (cadar thm-file-pairs)
                              (cddar thm-file-pairs)
                              ctx state)
            (declare (ignore val))
            (write-lemma-files (cdr thm-file-pairs) erp ctx state))))

(defun transform-defuns-fn (in-defs-file    ; %f definitions
                            out-defs-file   ;  f definitions
                            equalities-file ; thms (equal (%f ..) (f ..))
                            extra-initial-events-for-defs
                            extra-initial-events-for-lemmas
                            thm-file-pairs  ; (.. ( infile  ; thms (.. %f ..)
                                            ;       outfile ; thms (..  f ..)
                                            ;       . initial-events
                                            ;     ) ..
                                            ; )
                            state)
  (let ((ctx 'transform-defuns)
        (first-lemma '(local
                       (deftheory theory-0 (theory 'minimal-theory)))))
    (mv-let
     (erp in-defs state)
     (read-list in-defs-file ctx state)
     (if erp
         (silent-error state)
       (mv-let
        (erp out-defs lemmas state)
        (if (or out-defs-file equalities-file)
            (simplify-forms in-defs nil (list first-lemma) 0 'theory-0 (ens state)
                            (w state) state)
          (mv nil nil nil state))
        (if erp
            (silent-error state)
          (er-progn
           (if out-defs-file
               (write-list (append (list (car in-defs) ; in-package form
                                         '(set-ignore-ok t)
                                         '(set-irrelevant-formals-ok t)
                                         '(set-bogus-mutual-recursion-ok t))
                                   extra-initial-events-for-defs
                                   out-defs)
                           out-defs-file ctx state)
             (value nil))
           (if equalities-file
               (write-list (append
                            (initial-equality-events in-defs out-defs)
                            extra-initial-events-for-lemmas
                            (reverse (cons (final-deftheory lemmas)
                                           lemmas)))
                           equalities-file ctx state)
             (value nil))
           (write-lemma-files thm-file-pairs nil ctx state))))))))

(defmacro transform-defuns (in-defs-file
                            &key out-defs equalities
                            defs-extra eq-extra thm-file-pairs)
  `(transform-defuns-fn ,in-defs-file ,out-defs ,equalities
                        ,defs-extra ,eq-extra ,thm-file-pairs state))
