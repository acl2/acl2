; Replacing calls of functions in untranslated terms
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Replacing calls of functions with forms that involve their arguments (e.g.,
;; calls of new functions, perhaps with wrappers, etc.).

(include-book "helpers")
(include-book "kestrel/utilities/make-var-names" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "../utilities/lets")
(include-book "../utilities/fake-worlds")
(include-book "../utilities/lambdas")
(include-book "../utilities/doublets2")
(include-book "../alists-light/symbol-alistp")
(include-book "kestrel/utilities/translate" :dir :system)
;(include-book "kestrel/utilities/forms" :dir :system) ; for farg1, etc.
(include-book "kestrel/utilities/terms" :dir :system) ;for rename-fns, todo reduce
(include-book "kestrel/std/system/macro-namep" :dir :system)
(include-book "kestrel/utilities/magic-macroexpand1-dollar" :dir :system)

;; Returns a list like (:ARG1 :ARG2 :ARG3 :ARG4)
(defund make-arg-keywords-aux (first last)
  (declare (xargs :guard (and (posp first)
                              (natp last))
                  :measure (nfix (+ 1 (- last first)))))
  (if (or (not (mbt (integerp first)))
          (not (mbt (integerp last)))(< last first))
      nil
    (cons (intern (symbol-name (pack$ 'arg first)) "KEYWORD")
          (make-arg-keywords-aux (+ 1 first) last))))

(defthm symbol-listp-of-make-arg-keywords-aux
  (symbol-listp (make-arg-keywords-aux first last))
  :hints (("Goal" :in-theory (enable make-arg-keywords-aux))))

;; Returns a list like (:ARG1 :ARG2 :ARG3 :ARG4)
(defund make-arg-keywords (count)
  (declare (xargs :guard (natp count)))
  (make-arg-keywords-aux 1 count))

(defthm symbol-listp-of-make-arg-keywords
  (symbol-listp (make-arg-keywords count))
  :hints (("Goal" :in-theory (enable make-arg-keywords))))

;; Instantiate TEMPLATE by replacing :arg1 through arg2 with the corresponding ARGS.
;; For now, this is a really dumb replacement, since the template may be an untranslated term.
;; The template should mention :arg1, etc.
(defund replace-call (args template)
  (declare (xargs :guard (true-listp args)))
  (replace-symbols-in-tree template
                           (pairlis$ (make-arg-keywords (len args))
                                     args)))

;; Renames function symbols in TERM if indicated by ALIST.  Functions not mapped to anything ALIST are left alone.
;; (RENAME-FNs  '(foo '1 (baz (foo x y))) '((foo . bar)))
;; This is the version for translated terms.
(mutual-recursion
 (defun replace-calls (term alist)
   (declare (xargs :guard (and (pseudo-termp term)
                               (symbol-alistp alist))))
   (if (variablep term)
       term
     (if (fquotep term)
         term
       ;;function call or lambda
       (let* ((fn (ffn-symb term))
              (new-args (replace-calls-lst (fargs term) alist)))
         (if (flambdap fn)
             ;;if it's a lambda, replace calls in the body:
             `((lambda ,(lambda-formals fn) ,(replace-calls (lambda-body fn) alist))
               ,@new-args) ;todo: use make-lambda here?
           ;;if it's not a lambda:
           (let ((res (assoc-eq fn alist)))
             (if res
                 (replace-call new-args (cdr res))
               (fcons-term fn new-args))))))))

 ;;Replaces function symbols in TERMS if indicated by ALIST.
 (defun replace-calls-lst (terms alist)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (symbol-alistp alist))))
   (if (endp terms)
       nil
     (cons (replace-calls (car terms) alist)
           (replace-calls-lst (cdr terms) alist)))))

(mutual-recursion
 ;; Replaces all function calls in TERM according to ALIST, which maps function
 ;; names to templates (untranslated forms that mention the original function's
 ;; args (:arg1 through :argn)).  WRLD must contain real or fake info (at least
 ;; 'formals properties) for anything mentioned in the cdrs of ALIST, so we can
 ;; translate terms mentioning them.  TODO: Support matching a pattern with the
 ;; old call and applying the resulting unify subst to the template.
 (defun replace-calls-in-untranslated-term-aux (term
                                                alist
                                                permissivep ;whether, when TERM fails to translate, we should simply return it unchanged (used when applying a heuristic)
                                                count
                                                wrld ;this may have fake function entries in it, so it may be different from (w state)
                                                state ; needed for magic-macroexpand (why?)
                                                )
   (declare (xargs :guard (and ;; no guard on term, though below we try to translate it
                           (symbol-alistp alist) ;; TODO: Should not replace QUOTE?
                           (booleanp permissivep)
                           (natp count)
                           (plist-worldp wrld))
                   :mode :program ; because we call translate-term-with-defaults
                   :stobjs state))
   (if (zp count)
       ;; Should not happen:
       (er hard? 'replace-calls-in-untranslated-term-aux "Count reached.  Possible loop in macroexpansion.")
     (b* (((mv ctx msg-or-translated-term)
           (translate-term-with-defaults term 'replace-calls-in-untranslated-term-aux wrld))
          ((when ctx) ;; check for translation error
           (if permissivep
               ;; permissive means just return the thing unchanged (it might be an argument of a macro call, and such
               ;; things do not necessarily translate):
               term
             ;; Non-permissive mode means translation failure is an error:
             (er hard? 'replace-calls-in-untranslated-term-aux "Failed to translate ~x0. ~@1." term msg-or-translated-term)))
          ;; msg-or-translated-term was not in fact a message, so it is the translated term:
          (translated-term msg-or-translated-term))
       (if (atom term)
           term
         (if (fquotep term)
             term ; no fns to replace (we don't replace QUOTE here)
           ;;function call or lambda:
           (let* ((fn (ffn-symb term)))
             (case fn
               ((let let*) ;; (let/let* <bindings> ...declares... <body>)
                (let* ((bindings (let-bindings term))
                       (declares (let-declares term))
                       (body (let-body term))
                       (binding-vars (strip-cars bindings))
                       (binding-terms (strip-cadrs bindings)))
                  `(,fn ,(make-doublets binding-vars (replace-calls-in-untranslated-terms-aux binding-terms alist permissivep (+ -1 count) wrld state))
                        ,@declares ;; These can only be IGNORE, IGNORABLE, and TYPE.  TODO: What about (type (satisfies PRED) x) ?
                        ,(replace-calls-in-untranslated-term-aux body alist permissivep (+ -1 count) wrld state))))
               (b* ;; (b* <bindings> ...result-forms...)
                   (let ((bindings (farg1 term)))
                     (if (supported-b*-bindingsp bindings)
                         (let* ((terms (extract-terms-from-b*-bindings bindings))
                                (new-terms (replace-calls-in-untranslated-terms-aux terms alist permissivep (+ -1 count) wrld state))
                                (new-bindings (recreate-b*-bindings bindings new-terms))
                                (result-forms (rest (fargs term))))
                           `(b*
                                ,new-bindings
                              ,@(replace-calls-in-untranslated-terms-aux result-forms alist permissivep (+ -1 count) wrld state)))
                       ;; Not a supported b*, so macroexpand one step and try again:
                       (prog2$
                        (cw "NOTE: Macroexpanding non-supported b* form: ~x0.~%" term) ; suppress?
                        (replace-calls-in-untranslated-term-aux (magic-macroexpand1$$ term 'replace-calls-in-untranslated-term-aux wrld state)
                                                                alist permissivep (+ -1 count) wrld state)))))
               (cond ;; (cond <clauses>)
                ;; Note that cond clauses can have length 1 or 2.  We flatten the clauses, process the resulting list of untranslated terms, and then recreate the clauses
                ;; by walking through them and putting in the new items:
                (let* ((clauses (fargs term))
                       (items (append-all2 clauses))
                       (new-items (replace-calls-in-untranslated-terms-aux items alist permissivep (+ -1 count) wrld state)))
                  `(cond ,@(recreate-cond-clauses clauses new-items))))
               ((case) ;; (case <expr> ...cases...)
                (let* ((expr (farg1 term))
                       (cases (rest (fargs term)))
                       (vals-to-match (strip-cars cases))
                       (vals-to-return (strip-cadrs cases)))
                  `(case ,(replace-calls-in-untranslated-term-aux expr alist permissivep (+ -1 count) wrld state)
                     ,@(make-doublets vals-to-match
                                      (replace-calls-in-untranslated-terms-aux vals-to-return alist permissivep (+ -1 count) wrld state)))))
               ((case-match)              ;; (case-match <var> ...cases...)
                (let* ((var (farg1 term)) ; must be a symbol
                       (cases (rest (fargs term)))
                       (terms-from-cases (extract-terms-from-case-match-cases cases))
                       (new-terms-from-cases (replace-calls-in-untranslated-terms-aux terms-from-cases alist permissivep (+ -1 count) wrld state))
                       (new-cases (recreate-case-match-cases cases new-terms-from-cases)))
                  `(case-match ,var ; no change since it's a symbol
                     ,@new-cases)))
               ;; TODO: Consider FLET (watch for capture!)
               (otherwise
                (if (macro-namep fn wrld)
                    ;; It's a macro we don't have special handling for:
                    ;; First, we check the translation of the term to see whether it mentions any of the functions to be replaced:
                    (if (not (intersection-eq (strip-cars alist) (all-fnnames translated-term))) ; todo: optimize this.  do it sooner?
                        ;; No name to be replaced appears in the translation of TERM, so we can just return TERM (this will be more
                        ;; readable than its translation):
                        term
                      ;; Some replacement does need to be done:
                      (b* ( ;; We seek an untranslated term that translates to this but is nicer:
                           (translated-term-after-replacement (replace-calls translated-term alist))
                           ;; Heuristic #1: See if we can just dumbly replace symbols in the macro call (this may often work, but not if a function name to be replaced occurs as a variable or a piece of other syntax passed to a macro, or if a macro hides a function call):
                           (dumb-replacement (replace-symbols-in-tree term alist))
                           ((mv ctx translated-dumb-replacement) (translate-term-with-defaults dumb-replacement 'replace-calls-in-untranslated-term-aux wrld)))
                        (if (and (not ctx) ; no error
                                 (equal translated-dumb-replacement translated-term-after-replacement))
                            ;; The dumb-replacement translates to the right thing, so use it (will be more readable than if we expand the macro call):
                            dumb-replacement
                          ;; Heuristic #2: Try treating the macro args as terms and process them recursively.  Then see if the new macro call translates to the right thing.
                          (b* ((term-with-translated-args
                                (cons fn (replace-calls-in-untranslated-terms-aux (fargs term) alist
                                                                                  t ;be permissive, since the macro args may not translate
                                                                                  (+ -1 count) wrld state)))
                               ((mv erp translated-term-with-translated-args) (translate-term-with-defaults term-with-translated-args 'replace-calls-in-untranslated-term-aux wrld)))
                            (if (and (not erp)
                                     (equal translated-term-with-translated-args translated-term-after-replacement))
                                ;; The term with processed args translates to the right thing, so use it (will be more readable than if we expand the macro call):
                                term-with-translated-args
                              ;; None of the above worked, so macroexpand one step and try again:
                              (prog2$
                               (cw "NOTE: Macroexpanding non-supported form: ~x0.~%" term) ; suppress?
                               (replace-calls-in-untranslated-term-aux (magic-macroexpand1$$ term 'replace-calls-in-untranslated-term-aux wrld state)
                                                                       alist permissivep (+ -1 count) wrld state)))))))
                  ;; It's a function or lambda application:
                  (let* ((new-args (replace-calls-in-untranslated-terms-aux (fargs term) alist permissivep (+ -1 count) wrld state)))
                    (if (consp fn)
                        ;; ((lambda <formals> ...declares... <body>) ...args...)
                        ;;if it's a lambda application, replace calls in the body:
                        ;; TODO: Consider unclosed lambdas (translation closes them)
                        (let* ((lambda-formals (ulambda-formals fn))
                               (declares (ulambda-declares fn))
                               (lambda-body (ulambda-body fn))
                               (new-lambda-body (replace-calls-in-untranslated-term-aux lambda-body alist permissivep (+ -1 count) wrld state))
                               (new-fn (make-ulambda lambda-formals declares new-lambda-body)))
                          (cons new-fn new-args))
                      ;;if it's not a lambda:
                      (let ((res (assoc-eq fn alist)))
                        (if res
                            ;; Replace this call:
                            (replace-call new-args (cdr res))
                          ;; Don't replace:
                          (fcons-term fn new-args))))))))))))))

 ;; replace all functions calls in TERMS according to ALIST
 (defun replace-calls-in-untranslated-terms-aux (terms alist permissivep count wrld state)
   (declare (xargs :guard (and ;(untranslated-term-listp terms)
                           ;;(true-listp terms)
                           (symbol-alistp alist))
                   :stobjs state))
   (if (zp count)
       (er hard? 'replace-calls-in-untranslated-terms-aux "Count reached.")
     (if (atom terms) ;should be nil, but we don't check
         nil
       (cons (replace-calls-in-untranslated-term-aux (first terms) alist permissivep (+ -1 count) wrld state)
             (replace-calls-in-untranslated-terms-aux (rest terms) alist permissivep (+ -1 count) wrld state))))))

(defund replace-calls-in-untranslated-term (term
                                            alist ; the replacement to apply
                                            wrld ; must contain real or fake entries for all functions in TERM and in the cdrs of ALIST
                                            state ; needed for magic-macroexpand (why?)
                                            )
  (declare (xargs :guard (and (symbol-alistp alist)
                              ;; (symbol-listp (strip-cdrs function-renaming))
                              (plist-worldp wrld))
                  :mode :program ; since translation is done
                  :stobjs state))
  (replace-calls-in-untranslated-term-aux term
                                          alist
                                          nil ;initially, don't be permissive
                                          1000000000
                                          (table-programmatic 'acl2-defaults-table :ignore-ok t wrld) ;todo: instead, improve the individual calls to translate
                                          state))
