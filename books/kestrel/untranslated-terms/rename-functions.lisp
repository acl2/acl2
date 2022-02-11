; Renaming functions in untranslated terms
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/make-var-names" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "../utilities/lets")
(include-book "../utilities/fake-worlds")
(include-book "../utilities/lambdas")
(include-book "../utilities/doublets2")
(include-book "kestrel/utilities/translate" :dir :system)
;(include-book "kestrel/utilities/forms" :dir :system) ; for farg1, etc.
(include-book "kestrel/utilities/terms" :dir :system) ;for rename-fns, todo
(include-book "kestrel/std/system/macro-namep" :dir :system)
(include-book "kestrel/utilities/magic-macroexpand1-dollar" :dir :system)

;; The point of this utility is to preserve as much of the structure of the
;; term (macro calls, named constants, lets, etc.) as possible.

;; See tests in rename-functions-tests.lisp.

;; move
;; Returns the acl2-defaults-table as an alist.
(defund acl2-defaults-table-alist (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (let ((result (table-alist 'acl2-defaults-table wrld)))
    (if (not (alistp result))
        (er hard? 'acl2-defaults-table-alist "ACL2 defaults table is not an alist.") ; should never happen
      result)))

(defthm alistp-of-acl2-defaults-table-alist
  (alistp (acl2-defaults-table-alist wrld))
  :hints (("Goal" :in-theory (enable acl2-defaults-table-alist))))

;; Sets the ignore-ok property in WRLD to t.
;; Returns a new world.
(defund set-ignore-ok-in-world (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (putprop 'acl2-defaults-table
           'table-alist
           (acons :ignore-ok t (acl2-defaults-table-alist wrld))
           wrld))

;; Throws an error if macroexpansion fails.  Returns the term with one macro call now expanded.
(defund magic-macroexpand1$$ (term ctx wrld state)
  (declare (xargs :mode :program
                  :stobjs state))
  (b* ((- (cw "NOTE: Macroexpanding non-supported call ~x0.~%" term))
       ((mv erp term-expanded-one-step) (magic-macroexpand1$ term ctx wrld state))
       ;; Can this ever happen, given that we translated the term above?
       ((when erp) (er hard? 'rename-functions-in-untranslated-term-aux "Failed to macroexpand term: ~x0." term)))
    term-expanded-one-step))

;; Dumb replacement, without trying to determine whether symbols are vars,
;; function names, stuff passed to macros, etc.  TODO: Maybe stop if 'QUOTE is
;; encountered?
(defun replace-symbols-in-tree (tree alist)
  (declare (xargs :guard (symbol-alistp alist)))
  (if (atom tree)
      (if (symbolp tree)
          ;; Attempt to replace the symbol using the alist:
          (let ((res (assoc-eq tree alist)))
            (if res
                (cdr res)
              tree))
        ;; Non-symbol atom:
        tree)
    ;; TREE must be a cons:
    (cons (replace-symbols-in-tree (car tree) alist)
          (replace-symbols-in-tree (cdr tree) alist))))

;move
;clash
;similar to flatten
(defun append-all2 (lists)
  (declare (xargs :guard (true-listp lists)))
  (if (endp lists)
      nil
    (append (true-list-fix (first lists))
            (append-all2 (rest lists)))))

;; Replace the terms in the CLAUSES with the corresponding NEW-TERMS, which
;; come in order and correspond to the terms in the existing CLAUSES.  Note
;; that each element of CLAUSES may have length 1 or 2.
(defun recreate-cond-clauses (clauses new-terms)
  (if (endp clauses)
      nil
    (let* ((clause (first clauses))
           (clause-len (len clause)) ;can be 1 or 2
           )
      (cons (take clause-len new-terms) ; the new clause
            (recreate-cond-clauses (rest clauses)
                                   (nthcdr clause-len new-terms))))))

;; Extract the bodies of the items.  These are the untranslated terms that need to be handled.
;; TODO: What about a decl of (type (satisfies foo)) where perhaps FOO is a function to replace?
(defun extract-terms-from-case-match-cases (cases ;each is either (<pat> <body>) or (<pat> <dcl> <body>).
                                            )
  (declare (xargs :guard (true-list-listp cases)))
  (if (endp cases)
      nil
    (let ((case (first cases)))
      (if (= 2 (len case))
          ;; case is (<pat> <body>):
          (cons (second case) (extract-terms-from-case-match-cases (rest cases)))
        ;; case is (<pat> <dcl> <body>):
        (cons (third case) (extract-terms-from-case-match-cases (rest cases)))))))

;; Whenever there is a term in the cases, use the corresponding term from new-terms-from-cases.
(defun recreate-case-match-cases (cases new-terms-from-cases)
  (declare (xargs :guard (and (true-list-listp cases)
                              (true-listp new-terms-from-cases))))
  (if (endp cases)
      nil
    (let ((case (first cases)))
      (if (= 2 (len case))
          ;; case is (<pat> <body>):
          (cons (list (first case) (first new-terms-from-cases))
                (recreate-case-match-cases (rest cases) (rest new-terms-from-cases)))
        ;; case is (<pat> <dcl> <body>):
        (cons (list (first case) (second case) (first new-terms-from-cases))
              (recreate-case-match-cases (rest cases) (rest new-terms-from-cases)))))))

(defun supported-b*-bindingp (binding)
  (declare (xargs :guard t))
  (and (true-listp binding)
       (consp binding)
       (let ((binder (first binding)))
         (if (atom binder)
             (or (eq binder '-) ; (- <term> ... <term>) for any number of terms
                 (and (symbolp binder) ; (<var> <term)
                      (= 1 (len (fargs binding)))))
           (case (car binder)
             ((when if unless) (= 1 (len (fargs binder)))) ; ((when <term>) <term> ... <term>)
             (mv (and (symbol-listp (fargs binder)) ; ((mv <var> ... <var>) <term>)
                      (= 1 (len (fargs binding)))))
             ;; todo: add more kinds of supported binder
             (otherwise nil))))))

(defun supported-b*-bindingsp (bindings)
  (declare (xargs :guard t))
  (if (atom bindings)
      (null bindings)
    (and (supported-b*-bindingp (first bindings))
         (supported-b*-bindingsp (rest bindings)))))

(defund extract-terms-from-b*-binding (binding)
  (declare (xargs :guard (supported-b*-bindingp binding)))
  (let ((binder (first binding)))
    (if (symbolp binder)
        (if (eq binder '-) ; (- <term> ... <term>) for any number of terms
            (fargs binding)
          ;; it's a variable:
          (list (farg1 binding)))
      (case (car binder)
        ((when if unless) (cons (farg1 binder) (fargs binding)))
        (mv (list (farg1 binding)))
        ;; Should never happen:
        (t (er hard 'extract-terms-from-b*-binding "Unsupported b* binder: ~x0." binding))))))

(defthm true-listp-of-extract-terms-from-b*-binding
  (implies (supported-b*-bindingp binding)
           (true-listp (extract-terms-from-b*-binding binding)))
  :hints (("Goal" :in-theory (enable extract-terms-from-b*-binding))))

;; Extracts all the terms in the b* bindings, in order
(defun extract-terms-from-b*-bindings (bindings)
  (declare (xargs :guard (supported-b*-bindingsp bindings)))
  (if (endp bindings)
      nil
    (append (extract-terms-from-b*-binding (first bindings))
            (extract-terms-from-b*-bindings (rest bindings)))))

;; Returns (mv new-binding rest-new-terms).
(defun recreate-b*-binding (binding new-terms)
  (declare (xargs :guard (and (supported-b*-bindingp binding)
                              (true-listp new-terms))))
  (let* ((binder (first binding)))
    (if (symbolp binder)
        (if (eq binder '-) ; (- <term> ... <term>) for any number of terms
            (let ((num-terms (len (fargs binding))))
              (mv `(,binder ,@(take num-terms new-terms))
                  (nthcdr num-terms new-terms)))
          ;; it's a variable:
          (mv `(,binder ,(first new-terms)) ; (<var> <term)
              (rest new-terms)))
      (case (car binder)
        ((when if unless) ; ((when <term>) <term> ... <term>)
         (let ((num-args (len (fargs binding))))
           (mv `((,(car binder) ,(first new-terms)) ,@(take num-args (rest new-terms)))
               (nthcdr (+ 1 num-args) new-terms))))
        (mv ; ((mv <var> ... <var>) <term>)
         (mv `((mv ,@(fargs binder)) ,(first new-terms))
             (rest new-terms)))
        ;; Should never happen:
        (otherwise (progn$ (er hard 'recreate-b*-binding "Unsupported b* binder: ~x0." binding)
                           (mv nil nil)))))))

(defun recreate-b*-bindings (bindings new-terms)
  (declare (xargs :guard (and (supported-b*-bindingsp bindings)
                              (true-listp new-terms))))
  (if (endp bindings)
      nil
    (mv-let (new-first new-terms)
      (recreate-b*-binding (first bindings) new-terms)
      (let ((new-rest (recreate-b*-bindings (rest bindings) new-terms)))
        (cons new-first new-rest)))))

(mutual-recursion
 ;; Renames all function calls in TERM according to ALIST.  WRLD must contain real or fake info (at least 'formals
 ;; properties) for the cdrs of ALIST, so we can translate terms mentioning them.
 ;; TODO: Consider generalizing what happens when we find the matching function (e.g., generate some specific term using the args, such as a wrapped call of a new function)
 ;; Perhaps even try to match a pattern with the old call and apply the resulting unify subst to another pattern (but need rebust code for sublis on untranslated terms).
 (defun rename-functions-in-untranslated-term-aux (term
                                                   alist ; the renaming to apply
                                                   permissivep ;whether, when TERM fails to translate, we should simply return it unchanged (used when applying a heuristic)
                                                   count
                                                   wrld ;this may have fake function entries in it, so it may be different from (w state)
                                                   state ; needed for magic-macroexpand (why?)
                                                   )
   (declare (xargs :guard (and ;; no guard on term, though below we try to translate it
                           (symbol-alistp alist) ;; TODO: Should not rename QUOTE?
                           (booleanp permissivep)
                           (natp count)
                           (plist-worldp wrld))
                   :mode :program ; because we call translate-term-with-defaults
                   :stobjs state))
   (if (zp count)
       ;; Should not happen:
       (er hard? 'rename-functions-in-untranslated-term-aux "Count reached.  Possible loop in macroexpansion.")
     (b* (((mv ctx msg-or-translated-term)
           (translate-term-with-defaults term 'rename-functions-in-untranslated-term-aux wrld))
          ((when ctx) ;; check for translation error
           (if permissivep
               ;; permissive means just return the thing unchanged (it might be an argument of a macro call, and such
               ;; things do not necessarily translate):
               term
             ;; Non-permissive mode means translation failure is an error:
             (er hard? 'rename-functions-in-untranslated-term-aux "Failed to translate ~x0. ~@1." term msg-or-translated-term)))
          ;; msg-or-translated-term was not in fact a message, so it is the translated term:
          (translated-term msg-or-translated-term))
       (if (atom term)
           term
         (if (fquotep term)
             term ; no fns to rename (we don't rename QUOTE here)
           ;;function call or lambda:
           (let* ((fn (ffn-symb term)))
             (case fn
               ((let let*) ;; (let/let* <bindings> ...declares... <body>)
                (let* ((bindings (let-bindings term))
                       (declares (let-declares term))
                       (body (let-body term))
                       (binding-vars (strip-cars bindings))
                       (binding-terms (strip-cadrs bindings)))
                  `(,fn ,(make-doublets binding-vars (rename-functions-in-untranslated-terms-aux binding-terms alist permissivep (+ -1 count) wrld state))
                        ,@declares ;; These can only be IGNORE, IGNORABLE, and TYPE.  TODO: What about (type (satisfies PRED) x) ?
                        ,(rename-functions-in-untranslated-term-aux body alist permissivep (+ -1 count) wrld state))))
               (b* ;; (b* <bindings> ...result-forms...)
                   (let ((bindings (farg1 term)))
                     (if (supported-b*-bindingsp bindings)
                         (let* ((terms (extract-terms-from-b*-bindings bindings))
                                (new-terms (rename-functions-in-untranslated-terms-aux terms alist permissivep (+ -1 count) wrld state))
                                (new-bindings (recreate-b*-bindings bindings new-terms))
                                (result-forms (rest (fargs term))))
                           `(b*
                             ,new-bindings
                             ,@(rename-functions-in-untranslated-terms-aux result-forms alist permissivep (+ -1 count) wrld state)))
                       ;; Not a supported b*, so macroexpand one step and try again:
                       (prog2$
                        (cw "NOTE: Macroexpanding non-supported b* form: ~x0.~%" term)
                        (rename-functions-in-untranslated-term-aux (magic-macroexpand1$$ term 'rename-functions-in-untranslated-term-aux wrld state)
                                                                   alist permissivep (+ -1 count) wrld state)))))
               (cond ;; (cond <clauses>)
                ;; Note that cond clauses can have length 1 or 2.  We flatten the clauses, process the resulting list of untranslated terms, and then recreate the clauses
                ;; by walking through them and putting in the new items:
                (let* ((clauses (fargs term))
                       (items (append-all2 clauses))
                       (new-items (rename-functions-in-untranslated-terms-aux items alist permissivep (+ -1 count) wrld state)))
                  `(cond ,@(recreate-cond-clauses clauses new-items))))
               ((case) ;; (case <expr> ...cases...)
                (let* ((expr (farg1 term))
                       (cases (rest (fargs term)))
                       (vals-to-match (strip-cars cases))
                       (vals-to-return (strip-cadrs cases)))
                  `(case ,(rename-functions-in-untranslated-term-aux expr alist permissivep (+ -1 count) wrld state)
                     ,@(make-doublets vals-to-match
                                      (rename-functions-in-untranslated-terms-aux vals-to-return alist permissivep (+ -1 count) wrld state)))))
               ((case-match) ;; (case-match <var> ...cases...)
                (let* ((var (farg1 term)) ; must be a symbol
                       (cases (rest (fargs term)))
                       (terms-from-cases (extract-terms-from-case-match-cases cases))
                       (new-terms-from-cases (rename-functions-in-untranslated-terms-aux terms-from-cases alist permissivep (+ -1 count) wrld state))
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
                           (translated-term-after-replacement (rename-fns translated-term alist))
                           ;; Heuristic #1: See if we can just dumbly replace symbols in the macro call (this may often work, but not if a function name to be replaced occurs as a variable or a piece of other syntax passed to a macro, or if a macro hides a function call):
                           (dumb-replacement (replace-symbols-in-tree term alist))
                           ((mv ctx translated-dumb-replacement) (translate-term-with-defaults dumb-replacement 'rename-functions-in-untranslated-term-aux wrld)))
                        (if (and (not ctx) ; no error
                                 (equal translated-dumb-replacement translated-term-after-replacement))
                            ;; The dumb-replacement translates to the right thing, so use it (will be more readable than if we expand the macro call):
                            dumb-replacement
                          ;; Heuristic #2: Try treating the macro args as terms and process them recursively.  Then see if the new macro call translates to the right thing.
                          (b* ((term-with-translated-args
                                (cons fn (rename-functions-in-untranslated-terms-aux (fargs term) alist
                                                                                      t ;be permissive, since the macro args may not translate
                                                                                      (+ -1 count) wrld state)))
                               ((mv erp translated-term-with-translated-args) (translate-term-with-defaults term-with-translated-args 'rename-functions-in-untranslated-term-aux wrld)))
                            (if (and (not erp)
                                     (equal translated-term-with-translated-args translated-term-after-replacement))
                                ;; The term with processed args translates to the right thing, so use it (will be more readable than if we expand the macro call):
                                term-with-translated-args
                              ;; None of the above worked, so macroexpand one step and try again:
                              (rename-functions-in-untranslated-term-aux (magic-macroexpand1$$ term 'rename-functions-in-untranslated-term-aux wrld state)
                                                                         alist permissivep (+ -1 count) wrld state))))))
                  ;; It's a function or lambda application:
                  (let* ((args (fargs term))
                         (args (rename-functions-in-untranslated-terms-aux args alist permissivep (+ -1 count) wrld state))
                         (new-fn (if (consp fn)
                                     ;; ((lambda <formals> ...declares... <body>) ...args...)
                                     ;;if it's a lambda application, replace calls in the body:
                                     ;; TODO: Consider unclosed lambdas (translation closes them)
                                     (let* ((lambda-formals (ulambda-formals fn))
                                            (declares (ulambda-declares fn))
                                            (lambda-body (ulambda-body fn))
                                            (new-lambda-body (rename-functions-in-untranslated-term-aux lambda-body alist permissivep (+ -1 count) wrld state))
                                            (new-fn (make-ulambda lambda-formals declares new-lambda-body)))
                                       new-fn)
                                   ;;if it's not a lambda:
                                   (let ((res (assoc-eq fn alist)))
                                     (if res
                                         ;; Rename this function:
                                         (cdr res)
                                       ;; Don't rename:
                                       fn)))))
                    (cons new-fn args)))))))))))

 ;; rename all functions calls in TERMS according to ALIST
 (defun rename-functions-in-untranslated-terms-aux (terms alist permissivep count wrld state)
   (declare (xargs :guard (and ;(untranslated-term-listp terms)
                           ;;(true-listp terms)
                           (symbol-alistp alist))
                   :stobjs state))
   (if (zp count)
       (er hard? 'rename-functions-in-untranslated-terms-aux "Count reached.")
     (if (atom terms) ;should be nil, but we don't check
         nil
       (cons (rename-functions-in-untranslated-term-aux (first terms) alist permissivep (+ -1 count) wrld state)
             (rename-functions-in-untranslated-terms-aux (rest terms) alist permissivep (+ -1 count) wrld state))))))

(defund rename-functions-in-untranslated-term-with-fake-world (term
                                                               function-renaming ; the renaming to apply
                                                               wrld ; must contain real or fake entries for all functions in TERM
                                                               state ; needed for magic-macroexpand (why?)
                                                               )
  (declare (xargs :guard (and (symbol-alistp function-renaming)
                              (symbol-listp (strip-cdrs function-renaming))
                              (plist-worldp wrld))
                  :mode :program ; since translation is done
                  :stobjs state))
  (rename-functions-in-untranslated-term-aux term
                                             function-renaming
                                             nil ;initially, don't be permissive
                                             1000000000
                                             wrld
                                             state))

(defund rename-functions-in-untranslated-term (term ; and untranslated term
                                               function-renaming ; the renaming to apply
                                               state ; needed for magic-macroexpand (why?)
                                               )
  (declare (xargs :guard (and (symbol-alistp function-renaming)
                              (symbol-listp (strip-cdrs function-renaming)))
                  :mode :program ; since translation is done
                  :stobjs state))
  (let* ((wrld (w state))
         (wrld (set-ignore-ok-in-world wrld))
         (new-fns-arity-alist (pairlis$ (strip-cdrs function-renaming)
                                        (fn-arities (strip-cars function-renaming) wrld)))
         ;; New fns from the renaming may appear in TERM, but they are not yet
         ;; in the world, so we make this fake world:
         (fake-wrld (add-fake-fns-to-world new-fns-arity-alist wrld))
         )
    (rename-functions-in-untranslated-term-with-fake-world term
                                                           function-renaming ; the renaming to apply
                                                           fake-wrld ; contains real for fake entries for all functions in TERM
                                                           state
                                                           )))
