; Renaming functions in untranslated terms
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/make-var-names" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "../utilities/lets")
(include-book "../utilities/lambdas")
(include-book "../utilities/doublets2")
(include-book "kestrel/utilities/translate" :dir :system)
;(include-book "kestrel/utilities/forms" :dir :system) ; for farg1, etc.
(include-book "kestrel/utilities/terms" :dir :system) ;for rename-fns, todo
(include-book "kestrel/std/system/macro-namep" :dir :system)
(include-book "kestrel/utilities/magic-macroexpand1-dollar" :dir :system)

;; The point of this utility is to preserve as much of the structure of the
;; term (macros, etc.) as possible.

;; TODO: Add tests

(defun fn-arities (names wrld)
  (declare (xargs :guard (and (symbol-listp names)
                              (plist-worldp-with-formals wrld))))
  (if (endp names)
      nil
    (cons (nfix (arity (first names) wrld)) ;todo: drop the nfix (would require everything to be defined)
          (fn-arities (rest names) wrld))))

;; Extends WRLD with a fake entry for each function in the ALIST, giving it a
;; 'FORMALS property.  ALIST maps function symbols to arities.  The length of
;; each new fake 'FORMALS property is the arity associated with the function in
;; the ALIST.
(defun add-fake-fns-to-world (name-to-arity-alist wrld)
  (declare (xargs :guard (and (symbol-alistp name-to-arity-alist)
                              (nat-listp (strip-cdrs name-to-arity-alist))
                              (plist-worldp wrld))))
  (if (endp name-to-arity-alist)
      wrld
    (let* ((pair (first name-to-arity-alist))
           (fn (car pair))
           (arity (cdr pair))
           (wrld (putprop fn 'formals (rev-make-var-names arity 'fake-formal) wrld)))
      (add-fake-fns-to-world (rest name-to-arity-alist) wrld))))

;; ;; RENAMING is an alist mapping old-fns to new-fns.  We add fake items to WRLD
;; ;; for each new-fn, giving it the arity of the corresponding old-fn.
;; (defun add-fake-fns-from-renaming-to-world (renaming wrld)
;;   (declare (xargs :guard (and (function-renamingp renaming)
;;                               (plist-worldp-with-formals wrld))))
;;   (add-fake-fns-to-world (pairlis$ (strip-cdrs renaming)
;;                                    (fn-arities (strip-cars renaming) wrld))
;;                          wrld))

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

(mutual-recursion
 ;; Renames all function calls in TERM according to ALIST.  WRLD must contain real or fake info (at least 'formals
 ;; properties) for the cdrs of ALIST, so we can translate terms mentioning them.
 (defun rename-functions-in-untranslated-term-aux (term
                                                   alist ; the renaming to apply
                                                   permissivep ;whether, when TERM fails to translate, we should simply return it unchanged (used when applying a heuristic)
                                                   count
                                                   wrld ;this may have fake function entries in it, so it may be different from (w state)
                                                   state ; needed for magic-macroexpand (why?)
                                                   )
   (declare (xargs :guard (and ;; no guard on term, though below we try to translate it
                           (symbol-alistp alist) ;; TODO: Should not rename QUOTE?
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
               ((let let*) ;;(let <bindings> ...declares... <body>)
                (let* ((bindings (farg1 term))
                       (binding-vars (strip-cars bindings))
                       (binding-terms (strip-cadrs bindings))
                       (declares (let-declares term))
                       (body (car (last (fargs term)))))
                  `(,fn ,(make-doublets binding-vars (rename-functions-in-untranslated-terms-aux binding-terms alist permissivep (+ -1 count) wrld state))
                        ,@declares ;; These can only be IGNORE, IGNORABLE, and TYPE.  TODO: What about (type (satisfies PRED) x) ?
                        ,(rename-functions-in-untranslated-term-aux body alist permissivep (+ -1 count) wrld state))))
               (b* ;; (b* (...bindings...) ...result-forms...)
                   (let* ((bindings (farg1 term))
                          (result-forms (rest (fargs term)))
                          (binders (strip-cars bindings))
                          (expressions (strip-cadrs bindings)) ;FIXME: These are not necessarily pairs
                          )
                     `(,fn ,(make-doublets binders ;do nothing to these (TODO: might some have function calls?)
                                           (rename-functions-in-untranslated-terms-aux expressions alist permissivep (+ -1 count) wrld state))
                           ,@(rename-functions-in-untranslated-terms-aux result-forms alist permissivep (+ -1 count) wrld state))))
               (cond ;;(cond <clauses>) ;; TODO: Handle clauses of length 1
                (let* ((clauses (fargs term))
                       (conditions (strip-cars clauses))
                       (vals-to-return (strip-cadrs clauses)))
                  `(cond ,@(make-doublets (rename-functions-in-untranslated-terms-aux conditions alist permissivep (+ -1 count) wrld state)
                                          (rename-functions-in-untranslated-terms-aux vals-to-return alist permissivep (+ -1 count) wrld state)))))
               ((case case-match)
                (let* ((expr (farg1 term))
                       (cases (rest (fargs term)))
                       (vals-to-match (strip-cars cases))
                       (vals-to-return (strip-cadrs cases)))
                  `(,fn ,(rename-functions-in-untranslated-term-aux expr alist permissivep (+ -1 count) wrld state)
                        ,@(make-doublets vals-to-match
                                         (rename-functions-in-untranslated-terms-aux vals-to-return alist permissivep (+ -1 count) wrld state)))))
               ;; TODO: Consider FLET (watch for capture!)
               (otherwise
                (if (macro-namep fn wrld)
                    ;; It's a macro we don't have special handling for:
                    ;; First, we check the translation of the term to see whether it mentions any of the functions to be replaced:
                    (if (not (intersection-eq (strip-cars alist) (all-fnnames translated-term)))
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
                              (b* ((- (cw "NOTE: Macroexpanding non-supported call ~x0.~%" term))
                                   ((mv erp term-expanded-one-step) (magic-macroexpand1$ term 'rename-functions-in-untranslated-term-aux wrld state))
                                   ;; Can this ever happen, given that we translated the term above?
                                   ((when erp) (er hard? 'rename-functions-in-untranslated-term-aux "Failed to macroexpand term: ~x0." term)))
                                (rename-functions-in-untranslated-term-aux term-expanded-one-step alist permissivep (+ -1 count) wrld state)))))))
                  ;; It's a function or lambda application:
                  (let* ((args (fargs term))
                         (args (rename-functions-in-untranslated-terms-aux args alist permissivep (+ -1 count) wrld state))
                         (fn (if (consp fn)
                                 ;; ((lambda (...vars...) ...declares... body) ...args...)
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
                    (cons fn args)))))))))))

 ;;rename all functions calls in TERMS according to ALIST
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

(defun rename-functions-in-untranslated-term (term
                                              renaming ; the renaming to apply
                                              fake-fns-arity-alist ; maps functions which may be mentioned in TERM (but don't yet exist) to their arities
                                              state)
  (declare (xargs :guard (and (symbol-alistp renaming)
                              (symbol-listp (strip-cdrs renaming))
                              (symbol-alistp fake-fns-arity-alist)
                              (nat-listp (strip-cdrs fake-fns-arity-alist)))
                  :mode :program ; since translation is done
                  :stobjs state))
  (let* ((wrld (w state))
         (wrld-with-fake-fns (add-fake-fns-to-world fake-fns-arity-alist wrld)))
    (rename-functions-in-untranslated-term-aux term
                                               renaming
                                               nil ;initially, don't be permissive
                                               1000000000
                                               wrld-with-fake-fns
                                               state)))
