; A tool to rewrite a term, e.g., to unroll a spec
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also unroll-spec-basic.lisp

(include-book "rewriter")
(include-book "dag-to-term-with-lets")
(include-book "dag-size-fast")
(include-book "jvm/rule-lists-jvm") ;for amazing-rules-spec-and-dag
(include-book "rules-in-rule-lists")
(include-book "util2") ;; not strictly needed
(include-book "kestrel/utilities/make-event-quiet" :dir :system)
(include-book "kestrel/utilities/redundancy" :dir :system)
(include-book "kestrel/utilities/strip-stars-from-name" :dir :system)
(include-book "kestrel/utilities/system/fresh-names" :dir :system)

(defun unroll-spec-rules ()
  (append (amazing-rules-spec-and-dag) ;todo: reduce?
          (introduce-bv-array-rules)
          '(list-to-byte-array))) ;todo: add to a rule set (whatever mentions list-to-bv-array)

;; Is this really needed?
(defttag invariant-risk)
(set-register-invariant-risk nil) ;potentially dangerous but needed for execution speed

;; TODO: Add more options, such as :print and :print-interval, to pass through to simp-term
;; Returns (mv erp event state)
(defun unroll-spec-fn (defconst-name ;should begin and end with *
                        term extra-rules remove-rules
                        rules rule-alists assumptions monitor simplify-xorsp
                        produce-function
                        disable-function
                        function-type
                        function-params
                        produce-theorem
                        print
                        whole-form
                        state)
  (declare (xargs :stobjs (state)
                  :mode :program ;; because this calls translate
                  :guard (and (symbolp defconst-name)
                              ;; (pseudo-termp term) ;; really an untranlated term
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              (symbol-listp rules)
                              ;; (pseudo-term-listp assumptions) ;; untranslated terms
                              (symbol-listp monitor)
                              (booleanp simplify-xorsp) ;todo: strengthen
                              (booleanp produce-function)
                              (booleanp disable-function)
                              (member-eq function-type '(:auto :lets))
                              (or (symbol-listp function-params)
                                  (eq :auto function-params))
                              (booleanp produce-theorem))
                  :verify-guards nil))
  (b* (((when (command-is-redundantp whole-form state))
        (mv nil '(value-triple :invisible) state))
       ((when (and (not produce-function)
                   (not (eq :auto function-params))))
        (er hard? 'unroll-spec-fn ":function-params should not be given if :produce-function is nil.")
        (mv (erp-t) nil state))
       ((when (and (not produce-function)
                   disable-function))
        (er hard? 'unroll-spec-basic-fn ":disable-function should not be true if :produce-function is nil.")
        (mv (erp-t) nil state))
       (term (translate-term term 'unroll-spec-fn (w state)))
       (assumptions (translate-terms assumptions 'unroll-spec-fn (w state)))
       ((mv erp rule-alists)
        (if rule-alists ;; Use the user-supplied :rule-alists if given
            (mv (erp-nil) rule-alists)
          (b* (((mv erp res)
                (make-rule-alist
                 ;; Either use the user-supplied rules or the usual rules
                 ;; plus any user-supplied extra rules:
                 (or rules
                     (set-difference-eq (append (unroll-spec-rules)
                                                extra-rules)
                                        remove-rules))
                 (w state)))
               ((when erp) (mv erp nil)))
            (mv (erp-nil)
                (list res)))))
       ((when erp) (mv erp nil state))
       ((mv erp dag state)
        (simp-term term
                   :rule-alists rule-alists
                   :monitor monitor
                   :assumptions assumptions
                   :simplify-xorsp simplify-xorsp
                   :print print
                   :check-inputs nil))
       ((when erp)
        (mv erp nil state))
       ;; build the function:
       (function-name (intern-in-package-of-symbol
                       ;;todo: why is the re-interning needed here?
                       (symbol-name (fresh-name-in-world-with-$s (strip-stars-from-name defconst-name) nil (w state)))
                       defconst-name))
       (dag-vars (dag-vars dag)) ;todo: check these (what should be allowed)?
       (dag-fns (dag-fns dag))
       (function-params (if (eq :auto function-params)
                            dag-vars
                          ;; the function-params given should be a permutation of the dag-vars
                          (let ((diff1 (set-difference-eq dag-vars function-params))
                                (diff2 (set-difference-eq function-params dag-vars)))
                            (if (or diff1 diff2)
                                (er hard? 'unroll-spec-fn "Mismatch between supplied :function-params and the variables of the dag.  Dag has ~x0 vars.  :function-params has ~x1 vars.
Entries only in DAG: ~X23.  Entries only in :function-params: ~X45."
                                    (len dag-vars)
                                    (len function-params)
                                    diff1 nil
                                    diff2 nil)
                              function-params))))
       (function-body (if (eq :auto function-type)
                          (if (dag-or-quotep-size-less-thanp dag 1000)
                              (dag-to-term dag)
                            `(dag-val-with-axe-evaluator ,defconst-name
                                                         ,(make-acons-nest dag-vars)
                                                         ',(make-interpreted-function-alist (get-non-built-in-supporting-fns-list dag-fns (w state)) (w state))
                                                         '0 ;array depth (not very important)
                                                         ))
                        ;; function-type must be :lets:
                        (dag-to-term-with-lets dag)))
       ;; Make a theorem.  We must use skip-proofs because Axe does not yet
       ;; produce an ACL2 proof. TODO: We could support adding the theorem even
       ;; if the DAG is large if we use dag-val-with-axe-evaluator to express
       ;; the theorem.
       (new-term (and produce-theorem (dag-to-term dag))) ;tttodo: can explode!
       (defconst-name-string (symbol-name defconst-name))
       (theorem-name (and produce-theorem (pack$ (subseq defconst-name-string 1 (- (length defconst-name-string) 1)) '-unroll-spec-theorem)))
       (theorem (and produce-theorem
                     `(skip-proofs
                       (defthm ,theorem-name
                         (implies (and ,@assumptions)
                                  (equal ,term
                                         ,(dag-to-term dag)))
                         ;; Use :rule-classes nil if it can't be a theorem
                         ;; TODO: Use a more thorough check of whether it's a valid rewrite rule (if no change, ACL2 will reject the rule)
                         ,@(if (equal new-term term) '(:rule-classes nil) nil)))))
       (items-created (append (list defconst-name)
                              (if produce-function (list function-name) nil)
                              (if produce-theorem (list theorem-name) nil)))
       (defun-variant (if disable-function 'defund 'defun)))
    (mv (erp-nil)
        ;; If dag is a quoted constant, then it gets doubly quoted here.  This
        ;; makes sense: You unquote this thing and either get a DAG or a quoted
        ;; constant, as usual:
        `(progn (defconst ,defconst-name ',dag)
                ,@(and produce-function `((,defun-variant ,function-name ,function-params ,function-body)))
                ,@(and produce-theorem (list theorem))
                (table unroll-spec-table ',whole-form ':fake)
                (value-triple ',items-created) ;todo: use cw-event and then return :invisible here?
                )
        state)))

;; TODO: update
(defxdoc unroll-spec
  :parents (axe)
  :short "Given a specification, unroll all recursion, yielding a DAG that only includes bit-vector and array operations."
  :long "<h3>General Form:</h3>

@({
     (unroll-spec
        defconst-name             ;; The name of the DAG to create (will be a defconst)
        term                 ;; The term to simplify
        [:rules]             ;; If non-nil, rules to use to completely replace the usual set of rules
        [:extra-rules]       ;; Rules to add to the usual set of rules, Default: nil
        [:remove-rules]      ;; Rules to remove from the usual set of rules, Default: nil
        [:assumptions]       ;; Assumptions to use when unrolling, Default: nil
        [:monitor]           ;; List of symbols to monitor, Default: nil
        )
})

<p>To inspect the resulting form, you can use @('print-list') on the generated defconst.</p>")

;TODO: Automate even more by unrolling all functions down to the BV and array ops?
(defmacro unroll-spec (&whole whole-form
                              defconst-name ;; The name of the dag to create
                              term     ;; The term to simplify
                              &key
                              (extra-rules 'nil) ; to add to the usual set of rules
                              (remove-rules 'nil) ; to remove from to the usual set of rules
                              (rules 'nil) ;to completely replace the usual set of rules (TODO: default should be auto?)
                              (rule-alists) ;to completely replace the usual set of rules (TODO: default should be auto?)
                              (assumptions 'nil)
                              (monitor 'nil)
                              (simplify-xorsp 't)
                              (produce-function 'nil)
                              (disable-function 'nil) ;todo: consider making 't the default
                              (function-type ':auto)
                              (function-params ':auto)
                              (produce-theorem 'nil)
                              (print 'nil))
  `(make-event-quiet (unroll-spec-fn ',defconst-name
                                     ,term
                                     ,extra-rules
                                     ,remove-rules
                                     ,rules
                                     ,rule-alists
                                     ,assumptions
                                     ,monitor
                                     ,simplify-xorsp
                                     ,produce-function
                                     ,disable-function
                                     ,function-type
                                     ,function-params
                                     ,produce-theorem
                                     ,print
                                     ',whole-form
                                     state)))
