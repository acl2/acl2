; A version of unroll-spec that uses rewriter-basic.
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

;;TODO: What about xor simplification?  maybe ok to delay?

(include-book "rewriter-basic")
(include-book "rule-lists")
(include-book "dag-to-term")
(include-book "dag-size-fast") ; for dag-or-quotep-size-less-thanp
(include-book "dag-to-term-with-lets")
(include-book "rules-in-rule-lists")
(include-book "evaluator") ;; since this calls dag-val-with-axe-evaluator to embed the resulting dag in a function, introduces a skip-proofs
(include-book "kestrel/utilities/make-event-quiet" :dir :system)
(include-book "kestrel/utilities/redundancy" :dir :system)
(include-book "kestrel/utilities/strip-stars-from-name" :dir :system)
(include-book "kestrel/utilities/system/fresh-names" :dir :system) ;drop?

;; If asked to create a theorem, this uses skip-proofs to introduce it.

(defun unroll-spec-basic-rules ()
  (append (base-rules)
          (amazing-rules-bv)
          (list-rules)
          ;; (introduce-bv-array-rules)
          ;; '(list-to-byte-array) ;; todo: add to a rule set (whatever mentions list-to-bv-array)
          ))

;; TODO: Add more options, such as :print and :print-interval, to pass through to simp-term
;; Returns (mv erp event state)
(defun unroll-spec-basic-fn (defconst-name ;should begin and end with *
                              term
                              extra-rules
                              remove-rules
                              rules
                              ;;rule-alists
                              assumptions
                              interpreted-function-alist
                              monitor
                              memoizep
                              count-hitsp
                              ;; simplify-xorsp ;todo
                              produce-function
                              disable-function
                              function-type
                              function-params
                              produce-theorem
                              print
                              whole-form
                              state)
  (declare (xargs :stobjs state
                  :mode :program ;; because this calls translate (todo: factor that out)
                  :guard (and (symbolp defconst-name)
                              ;; (pseudo-termp term) ;; really an untranlated term
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              (symbol-listp rules)
                              ;; (pseudo-term-listp assumptions) ;; untranslated terms
                              (interpreted-function-alistp interpreted-function-alist) ;todo: extract from the terms and rules?
                              (symbol-listp monitor)
                              (booleanp memoizep)
                              (booleanp count-hitsp)
                              ;; (booleanp simplify-xorsp) ;todo: strengthen
                              (booleanp produce-function)
                              (booleanp disable-function)
                              (member-eq function-type '(:term :lets :embedded-dag :auto))
                              (or (symbol-listp function-params)
                                  (eq :auto function-params))
                              (booleanp produce-theorem)))
           (ignore print) ;todo
           )
  (b* (((when (command-is-redundantp whole-form state))
        (mv nil '(value-triple :invisible) state))
       ((when (and (not produce-function)
                   (not (eq :auto function-params))))
        (er hard? 'unroll-spec-basic-fn ":function-params should not be given if :produce-function is nil.")
        (mv (erp-t) nil state))
       ((when (and (not produce-function)
                   disable-function))
        (er hard? 'unroll-spec-basic-fn ":disable-function should not be true if :produce-function is nil.")
        (mv (erp-t) nil state))
       ((when (and rules extra-rules))
        (er hard? 'unroll-spec-basic-fn ":rules and :extra-rules should not both be given.")
        (mv (erp-t) nil state))
       ((when (and rules remove-rules))
        (er hard? 'unroll-spec-basic-fn ":rules and :remove-rules should not both be given.")
        (mv (erp-t) nil state))
       (term (translate-term term 'unroll-spec-basic-fn (w state)))
       (assumptions (translate-terms assumptions 'unroll-spec-basic-fn (w state)))
       ((mv erp rule-alist)
        (make-rule-alist
         ;; Either use the user-supplied rules or the usual rules
         ;; plus any user-supplied extra rules:
         (or rules
             (set-difference-eq (append (unroll-spec-basic-rules)
                                        extra-rules)
                                remove-rules))
         (w state)))
       ((when erp) (mv erp nil state))
       ((mv erp dag)
        (simplify-term-basic term
                             assumptions
                             rule-alist
                             interpreted-function-alist
                             monitor
                             memoizep
                             count-hitsp
                             (w state)
                             ;; :assumptions assumptions
                             ;; :simplify-xorsp simplify-xorsp
                             ;; :print print
                             ))
       ((when erp)
        (mv erp nil state))
       ((when (quotep dag))
        (er hard? 'unroll-spec-basic-fn "Spec unexpectedly rewrote to the constant ~x0." dag)
        (mv :unexpected-quotep nil state))
       ;; Make a theorem if the term is small enough.  We must use skip-proofs
       ;; because Axe does not yet produce an ACL2 proof. TODO: We could
       ;; support adding the theorem even if the DAG is large is we use
       ;; dag-val-with-axe-evaluator to express the theorem.
       (dag-vars (dag-vars dag)) ;todo: check these (what should be allowed)?
       (dag-fns (dag-fns dag))
       ;; build the function:
       (function-name (intern-in-package-of-symbol
                       ;;todo: why is the re-interning needed here?
                       (symbol-name (fresh-name-in-world-with-$s (strip-stars-from-name defconst-name) nil (w state)))
                       defconst-name))
       (function-params (if (eq :auto function-params)
                            dag-vars
                          ;; the function-params given should be a permutation of the dag-vars
                          (let ((diff1 (set-difference-eq dag-vars function-params))
                                (diff2 (set-difference-eq function-params dag-vars)))
                            (if (or diff1 diff1)
                                (er hard? 'unroll-spec-basic-fn "Mismatch between supplied :function-params and the variables of the dag.  Dag has ~x0 vars.  :function-params has ~x1 vars.
Entries only in DAG: ~X23.  Entries only in :function-params: ~X45."
                                    (len dag-vars)
                                    (len function-params)
                                    diff1 nil
                                    diff2 nil)
                              function-params))))
       ;; Handle a :function-type of :auto
       (function-type (if (eq :auto function-type)
                          (if (dag-or-quotep-size-less-thanp dag 1000)
                              :term
                            :embedded-dag)
                        function-type))
       (function-body (if (eq :term function-type)
                          (dag-to-term dag)
                        (if (eq :embedded-dag function-type)
                            `(dag-val-with-axe-evaluator ,defconst-name
                                                         ,(make-acons-nest dag-vars)
                                                         ',(make-interpreted-function-alist (get-non-built-in-supporting-fns-list dag-fns (w state)) (w state))
                                                         '0 ;array depth (not very important)
                                                         )
                          ;; function-type must be :lets:
                          (dag-to-term-with-lets dag))))
       (new-term (and produce-theorem (dag-to-term dag)))
       (defconst-name-string (symbol-name defconst-name))
       (theorem-name (and produce-theorem (pack$ (subseq defconst-name-string 1 (- (length defconst-name-string) 1)) '-unroll-spec-basic-theorem)))
       (theorem (and produce-theorem
                     `(skip-proofs
                       (defthm ,theorem-name
                         (implies (and ,@assumptions)
                                  (equal ,term
                                         ,new-term))
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
                (table unroll-spec-basic-table ',whole-form ':fake)
                (value-triple ',items-created) ;todo: use cw-event and then return :invisible here?
                )
        state)))

;TODO: Automate even more by unrolling all functions down to the BV and array ops?
(defmacro unroll-spec-basic (&whole whole-form
                                    defconst-name ;; The name of the DAG constant to create
                                    term          ;; The term to simplify
                                    &key
                                    (extra-rules 'nil) ; to add to the usual set of rules
                                    (remove-rules 'nil) ; to remove from to the usual set of rules
                                    (rules 'nil) ;to completely replace the usual set of rules (TODO: default should be auto?)
                                    ;; (rule-alists) ;to completely replace the usual set of rules (TODO: default should be auto?)
                                    (assumptions 'nil)
                                    (interpreted-function-alist 'nil)
                                    (monitor 'nil)
                                    (memoizep 't)
                                    (count-hitsp 'nil)
                                    ;; (simplify-xorsp 't)
                                    (produce-function 'nil)
                                    (disable-function 'nil) ;todo: consider making 't the default
                                    (function-type ':auto)
                                    (function-params ':auto)
                                    (produce-theorem 'nil)
                                    (print 'nil))
  `(make-event-quiet (unroll-spec-basic-fn ',defconst-name
                                           ,term
                                           ,extra-rules
                                           ,remove-rules
                                           ,rules
                                           ;; ,rule-alists
                                           ,assumptions
                                           ,interpreted-function-alist
                                           ,monitor
                                           ,memoizep
                                           ,count-hitsp
                                           ;; ,simplify-xorsp
                                           ,produce-function
                                           ,disable-function
                                           ,function-type
                                           ,function-params
                                           ,produce-theorem
                                           ,print
                                           ',whole-form
                                           state)))

;; (defxdoc unroll-spec-basic
;;   :parents (axe)
;;   :short "Given a specification, unroll all recursion, yielding a DAG that only includes bit-vector and array operations."
;;   :long "<h3>General Form:</h3>
;; @({
;;      (unroll-spec-basic
;;         defconst-name        ;; The name of the DAG defconst to create
;;         term                 ;; The term to simplify
;;         [:rules]             ;; If non-nil, rules to use to completely replace the usual set of rules
;;         [:extra-rules]       ;; Rules to add to the usual set of rules, Default: nil
;;         [:remove-rules]      ;; Rules to remove from the usual set of rules, Default: nil
;;         [:assumptions]       ;; Assumptions to use when unrolling, Default: nil
;;         [:monitor]           ;; List of symbols to monitor, Default: nil
;;         [:interpreted-function-alist]           ;; Definitions of non-built-in functions to evaluate; Default: nil
;;         [:memoizep]           ;; Whether to memoize during rewriting, Default: nil
;;         [:count-hitsp]           ;; Whether to count rule hits rewriting, Default: nil
;;         [:produce-function]           ;; Whether to produce a function (in addition to a defconst), Default: nil
;;         [:disable-function]           ;; Whether to disable the produced function, Default: nil
;;         [:function-type]           ;; How to create a function for the DAG (:term, :embedded-dag, :lets, or :auto), Default:: auto
;;         [:function-params]           ;; The param to use for the produced function (specifies their order)
;;         [:produce-theorem]           ;; Whether to create a theorem stating that the dag is equal to the orignal term (using skip-proofs).
;;         [:print]           ;; How much to print
;;         )
;; })")
