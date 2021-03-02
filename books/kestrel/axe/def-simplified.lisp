; A tool to simplify a term and store the resulting DAG in a constant
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

;; See also unroll-spec-basic.  That one involves skip-proofs but can embed the DAG in a function (and state a theorem).
;;TODO: What about xor simplification?  maybe ok to delay?

;; TODO: Add -basic to the name of this file and the things defined here.

(include-book "rewriter-basic")
(include-book "rule-lists")
(include-book "rules-in-rule-lists")
(include-book "kestrel/utilities/make-event-quiet" :dir :system)
(include-book "kestrel/utilities/redundancy" :dir :system)

(defun def-simplified-rules ()
  (append (base-rules)
          (amazing-rules-bv)
          (list-rules)
          ;; (introduce-bv-array-rules)
          ;; '(list-to-byte-array) ;; todo: add to a rule set (whatever mentions list-to-bv-array)
          ))

;; TODO: Add more options, such as :print and :print-interval, to pass through to simp-term
;; Returns (mv erp event state)
(defund def-simplified-fn (defconst-name ;should begin and end with *
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
                              ))
           (ignore print) ;todo
           )
  (b* (((when (command-is-redundantp whole-form state))
        (mv nil '(value-triple :invisible) state))
       ((when (and rules extra-rules))
        (er hard? 'def-simplified-fn ":rules and :extra-rules should not both be given.")
        (mv (erp-t) nil state))
       ((when (and rules remove-rules))
        (er hard? 'def-simplified-fn ":rules and :remove-rules should not both be given.")
        (mv (erp-t) nil state))
       (term (translate-term term 'def-simplified-fn (w state)))
       (assumptions (translate-terms assumptions 'def-simplified-fn (w state)))
       ((mv erp rule-alist)
        (make-rule-alist
         ;; Either use the user-supplied rules or the usual rules
         ;; plus any user-supplied extra rules:
         (or rules
             (set-difference-eq (append (def-simplified-rules)
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
        (mv erp nil state)))
    (mv (erp-nil)
        ;; If dag is a quoted constant, then it gets doubly quoted here.  This
        ;; makes sense: You unquote this thing and either get a DAG or a quoted
        ;; constant, as usual:
        `(progn (defconst ,defconst-name ',dag)
                (table def-simplified-table ',whole-form ':fake)
                (value-triple ',defconst-name) ;todo: use cw-event and then return :invisible here?
                )
        state)))

;; ;; TODO: update
;; (defxdoc def-simplified
;;   :parents (axe)
;;   :short "Given a specification, unroll all recursion, yielding a DAG that only includes bit-vector and array operations."
;;   :long "<h3>General Form:</h3>

;; @({
;;      (def-simplified
;;         defconst-name             ;; The name of the DAG to create (will be a defconst)
;;         term                 ;; The term to simplify
;;         [:rules]             ;; If non-nil, rules to use to completely replace the usual set of rules
;;         [:extra-rules]       ;; Rules to add to the usual set of rules, Default: nil
;;         [:remove-rules]      ;; Rules to remove from the usual set of rules, Default: nil
;;         [:assumptions]       ;; Assumptions to use when unrolling, Default: nil
;;         [:monitor]           ;; List of symbols to monitor, Default: nil
;;         )
;; })

;; <p>To inspect the resulting form, you can use @('print-list') on the generated defconst.</p>")

;TODO: Automate even more by unrolling all functions down to the BV and array ops?
(defmacro def-simplified (&whole whole-form
                                 defconst-name ;; The name of the dag to create
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
                                 (print 'nil))
  `(make-event-quiet (def-simplified-fn
                       ',defconst-name
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
                       ,print
                       ',whole-form
                       state)))
