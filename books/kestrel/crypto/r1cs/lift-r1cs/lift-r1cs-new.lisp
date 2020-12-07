; Lifter for R1CSes (in sparse form)
;
; Copyright (C) 2019-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

;; This is for R1CSes in sparse form

(include-book "lift-r1cs-rules")
(include-book "lift-r1cs-rule-lists")
(include-book "../sparse/rule-lists")
(include-book "../sparse/rules-axe")
(include-book "../sparse/rules")
(include-book "filter-and-combine-symbol-alists")
(include-book "lift-r1cs-common")
(include-book "kestrel/axe/def-simplified" :dir :system)
(include-book "kestrel/prime-fields/prime-fields-rules-axe" :dir :system)
(include-book "kestrel/prime-fields/rules2" :dir :system)
(include-book "kestrel/utilities/ensure-rules-known" :dir :system)

(acl2::ensure-rules-known (lift-r1cs-rules))

;; Returns (mv erp event state).
(defun lift-r1cs-new-fn (name-of-defconst
                         vars
                         constraints
                         prime
                         extra-rules remove-rules rules
                         monitor memoizep
                         count-hitsp
                         print
                         whole-form state)
  (declare (xargs :guard (and (symbolp name-of-defconst)
                              (symbol-listp vars)
                              (r1cs-constraint-listp constraints)
                              ;;(r1csp r1cs)
                              (natp prime) ;;(rtl::primep prime) ;todo, slow!
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              (symbol-listp rules)
                              (symbol-listp monitor)
                              (booleanp memoizep)
                              (booleanp count-hitsp))
                  :mode :program
                  :stobjs state))
  (let* (;(vars (r1cs->vars r1cs))
         ;(constraints (r1cs->constraints r1cs))
         (term-to-simplify `(r1cs::r1cs-constraints-holdp ',constraints
                                                          ,(make-valuation-from-keyword-vars2 vars)
                                                          ',prime)))
    (acl2::def-simplified-fn name-of-defconst
                             term-to-simplify
                             ;; The extra rules:
                             (if rules
                                 nil ;rules are given below, so extra-rules are not allowed
                               (append (lift-r1cs-rules)
                                       extra-rules))
                             remove-rules
                             rules ;to override the default
                             ;; nil ;rule-alists
                             ;; drop? but we need to know that all lookups of vars give integers:
                             (make-fep-assumptions-from-keyword-vars vars prime)
                             ;; TODO: Add more functions to this?
                             ;; TODO: Make this once and store it?
                             (acl2::make-interpreted-function-alist '(r1cs::r1cs-constraint->a$inline
                                                                      r1cs::r1cs-constraint->b$inline
                                                                      r1cs::r1cs-constraint->c$inline
                                                                      assoc-equal ; called by r1cs::r1cs-constraint->a$inline, etc
                                                                      ;; todo: i had assoc here; should that be an error?
                                                                      mul
                                                                      neg
                                                                      add
                                                                      pfield::pos-fix)
                                                                    (w state))
                             monitor
                             memoizep
                             count-hitsp
                             ;; nil                             ;simplify-xorsp
                             print
                             whole-form
                             state)))

;; Expects the functions <BASE-NAME>-constraints and <BASE-NAME>-vars to
;; exist.  Creates a constant DAG named *<BASE-NAME>-holdsp*.
(defmacro lift-r1cs-new (&whole whole-form
                                name-of-defconst
                                ;; r1cs ;todo: currentlty can't make the r1cs (due to prime tests?)
                                vars
                                constraints
                                prime
                                &key
                                (extra-rules 'nil)
                                (remove-rules 'nil)
                                (rules 'nil)
                                (monitor 'nil)
                                (memoizep 'nil) ;; memoization can slow down R1CS lifting a lot, due to many terms with the same single nodenum (the valuation?) being put into the same memo slot
                                (count-hitsp 'nil)
                                (print 'nil))
  `(acl2::make-event-quiet (lift-r1cs-new-fn ',name-of-defconst
                                             ,vars
                                             ,constraints
                                             ,prime
                                             ,extra-rules
                                             ,remove-rules
                                             ,rules
                                             ,monitor
                                             ,memoizep
                                             ,count-hitsp
                                             ,print
                                             ',whole-form
                                             state)))
