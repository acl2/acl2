; Lifter for R1CSes (in sparse form)
;
; Copyright (C) 2019-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

;; NOTE: This tool is deprecated.  Use lift-r1cs instead.

;; This is for R1CSes in sparse form

(include-book "lift-r1cs-rules")
(include-book "lift-r1cs-rule-lists")
(include-book "../sparse/rule-lists")
(include-book "../sparse/rules-axe")
(include-book "../sparse/rules")
(include-book "lift-r1cs-common")
(include-book "kestrel/utilities/keywords-to-acl2-package" :dir :system)
(include-book "kestrel/axe/unroll-spec-basic" :dir :system) ; brings in skip-proofs
(include-book "kestrel/prime-fields/prime-fields-rules-axe" :dir :system)
(include-book "kestrel/prime-fields/bitp-idioms" :dir :system)
(include-book "kestrel/prime-fields/rules2" :dir :system)
(include-book "kestrel/utilities/ensure-rules-known" :dir :system)

(acl2::ensure-rules-known (lift-r1cs-rules))

;; Returns (mv erp event state).
(defun lift-r1cs-old-fn (base-name extra-rules remove-rules rules monitor memoizep count-hitsp produce-function function-type vars produce-theorem prime whole-form state)
  (declare (xargs :guard (and (symbolp base-name)
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              (symbol-listp rules)
                              (symbol-listp monitor)
                              (booleanp memoizep)
                              (booleanp count-hitsp)
                              (acl2::keyword-listp vars)
                              (booleanp produce-function)
                              (booleanp produce-theorem)
                              (natp prime) ;;(rtl::primep prime) ;todo, slow!
                              )
                  :mode :program
                  :stobjs state))
  (let ((constraints-fn-name (acl2::pack$ base-name '-constraints)))
    (acl2::unroll-spec-basic-fn (acl2::pack$ '* base-name '-holdsp*)
                                `(r1cs::r1cs-constraints-holdp (,constraints-fn-name)
                                                               ,(make-valuation-from-keyword-vars2 vars)
                                                               ;;todo: gen:
                                                               ',prime)
                                ;; The extra rules:
                                (if rules
                                    nil ;rules are given below, so extra-rules are not allowed
                                  (append (list constraints-fn-name)
                                          (lift-r1cs-rules)
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
                                produce-function
                                (if produce-function
                                    t ; disable-function
                                  nil)
                                function-type
                                (if produce-function
                                    (keywords-to-acl2-package vars) ;; function-params -- this provides the ordering
                                  ;; the default, since no function will be produced:
                                  :auto)
                                produce-theorem
                                nil ;print
                                whole-form
                                state)))

;; Expects the functions <BASE-NAME>-constraints and <BASE-NAME>-vars to
;; exist.  Creates a constant DAG named *<BASE-NAME>-holdsp*.
(defmacro lift-r1cs-old (&whole whole-form
                            base-name
                            &key
                            (extra-rules 'nil)
                            (remove-rules 'nil)
                            (rules 'nil)
                            (monitor 'nil)
                            (memoizep 'nil) ;; memoization can slow down R1CS lifting a lot, due to many terms with the same single nodenum (the valuation?) being put into the same memo slot
                            (count-hitsp 'nil)
                            (produce-function 't)
                            (produce-theorem 'nil)
                            (function-type ':auto)
                            (prime '21888242871839275222246405745257275088548364400416034343698204186575808495617) ;todo: think about this
                            )
  `(acl2::make-event-quiet (lift-r1cs-old-fn ',base-name
                                         ,extra-rules
                                         ,remove-rules
                                         ,rules
                                         ;; ,rule-alists
                                         ;; ,assumptions
                                         ,monitor
                                         ,memoizep
                                         ,count-hitsp
                                         ;; ,simplify-xorsp
                                         ,produce-function
                                         ,function-type
                                         ;; ,function-params
                                         (,(acl2::pack$ base-name '-vars))
                                         ,produce-theorem
                                         ;; ,print
                                         ,prime
                                         ',whole-form
                                         state)))
