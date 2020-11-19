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

(include-book "rules")
(include-book "../sparse/rule-lists")
(include-book "proof-support-rules")
(include-book "filter-and-combine-symbol-alists")
(include-book "kestrel/utilities/keywords-to-acl2-package" :dir :system)
(include-book "kestrel/axe/unroll-spec-basic" :dir :system)
(include-book "kestrel/prime-fields/prime-fields-rules-axe" :dir :system)
(include-book "kestrel/utilities/ensure-rules-known" :dir :system)

;; try this rule last since it has a free var (do we really need it at all?):
(table acl2::axe-rule-priorities-table 'pfield::integerp-when-fep 10)

(defun more-r1cs-proof-rules ()
  (declare (xargs :guard t))
  '(acl2::mod-of-1-arg1
    acl2::rationalp-of-mod
    acl2::rationalp-when-integerp
    acl2::mod-of-mod-same-arg2
    acl2::integerp-of-mod
    posp
    ;; ifix ;drop?
    acl2::integerp-of-ifix

    pfield::mul-of-1-arg1-gen
    pfield::add-of-0-arg1-gen
    pfield::add-of-0-arg2-gen
    pfield::add-of-mod-arg1
    pfield::add-of-mod-arg2
    pfield::rationalp-of-mul
    pfield::mul-of-mod-arg1
    pfield::mul-of-mod-arg2
    pfield::mod-of-mul
    pfield::mul-becomes-neg
    pfield::integerp-of-neg
    pfield::mod-of-neg
    pfield::neg-of-0
    pfield::equal-of-neg-arg2
    pfield::equal-of-add-of-neg-arg2
    ;;fep-of-lookup-equal ;fixme
    ;;integerp-of-lookup-equal ;fixme
    pfield::fep-of-mul
    pfield::fep-of-neg
    pfield::neg-of-mul-of-neg-arg1
    pfield::neg-of-mul-of-neg-arg2
    pfield::neg-of-mul-of-add-of-neg-arg1-arg2
    pfield::neg-of-mul-of-add-of-add-of-neg-arg1-arg2-arg2
    pfield::neg-of-mul-of-add-of-neg-arg2-arg2
    pfield::integerp-of-add
    pfield::neg-when-constant-arg1
    pfield::pos-fix-when-posp
    pfield::mod-of-neg
    pfield::mod-when-fep
    pfield::fep-of-add
    pfield::fep-of-mul
    pfield::mul-of-ifix-arg1
    pfield::mul-of-ifix-arg2
    pfield::add-of-ifix-arg1
    pfield::add-of-ifix-arg2
    acl2::equal-same

    pfield::fep-of-ifix
    pfield::ifix-when-fep
    ))

(defun lift-r1cs-rules ()
  (declare (xargs :guard t))
  (append '(acl2::lookup-equal-of-filter-and-combine-symbol-alists-safe
            pfield::neg-of-neg
            pfield::equal-of-add-of-add-of-neg-arg2-arg2
            bitp-idiom-1
            bitp-idiom-2
            bitp-idiom-with-constant-1
            bitp-idiom-with-constant-2
            mul-normalize-constant-arg1
            add-of-constant-normalize-to-fep ;todo: normalize to small pos or eg numbers instead
            pfield::mul-of--1-becomes-neg-gen ;todo: be consistent about negative constants
            ;primes::primep-of-bn-254-group-prime-constant
            ;;bitp-of-add-of-constant-negated-special ;;caused problems, possibly a loop, after adding fns to the evaluator.  TODO: why?
            pfield::neg-of-add
            pfield::neg-of-mul-when-constant
            xor-idiom-3
            xor-idiom-3-alt
            acl2::lookup-equal-of-acons)
          (more-r1cs-proof-rules) ;todo
          (r1cs-proof-rules)))

(acl2::ensure-rules-known (lift-r1cs-rules))

;; Returns (mv erp event state).
(defun lift-r1cs-fn (base-name extra-rules remove-rules rules monitor memoizep count-hitsp produce-function function-type vars produce-theorem whole-form state)
  (declare (xargs :guard (and (symbolp base-name)
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              (symbol-listp rules)
                              (symbol-listp monitor)
                              (booleanp memoizep)
                              (booleanp count-hitsp)
                              (acl2::keyword-listp vars)
                              (booleanp produce-function)
                              (booleanp produce-theorem))
                  :mode :program
                  :stobjs state))
  (let ((constraints-fn-name (acl2::pack$ base-name '-constraints)))
    (acl2::unroll-spec-basic-fn (acl2::pack$ '* base-name '-holdsp*)
                                `(r1cs::r1cs-constraints-holdp (,constraints-fn-name)
                                                               ,(acl2::make-valuation-from-keyword-vars2 vars)
                                                               ;;todo: gen:
                                                               21888242871839275222246405745257275088548364400416034343698204186575808495617)
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
                                (make-fep-assumptions-from-keyword-vars vars 21888242871839275222246405745257275088548364400416034343698204186575808495617)
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
                                  ;; the defautl, since no function will be produced:
                                  :auto)
                                produce-theorem
                                nil ;print
                                whole-form
                                state)))

(defmacro lift-r1cs (&whole whole-form
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
                            (function-type ':auto))
  `(acl2::make-event-quiet (lift-r1cs-fn ',base-name
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
                                         ',whole-form
                                         state)))
