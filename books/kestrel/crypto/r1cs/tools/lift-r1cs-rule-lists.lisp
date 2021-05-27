; Rule lists for lifting R1CSes
;
; Copyright (C) 2019-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "../sparse/rule-lists")

;; try this rule last since it has a free var (do we really need it at all?):
(table acl2::axe-rule-priorities-table 'pfield::integerp-when-fep 10)

(defun more-prime-fields-rules ()
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
    acl2::pos-fix-when-posp
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

;; TODO: Consider removing PFIELD::ADD-COMMUTATIVE-AXE and PFIELD::ADD-COMMUTATIVE-2-AXE from this
(defun lift-r1cs-rules ()
  (declare (xargs :guard t))
  (append '(acl2::lookup-equal-of-filter-and-combine-symbol-alists-safe
            pfield::neg-of-neg
            pfield::equal-of-add-of-add-of-neg-arg2-arg2
            mul-normalize-constant-arg1
            add-of-constant-normalize-to-fep ;todo: normalize to small pos or neg numbers instead?
            pfield::mul-of--1-becomes-neg-gen ;todo: be consistent about negative constants
            ;;primes::primep-of-bn-254-group-prime-constant
            ;;bitp-of-add-of-constant-negated-special ;;caused problems, possibly a loop, after adding fns to the evaluator.  TODO: why?
            pfield::neg-of-add
            pfield::neg-of-mul-when-constant
            pfield::xor-idiom-3
            pfield::xor-idiom-3-alt
            acl2::lookup-equal-of-acons
            pfield::integerp-when-fep ;todo: maybe drop, if we use the efficient plan for fep assumptions (fe-listp of a balanced append nest)
            )
          (pfield::bitp-idiom-rules)
          (pfield::prime-field-proof-rules)
          (more-prime-fields-rules) ;todo
          (r1cs-rules)))
