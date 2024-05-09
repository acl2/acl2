; An Axe Prover for R1CS reasoning
;
; Copyright (C) 2020-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/axe/make-prover-simple" :dir :system)
(include-book "axe-evaluator-r1cs")
(include-book "axe-syntaxp-evaluator-r1cs")
;; At least for now, the basic version of this is fine:
(include-book "kestrel/axe/axe-bind-free-evaluator-basic" :dir :system)
(include-book "axe-rules-r1cs")

(defun r1cs-prover-default-global-rules ()
  (declare (xargs :guard t))
  '(;; fep rules:
    pfield::fep-of-add
    pfield::fep-of-mul
    pfield::fep-of-neg
    pfield::fep-of-bitxor
    pfield::fep-of-bvcat
    pfield::fep-of-bvxor
    pfield::fep-of-bvchop
    pfield::fep-of-mod ;todo: more fep rules?
    ;; integerp rules:
    acl2::integerp-of-bvcat
    acl2::integerp-of-bitxor
    acl2::integerp-of-bvxor
    acl2::integerp-of-bvnot
    pfield::integerp-of-add
    pfield::integerp-of-mul
    pfield::integerp-of-neg
    ;; bitp rules:
    acl2::bitp-of-bitxor
    acl2::bitp-of-bitand
    acl2::bitp-of-bitnot
    acl2::bitp-of-getbit
    ;; booleanp rules:
    (acl2::booleanp-rules) ; some may not be needed
    ;; fe-listp stuff:
    pfield::booleanp-of-fe-listp
    pfield::fep-when-fe-listp-and-memberp
    acl2::memberp-of-append-with-key-first-half-axe
    acl2::memberp-of-append-with-key-second-half-axe
    acl2::memberp-of-cons ;todo: make a faster version for axe
    ;; basic rules:
    acl2::equal-same
    acl2::ifix-when-integerp
    ;; prime field rules:
    pfield::add-of-0-arg1
    pfield::add-of-0-arg2
    pfield::neg-of-0
    pfield::mul-of-0-arg1
    pfield::mul-of-0-arg2
    ;; rules to remove mod (todo: perhaps avoid introducing it):
    pfield::neg-of-mod
    pfield::add-of-mod-arg1
    pfield::add-of-mod-arg2
    pfield::mul-of-mod-arg1
    pfield::mul-of-mod-arg1
    ))

(make-prover-simple r1cs
                    r1cs
                    r1cs
                    basic
                    :default-global-rules (r1cs-prover-default-global-rules))
