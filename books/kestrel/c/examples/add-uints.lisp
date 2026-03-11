; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/c/syntax/input-files" :dir :system)
(include-book "kestrel/c/language/dynamic-semantics" :dir :system)
(include-book "kestrel/c/representation/integers" :dir :system)
(include-book "kestrel/c/proof-support/const-ast-accessors" :dir :system)
(include-book "kestrel/c/proof-support/exec-stmt-openers" :dir :system)
(include-book "kestrel/c/atc/symbolic-execution-rules/top" :dir :system)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file verifies the correctness of the function in the add_uints.c file.
; The function is proved to return an unsigned int that is
; the sum of the two argument unsigned ints,
; modulo one plus the maximum representable unsigned int.
; The proof is simple:
; we symbolically execute the function,
; and we show that it satisfies the above specification.
; We use the same rules that ATC uses to prove
; the correctness of the generated C code.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Read C code into ACL2 representation.
(c$::input-files :files '("add_uints.c")
                 :preprocess :internal
                 :const *add-uints*)

; Check that the C code is within the subset with formal semantics.
(assert-event
 (c$::transunit-ensemble-formalp
  (c$::code-ensemble->transunits *add-uints*)))

; Map the code to the form over which the formal semantics is defined.
(defconst *add-uints-formal*
  (b* (((mv & tunits)
        (c$::ldm-transunit-ensemble
         (c$::code-ensemble->transunits *add-uints*))))
    tunits))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Information about the C function

(make-event
 `(defruled lookup-of-f
    (equal (c::fun-env-lookup (c::ident "f")
                              (c::init-fun-env
                               (c::preprocess *add-uints-formal*)))
           ',(c::fun-env-lookup (c::ident "f")
                                (c::init-fun-env
                                 (c::preprocess *add-uints-formal*))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lemma to bridge the shallowly embedded representation of the code
; with the specification that we verify the code to satisfy.

(defruled spec-lemma
  (implies (and (c::uintp x)
                (c::uintp y))
           (equal (c::integer-from-uint (c::add-uint-uint x y))
                  (mod (+ (c::integer-from-uint x)
                          (c::integer-from-uint y))
                       (+ 1 (c::uint-max)))))
  :enable (c::add-uint-uint
           c::uint-from-integer-mod
           ifix
           c::uint-integer-fix
           c::uint-integerp-alt-def))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Correctness: the code satisfies the specification.

(defrule correctness

  (implies (and

            ;; Obtain function environment from ACL2 representation of the code.
            (equal fenv (c::init-fun-env (c::preprocess *add-uints-formal*)))

            ;; Name of the function of interest.
            (equal fun (c::ident "f"))

            ;; This is the initial computation state.
            (c::compustatep compst)

            ;; The parameters x and y are unsigned ints.
            (c::uintp x)
            (c::uintp y)

            ;; Execution limit that suffices for this C code
            ;; (for total correctness, vs. just partial correctness).
            (integerp limit)
            (>= limit 6) ; determined experimentally, but could be calculated

            ;; Execute C function, obtaining result and final computation state.
            (equal result+new-compst
                   (c::exec-fun fun (list x y) compst fenv limit))
            (equal result (mv-nth 0 result+new-compst))
            (equal new-compst (mv-nth 1 result+new-compst)))

           (and

            ;; Execution does not cause an error.
            (not (c::errorp result))

            ;; The function returns an unsigned int value,
            ;; which is the modular sum of x and y.
            result ; not NIL
            (c::uintp result)
            (equal (c::integer-from-uint result)
                   (mod (+ (c::integer-from-uint x)
                           (c::integer-from-uint y))
                        (1+ (c::uint-max))))

            ;; The final computation state is the same as the initial one.
            (equal new-compst compst)))

  :in-theory (union-theories
              ;; generic rules:
              (expand-ruleset '(c::const-ast-accessors
                                c::exec-stmt-openers)
                              world)
              '(c::exec-fun-open-return
                c::not-zp-of-limit-variable
                lookup-of-f
                (:e c::fun-info->params)
                c::init-scope-when-consp
                (:e c::param-declonp)
                c::valuep-when-uintp
                c::value-kind-when-uintp
                (:e c::param-declon-to-ident+tyname)
                c::tyname-to-type
                c::tyname-to-type-aux
                c::tyspecseq-to-type
                c::adjust-type-of-type-uint
                c::type-of-value-when-uintp
                c::value-listp-of-cons
                (:e c::value-listp)
                (:e c::init-scope)
                (:e c::scopep)
                (:e omap::assoc)
                c::remove-flexible-array-member-when-absent
                c::not-flexible-array-member-p-when-uintp
                c::value-fix-when-valuep
                c::scopep-of-update
                (:e c::identp)
                omap::assoc-of-update
                c::exec-block-item-list-when-consp
                (:e c::fun-info->body)
                c::not-zp-of-limit-minus-const
                c::exec-block-item-when-stmt
                c::exec-expr-when-pure
                (:e c::expr-purep)
                (:e c::expr-pure-limit)
                c::push-frame-of-one-nonempty-scope
                c::push-frame-of-one-empty-scope
                c::compustatep-of-add-var
                c::exec-expr-pure-when-strict-pure-binary
                (:e member-equal)
                c::exec-expr-pure-when-ident
                c::exec-ident-open
                c::read-var-of-add-var
                c::expr-valuep-of-expr-value
                c::ident-fix-when-identp
                c::exec-binary-strict-pure-when-add
                (:e c::binop-add)
                c::add-values-when-uint
                c::add-uint-and-value-when-uint
                c::uintp-of-add-uint-uint
                c::apconvert-expr-value-when-not-value-array
                c::expr-value->value-of-expr-value
                c::return-type-of-stmt-value-return
                c::stmt-value-return->value?-of-stmt-value-return
                c::value-option-fix-when-value-optionp
                c::value-optionp-when-valuep
                c::type-of-value-option-when-valuep
                (:e c::fun-info->result)
                c::pop-frame-of-add-var
                c::pop-frame-of-add-frame
                c::not-errorp-when-valuep
                (:t c::add-uint-uint)
                ;; specific to the example:
                spec-lemma))
  :rule-classes nil)
