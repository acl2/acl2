; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../symbolic-computation-states")
(include-book "../shallow-embedding")

(include-book "types")
(include-book "values")
(include-book "type-of-value")
(include-book "test-value")
(include-book "exec-const")
(include-book "exec-ident")
(include-book "exec-unary")
(include-book "exec-binary-strict-pure")
(include-book "exec-cast")
(include-book "exec-arrsub")
(include-book "exec-expr-pure")
(include-book "exec-expr-when-call")
(include-book "exec-expr-when-asg")
(include-book "exec-expr")
(include-book "exec-fun")
(include-book "exec-stmt")
(include-book "exec-initer")
(include-book "exec-obj-declon")
(include-book "exec-block-item")
(include-book "init-scope")
(include-book "adjust-type")
(include-book "static-variable-pointers")
(include-book "identifiers")
(include-book "wrappers")
(include-book "if-distributivity")
(include-book "returns")
(include-book "executable-counterparts")
(include-book "limit")
(include-book "not-error")
(include-book "integer-operations")
(include-book "misc-rewrite")
(include-book "type-prescriptions")
(include-book "compound-recognizers")
(include-book "flexible-array-member")
(include-book "if-star")
(include-book "boolean-equality")
(include-book "hide")
(include-book "pointed-integers")
(include-book "sint-from-boolean")
(include-book "apconvert")
(include-book "object-designators")
(include-book "compustatep")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-symbolic-execution-rules
  :parents (atc-event-and-code-generation)
  :short "Symbolic execution rules for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently, the generated proofs of function correctness
     are carried out via symbolic execution of the C code.
     The C code is a constant value,
     because we are generating proofs over specific C functions;
     this makes symbolic execution possible.")
   (xdoc::p
    "In order to make these generated proofs more robust,
     we carry them out in a theory that consists exactly of
     (what we believe to be) all and only the needed rules.
     This file defines that theory.
     This set of rules has been defined by
     not only thinking of what is needed for symbolic execution,
     but also experimenting with several symbolic execution proofs,
     starting with the empty theory and adding rules
     as needed to advance the symbolic execution,
     and also by looking at the C dynamic semantics.
     There is no guarantee (meta proof) that
     these rules will suffice for every use of ATC;
     there is also no guarantee that
     the proof will not be defeated by some ACL2 heuristic in some cases.
     Nonetheless, the proof strategy seems sound and robust,
     and if a generated proof fails
     it should be possible to (prove and) use additional rules.")
   (xdoc::p
    "Some of the rules that are used in the symbolic execution
     rewrite calls of functions used in the deeply embedded dynamic semantics
     into their shallowly embedded counterparts,
     under hypothesis on the types of the arguments.
     For instance, @('(exec-unary op x compst)')
     is rewritten to @('(<op>-<type> x)')
     when @('op') is the unary operation corresponding to @('<op>')
     (unary plus, unary minus, bitwise complement, or logical complement),
     and @('x') has type @('<type>').
     These shallowly embedded counterparts are used
     in the ACL2 functions from which C code is represented:
     thus, the rewrite rules serve to turn (the execution of) the C code
     into the ACL2 terms from which the C code is generated,
     which is at the core of proving the correctness of the generated C code.")
   (xdoc::p
    "For recursive ACL2 functions that model C execution
     (e.g. @(tsee exec-expr-pure)),
     we introduce opener rules,
     which include @(tsee syntaxp) hypotheses requiring that
     the C abstract syntax being executed is a quoted constant.
     Some of these opener rules include binding hypotheses,
     which avoid symbolically executing the same pieces of C abstract syntax
     multiple times in some situations.")
   (xdoc::p
    "We collect the rules in lists,
     each of which serves a particular symbolic execution purpose.
     Certain rules may appear in multiple lists,
     when they serve multiple symbolic execution purposes.
     The current organization and subdivision of the rules in these lists
     is reasonable, but can (and will) certainly be improved"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-all-rules*
  :short "List of all the (generic) rules for the proofs generated by ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the ones used in all the generated proofs.
     In addition, each proof includes a few additional rules
     that depend on the specific C-representing ACL2 functions involved.
     See @(see atc-implementation)."))
  (append *atc-symbolic-computation-state-rules*
          *atc-tyname-to-type-rules*
          *atc-type-kind-rules*
          *atc-valuep-rules*
          *atc-value-listp-rules*
          *atc-value-optionp-rules*
          *atc-value-kind-rules*
          *atc-type-of-value-rules*
          *atc-type-of-value-option-rules*
          *atc-value-array->elemtype-rules*
          *atc-array-length-rules*
          *atc-array-length-write-rules*
          *atc-static-variable-pointer-rules*
          *atc-exec-ident-rules*
          *atc-exec-const-rules*
          *atc-exec-arrsub-rules*
          *atc-exec-unary-nonpointer-rules*
          *atc-exec-indir-rules*
          *atc-exec-cast-rules*
          *atc-exec-binary-strict-pure-rules*
          *atc-test-value-rules*
          *atc-exec-expr-pure-rules*
          *atc-exec-expr-pure-list-rules*
          *atc-exec-expr-when-call-rules*
          *atc-exec-expr-when-asg-rules*
          *atc-exec-expr-rules*
          *atc-exec-fun-rules*
          *atc-exec-stmt-rules*
          *atc-exec-initer-rules*
          *atc-init-value-to-value-rules*
          *atc-exec-obj-declon-rules*
          *atc-exec-block-item-rules*
          *atc-exec-block-item-list-rules*
          *atc-init-scope-rules*
          *atc-adjust-type-rules*
          *atc-other-executable-counterpart-rules*
          *atc-wrapper-rules*
          *atc-distributivity-over-if-rewrite-rules*
          *atc-identifier-rules*
          *atc-integer-const-rules*
          *atc-integer-size-rules*
          *atc-integer-ops-1-return-rewrite-rules*
          *atc-integer-ops-2-return-rewrite-rules*
          *atc-integer-convs-return-rewrite-rules*
          *atc-array-read-return-rewrite-rules*
          *atc-array-write-return-rewrite-rules*
          *atc-integer-ops-1-type-prescription-rules*
          *atc-integer-ops-2-type-prescription-rules*
          *atc-integer-convs-type-prescription-rules*
          *atc-array-read-type-prescription-rules*
          *atc-misc-rewrite-rules*
          *atc-type-prescription-rules*
          *atc-compound-recognizer-rules*
          *integer-value-disjoint-rules*
          *array-value-disjoint-rules*
          *atc-sint-from-boolean*
          *atc-boolean-from-sint*
          *atc-integer-ifix-rules*
          *atc-limit-rules*
          *atc-not-error-rules*
          *atc-value-result-fix-rules*
          *atc-lognot-sint-rules*
          *atc-boolean-from-integer-return-rules*
          *atc-integer-constructors-return-rules*
          *atc-computation-state-return-rules*
          *atc-value-fix-rules*
          *atc-flexible-array-member-rules*
          *atc-pointed-integer-rules*
          *atc-apconvert-rules*
          *atc-object-designator-rules*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We define a theory for the rules because experiments show that
; a long time is spent by ACL2 translating hints,
; given that *ATC-ALL-RULES* consists of thousands of rules.
; We use this theory in the generated proofs (see generation.lisp).

(deftheory atc-all-rules *atc-all-rules*)
