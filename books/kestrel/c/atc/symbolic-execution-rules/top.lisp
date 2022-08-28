; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "proof-support")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-symbolic-execution-rules
  :parents (atc-execution)
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
     For instance, @('(exec-unary op x)')
     is rewritten to @('(<op>-<type> x)')
     when @('op') is @('<op>')
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
