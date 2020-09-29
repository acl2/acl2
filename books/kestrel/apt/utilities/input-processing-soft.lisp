; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/soft/core" :dir :system)
(include-book "kestrel/utilities/error-checking/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains input processors that depend on SOFT.
; These are in this separate file so that input-processing.lisp
; does not have to depend on SOFT too.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-input-old-soft-io-sel-mod (old verify-guards ctx state)
  :returns (mv erp
               (result "A @('(tuple (old symbolp)
                                    (?f symbolp)
                                    (x-x1...xn symbol-listp)
                                    (x-a1...am pseudo-term-listp)
                                    (y symbolp)
                                    (iorel pseudo-lambdap))').")
               state)
  :mode :program
  :parents (input-processors)
  :short "Process the @('old') input of an APT transformation,
          when that input must denote
          a SOFT shallow pop-refinement specification of a certain form."
  :long
  (xdoc::topstring
   (xdoc::p
    "The form that the specification must have is the one described in
     Section `Input/Output Relation with Selected Input and Modified Inputs'
     of @(see specification-forms).")
   (xdoc::p
    "We check that @('old') is either the name of an existing function or a "
    (xdoc::seetopic "acl2::numbered-names" "numbered name")
    " with a wildcard that resolves to the name of an existing function.
     Either way,
     the name of the existing function is returned as first result.")
   (xdoc::p
    "This input processor also takes as input
     the @(':verify-guards') input of the APT transformation.
     If this is @('t'),
     we ensure that the function denoted by @('old') is guard-verified.")
   (xdoc::p
    "We check that the function denoted by @('old') satisfies
     all the constraints described in
     the aforementioned section of @(see specification-forms).
     Note that the check that it is a SOFT quantifier function
     implies that the function is in logic mode
     (so we do not need to check for logic mode explicitly).")
   (xdoc::p
    "If all the checks are successful,
     we return, as second and subsequent results:
     the (only) function variable that the function depends on;
     the quantified variables,
     where the selected one @('x') may appear anywhere in the list
     (in fact, the exact @('x') is selected
     via some other input of the transformation);
     the arguments of the (only) call of the function variable,
     where the selected one @('x') may appear anywhere in the list
     (see parenthetical observation above);
     a fresh (ordinary) variable that replaces the call of the function variable
     in the lambda expression returned as the next result;
     and a lambda expression for the input/output relation.
     The fresh variable for the last formal parameter of the lambda expression
     is generated, and returned to the caller as noted above;
     we use the name of the function variable followed by `@('-call')',
     possibly augmented with disambiguating indices via @('genvar'),
     in the same package as the function variable.")
   (xdoc::p
    "In the first error message below,
     the @('old') input is referred to as `first input' of the transformation.
     It is normally the case that
     the first input of a transformation is the target function,
     but we may generalize this input processor at some point
     to take as additional input
     a description of the @('old') input to use in the error message.
     Other error messages below refer to `the target function ...' instead."))
  (b* ((wrld (w state))
       ((er old) (ensure-function-name-or-numbered-wildcard$
                  old "The first input" t nil))
       ((when (and (eq verify-guards t)
                   (not (guard-verified-p old wrld))))
        (er-soft+ ctx t nil
                  "Since the :VERIFY-GUARDS input is T, ~
                   the target function ~x0 must be guard-verified, ~
                   but it is not."
                  old))
       ((unless (soft::quant-sofunp old wrld))
        (er-soft+ ctx t nil
                  "The target function ~x0 ~
                   must be a SOFT quantifier function,
                   but it is not."
                  old))
       (funvars (soft::sofun-funvars old wrld))
       ((unless (= (len funvars) 1))
        (er-soft+ ctx t nil
                  "The target function ~x0 ~
                   must depend on exactly one function variable, ~
                   but instead it depends on ~x1."
                  old funvars))
       (??f (car funvars))
       ((when (consp (formals old wrld)))
        (er-soft+ ctx t nil
                  "The target function ~x0 ~
                   must have no parameters, but instead it has parameters ~x1."
                  old (formals old wrld)))
       ((unless (eq (defun-sk-quantifier old wrld) 'forall))
        (er-soft+ ctx t nil
                  "The quantifier of the target function ~x0 ~
                   must be universal, but it is existential instead."
                  old))
       (x-x1...xn (defun-sk-bound-vars old wrld))
       (matrix (defun-sk-matrix old wrld))
       (??f-calls (all-calls (list ?f) matrix nil nil))
       ((unless (= (len ?f-calls) 1))
        (er-soft+ ctx t nil
                  "The matrix ~x0 of the target function ~x1 ~
                   must have exactly one call of the function variable ~x2, ~
                   but it has ~x3 calls instead."
                  matrix old ?f (len ?f-calls)))
       (??f-call (car ?f-calls))
       (x-a1...am (fargs ?f-call))
       ((unless (consp x-a1...am))
        (er-soft+ ctx t nil
                  "The call ~x0 in the matrix ~x1 of ~x2 ~
                   must have at least one argument, ~
                   but it has none instead."
                  ?f-call matrix old))
       (y (genvar old (add-suffix ?f "-CALL") nil x-x1...xn))
       (iorel-body (subst-expr y ?f-call matrix))
       (iorel (make-lambda (append x-x1...xn (list y)) iorel-body)))
    (value (list old ?f x-x1...xn x-a1...am y iorel))))
