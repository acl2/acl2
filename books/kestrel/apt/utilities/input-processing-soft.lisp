; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/error-checking/ensure-value-is-in-list" :dir :system)
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
                                    (iorel pseudo-lambdap)
                                    result)').")
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
     via some other input of the transformation:
     see @(tsee process-input-select-old-soft-io));
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
       (??f-call-string (concatenate 'string (symbol-name ?f) "-CALL"))
       (y (genvar old ?f-call-string nil x-x1...xn))
       (iorel-body (subst-expr y ?f-call matrix))
       (iorel (make-lambda (append x-x1...xn (list y)) iorel-body)))
    (value (list old ?f x-x1...xn x-a1...am y iorel))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define process-input-select-old-soft-io (select-input-value
                                          (select-input-keyword keywordp)
                                          (old symbolp)
                                          (?f symbolp)
                                          (x-x1...xn symbol-listp)
                                          (x-a1...am pseudo-term-listp)
                                          ctx
                                          state)
  :returns (mv erp
               (x symbolp
                  :hints (("Goal"
                           :in-theory
                           (enable acl2::ensure-value-is-in-list))))
               state)
  :short "Process the input of an APT transformation
          that selects an input of the function variable call in
          a SOFT shallow pop-refinement specification of a certain form."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is related to @(tsee process-input-old-soft-io-sel-mod),
     which checks that the target function of an APT transformation
     is a SOFT shallow pop-refinement specification
     of the form referenced in the documentation of that input processor.
     That documentation mentions that the selected input
     is specified via some other input of the transformation.
     This input processor serves to process that input.")
   (xdoc::p
    "Some of the arguments of this input processor
     are the homonymous results of @(tsee process-input-old-soft-io-sel-mod),
     some of which are just for error messages.
     There are two arguments about the transformation input to process:
     its value and its keyword (the latter is just for error messages).")
   (xdoc::p
    "If the input being processed is @(':auto'),
     which must be the default (this is assumed by an error messages below),
     then the call of the function variable must have a single argument,
     which must necessarily be a variable because of the checks
     performed by @(tsee process-input-select-old-soft-io);
     in this case, this is the argument selected by the input being processed.
     Otherwise, the input being processed must be a variable
     among the arguments of the call of the function variable."))
  (b* (((er x) (if (eq select-input-value :auto)
                   (if (= (len x-a1...am) 1)
                       (value (car x-a1...am))
                     (er-soft+ ctx t nil
                               "The ~x0 input is ~
                                (perhaps by default) :AUTO, ~
                                but this is allowed only if ~
                                the call of ~x1 in ~x2 ~
                                has exactly one argument, ~
                                but it has ~x3 arguments instead."
                               select-input-keyword ?f old (len x-a1...am)))
                 (b* (((er &) (ensure-value-is-in-list$
                               select-input-value
                               x-a1...am
                               (msg "one of the arguments ~x0 of ~
                                     the call of ~x1 in ~x2"
                                    x-a1...am ?f old)
                               (msg "The ~x0 input" select-input-keyword)
                               t
                               nil)))
                   (value select-input-value))))
       ((unless (symbolp x))
        (er-soft+ ctx t nil
                  "The argument ~x0 of the call of ~x1 in ~x2, ~
                   specified (perhaps by default) by the ~x3 input, ~
                   must be a variable, but it is not."
                  x ?f old select-input-keyword))
       ((unless (member-eq x x-x1...xn))
        (value (raise "Internal error: ~
                       the variable ~x0 in the call of ~x1 in ~x2 ~
                       is not among the bound variables ~x3."
                      x ?f old x-x1...xn)))
       (a1...am (remove1-eq x x-a1...am))
       ((when (member-eq x (all-vars (cons :dummy-fn a1...am))))
        (er-soft+ ctx t nil
                  "Aside from the argument ~x0 itself, ~
                   the other arguments ~x1 of the call of ~x2 ~
                   must not depend on ~x0, but they do."
                  x a1...am ?f)))
    (value x))
  :prepwork
  ((local (include-book "kestrel/std/system/all-vars" :dir :system))
   (local (include-book "std/typed-lists/pseudo-term-listp" :dir :system))))
