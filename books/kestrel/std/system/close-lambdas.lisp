; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defines" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (include-book "kestrel/std/system/all-vars" :dir :system))
(local (include-book "std/typed-lists/pseudo-term-listp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines close-lambdas
  :parents (std/system/term-transformations)
  :short "Make all the lambda expressions in a term closed."
  :long
  (xdoc::topstring
   (xdoc::p
    "ACL2 lambda expressions in translated terms are always closed,
     which means that they often include formal parameters
     that are replaced by themselves (i.e. by the same symbols)
     when the lambda expression is applied.
     For instance, the untranslated term @('(let ((x 0)) (+ x y))')
     is @('((lambda (x y) (binary-+ x y)) '3 y)') in translated form:
     the lambda expression includes the extra formal parameter @('y')
     which is not bound by the @(tsee let),
     applied to @('y') itself,
     making the lambda expression closed.")
   (xdoc::p
    "Terms with non-closed lambda expressions,
     e.g. produced by @(tsee remove-trivial-vars),
     still satisfy @(tsee pseudo-termp), but not @(tsee termp).
     The @('close-lambdas') utility
     closes any non-closed lambda expression in a term,
     so that it also satisfies @(tsee lambdap).
     It is essentially the inverse of @(tsee remove-trivial-vars).")
   (xdoc::@def "close-lambdas")
   (xdoc::@def "close-lambdas-lst"))

  (define close-lambdas ((term pseudo-termp))
    :returns (new-term pseudo-termp :hyp (pseudo-termp term))
    (b* (((when (variablep term)) term)
         ((when (fquotep term)) term)
         (fn (ffn-symb term))
         ((when (symbolp fn)) (fcons-term fn (close-lambdas-lst (fargs term))))
         (formals (lambda-formals fn))
         (body (lambda-body fn))
         (actuals (fargs term))
         (new-body (close-lambdas body))
         (extra-params (set-difference-eq (all-vars new-body) formals))
         (new-formals (append formals extra-params))
         (new-actuals (append (close-lambdas-lst actuals) extra-params)))
      (fcons-term (make-lambda new-formals new-body) new-actuals)))

  (define close-lambdas-lst ((terms pseudo-term-listp))
    :returns (new-terms (and (pseudo-term-listp new-terms)
                             (equal (len new-terms) (len terms)))
                        :hyp (pseudo-term-listp terms))
    (cond ((endp terms) nil)
          (t (cons (close-lambdas (car terms))
                   (close-lambdas-lst (cdr terms))))))

  :verify-guards nil ; done below
  ///
  (verify-guards close-lambdas))
