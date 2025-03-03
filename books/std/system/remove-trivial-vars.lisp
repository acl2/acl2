; Standard System Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defines" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define remove-equal-formals-actuals ((formals symbol-listp)
                                      (actuals pseudo-term-listp))
  :guard (= (len formals) (len actuals))
  :returns (mv (new-formals symbol-listp :hyp (symbol-listp formals))
               (new-actuals pseudo-term-listp :hyp (pseudo-term-listp actuals)))
  :parents (remove-trivial-vars)
  :short "Remove equal formals and actuals
          from two lists of the same length."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee remove-trivial-vars),
     but it may be more generally useful.
     In fact, it could be generalized to an operation on lists."))
  (b* (((when (endp formals)) (mv nil nil))
       ((unless (mbt (consp actuals))) (mv nil nil))
       (formal (car formals))
       (actual (car actuals))
       ((when (eq formal actual))
        (remove-equal-formals-actuals (cdr formals) (cdr actuals)))
       ((mv rest-formals rest-actuals)
        (remove-equal-formals-actuals (cdr formals) (cdr actuals))))
    (mv (cons formal rest-formals)
        (cons actual rest-actuals)))
  ///

  (defthmd remove-equal-formals-actuals-same-len
    (equal (len (mv-nth 0 (remove-equal-formals-actuals formals actuals)))
           (len (mv-nth 1 (remove-equal-formals-actuals formals actuals)))))

  (more-returns
   (new-formals true-listp :rule-classes :type-prescription))

  (more-returns
   (new-actuals true-listp :rule-classes :type-prescription))

  (defret acl2-count-of-remove-equal-formals-actuals.formals
    (<= (acl2-count new-formals)
        (acl2-count formals))
    :rule-classes :linear)

  (defret acl2-count-of-remove-equal-formals-actuals.actuals
    (<= (acl2-count new-actuals)
        (acl2-count actuals))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines remove-trivial-vars
  :parents (std/system/term-transformations)
  :short "Remove the trivial lambda-bound variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "ACL2 lambda expressions in translated terms are always closed,
     which means that they often include formal parameters
     that are replaced by themselves (i.e. by the same symbols)
     when the lambda expression is applied.
     For instance, the untranslated term @('(let ((x 3)) (+ x y))')
     is @('((lambda (x y) (binary-+ x y)) '3 y)') in translated form:
     the lambda expression includes the extra formal parameter @('y')
     which is not bound by the @(tsee let),
     applied to @('y') itself,
     making the lambda expression closed.")
   (xdoc::p
    "This function removes the formal parameters of lambda expressions
     that are ``trivial'' in the sense that
     they are replaced by identical actual parameters.
     These are ``artificial'' variables,
     not @(tsee let) variables.
     We also remove the corresponding actual parameters, of course,
     so that beta reduction still makes sense,
     and the number of actual parameters still matches
     the number of formal parameters.
     Applying this function to the example above yields
     @('((lambda (x) (binary-+ x y)) '3)').")
   (xdoc::p
    "If all the formal parameters are trivial,
     we replace the lambda expression with its body.
     A lambda expression with all trivial formal parameters
     may not result from hand-written code,
     but could result from generated code.")
   (xdoc::p
    "We obtain terms whose lambda expressions may not be closed.
     These do not satisfy @(tsee termp),
     but they still satisfy @(tsee pseudo-termp).
     Furthermore, it is easy to close any open lambda expressions,
     by adding formal parameters, and corresponding actual parameters,
     for the free variables in the lambda expression.")
   (xdoc::p
    "For certain term transformations,
     it may be more convenient to work
     with the possibly open lamba expressions produced by this function.
     This way, every lambda expression corresponds to a @(tsee let)
     without any trivial bindings.
     In other languages,
     @(tsee let) expressions are normally not closed."))

  (define remove-trivial-vars ((term pseudo-termp))
    :returns (new-term pseudo-termp :hyp (pseudo-termp term))
    (b* (((when (variablep term)) term)
         ((when (fquotep term)) term)
         (fn (ffn-symb term))
         ((when (symbolp fn))
          (fcons-term fn (remove-trivial-vars-lst (fargs term))))
         (formals (lambda-formals fn))
         (body (lambda-body fn))
         (actuals (fargs term))
         ((unless (mbt (equal (len formals)
                              (len actuals)))) nil) ; for termination
         ((mv nontrivial-formals nontrivial-actuals)
          (remove-equal-formals-actuals formals actuals))
         ((when (eq nontrivial-formals nil)) (remove-trivial-vars body)))
      (fcons-term (make-lambda nontrivial-formals
                               (remove-trivial-vars body))
                  (remove-trivial-vars-lst nontrivial-actuals))))

  (define remove-trivial-vars-lst ((terms pseudo-term-listp))
    :returns (new-terms (and (pseudo-term-listp new-terms)
                             (equal (len new-terms) (len terms)))
                        :hyp (pseudo-term-listp terms))
    (b* (((when (endp terms)) nil)
         ((cons term terms) terms)
         (new-term (remove-trivial-vars term))
         (new-terms (remove-trivial-vars-lst terms)))
      (cons new-term new-terms)))

  :guard-hints (("Goal" :expand ((pseudo-termp term))))

  :returns-hints
  (("Goal" :in-theory (enable remove-equal-formals-actuals-same-len))))
