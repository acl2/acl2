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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define remove-unused-vars-from-lambda ((formals symbol-listp)
                                        (actuals pseudo-term-listp)
                                        (body-vars symbol-listp))
  :guard (= (len formals) (len actuals))
  :returns (mv (remaining-formals symbol-listp
                                  :hyp (symbol-listp formals))
               (remaining-actuals pseudo-term-listp
                                  :hyp (pseudo-term-listp actuals)))
  :parents (remove-unused-vars-from-term)
  :short "Remove from a lambda expression all the formal parameters,
          and corresponding actual parameters, that are not used in the body."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is an auxiliary function,
     which supports the main function @(tsee remove-unused-vars-from-term).")
   (xdoc::p
    "The inputs of this function are
     the formal parameters of the lambda expression,
     the actual parameters of the lambda expression,
     and the free variables of the body of the lambda expression.
     These inputs are calculated by @(tsee remove-unused-vars-from-term)
     when it encounters a lambda expression.")
   (xdoc::p
    "We go through the lists of formal and actual parameters,
     and drop any formal parameter, and corresponding actual parameter,
     that is not free in the body.
     The input @('body-vars') consists of the free variables of the body.
     Then we return the remaining formal and actual parameter lists."))
  (b* (((when (endp formals)) (mv nil nil))
       (formal (car formals))
       (actual (car actuals))
       ((unless (member-eq formal body-vars))
        (remove-unused-vars-from-lambda (cdr formals)
                                        (cdr actuals)
                                        body-vars))
       ((mv formals actuals) (remove-unused-vars-from-lambda (cdr formals)
                                                             (cdr actuals)
                                                             body-vars)))
    (mv (cons formal formals) (cons actual actuals)))
  ///

  (more-returns

   (remaining-formals
    (<= (acl2-count remaining-formals)
        (acl2-count formals))
    :name len-of-new-formals-of-remove-unused-vars-from-lambda
    :rule-classes :linear)

   (remaining-actuals
    (<= (acl2-count remaining-actuals)
        (acl2-count actuals))
    :hyp (= (len formals) (len actuals))
    :name len-of-new-actuals-of-remove-unused-vars-from-lambda
    :rule-classes :linear)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines remove-unused-vars-from-term
  :short "Remove all the lambda-bound variables that are not used."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through the term and, for each lambda expression we encounter,
     we use @(tsee remove-unused-vars-from-lambda) to remove
     all the formal parameters, and corresponding actual parameters,
     that are not free in the body of the lambda expression,
     i.e. that are not used.
     If all the formal parameters are unused,
     we replace the lambda expression with its body.")
   (xdoc::p
    "The new term is logically equivalent to the old term.
     If the actual parameters that have been removed have no side effects,
     executing the new term gives the same outcomes as executing the old term
     (except for perhaps doing so a little faster).")
   (xdoc::p
    "In order to prove termination,
     we add an @(tsee mbt) that establishes the hypothesis
     of the theorem about @(tsee remove-unused-vars-from-lambda)
     asserting that the new actual parameters are not more than the old ones."))
  :verify-guards nil

  (define remove-unused-vars-from-term ((term pseudo-termp))
    :returns (new-term "A @(tsee pseudo-termp).")
    (b* (((when (variablep term)) term)
         ((when (fquotep term)) term)
         (fn (ffn-symb term))
         ((when (symbolp fn))
          (fcons-term fn (remove-unused-vars-from-terms (fargs term))))
         (formals (lambda-formals fn))
         (body (lambda-body fn))
         (actuals (fargs term))
         (body-vars (all-vars body))
         ((unless (mbt (equal (len formals) (len actuals)))) nil)
         ((mv formals actuals) (remove-unused-vars-from-lambda formals
                                                               actuals
                                                               body-vars))
         ((when (eq formals nil)) (remove-unused-vars-from-term body))
         (actuals (remove-unused-vars-from-terms actuals))
         (body (remove-unused-vars-from-term body)))
      (fcons-term (make-lambda formals body) actuals)))

  (define remove-unused-vars-from-terms ((terms pseudo-term-listp))
    :returns (new-terms "A @(tsee pseudo-term-listp).")
    (cond ((endp terms) nil)
          (t (cons (remove-unused-vars-from-term (car terms))
                   (remove-unused-vars-from-terms (cdr terms)))))))
