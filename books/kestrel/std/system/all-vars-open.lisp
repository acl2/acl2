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

(defines all-vars-open
  :parents (std/system/term-queries)
  :short "Free variables in a term
          that may contain non-closed (i.e. open) lambda expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "When trivial lambda-bound variables are removed from a term
     via @(tsee remove-trivial-vars),
     some lambda expressions may not be closed.
     For collecting the free variables of this kind of terms,
     the system utility @(tsee all-vars) is inadequate,
     because it skips over lambda expressions, assuming they are closed,
     as is the case in ACL2's internal translated form.")
   (xdoc::p
    "Thus, we define a utility similar to @(tsee all-vars)
     that does not skip over lambda expressions.
     Instead, it collects the free variables of the body of a lambda expression,
     removes the formal parameters of the lambda expressions,
     and regards the remaining variables
     as the free ones of the lambda expression.
     This is the standard treatment of lambda expressions
     in languages where lambda expressions are not necessarily closed.")
   (xdoc::p
    "The returned list of variables has no duplicates.
     The list is in no particular order.")
   (xdoc::@def "all-vars-open")
   (xdoc::@def "all-vars-open-lst"))

  (define all-vars-open ((term pseudo-termp))
    :returns (vars symbol-listp :hyp :guard)
    (b* (((when (variablep term)) (list term))
         ((when (fquotep term)) nil)
         (fn (ffn-symb term))
         (fn-vars (if (symbolp fn)
                      nil
                    (set-difference-eq (all-vars-open (lambda-body fn))
                                       (lambda-formals fn))))
         (args-vars (all-vars-open-lst (fargs term))))
      (union-eq fn-vars args-vars)))

  (define all-vars-open-lst ((terms pseudo-term-listp))
    :returns (vars symbol-listp :hyp :guard)
    (cond ((endp terms) nil)
          (t (union-eq (all-vars-open (car terms))
                       (all-vars-open-lst (cdr terms))))))

  :verify-guards nil ; done below

  ///

  (std::defret-mutual all-vars-open
    (defret true-listp-of-all-vars-open
      (true-listp vars)
      :rule-classes :type-prescription
      :fn all-vars-open)
    (defret true-listp-of-all-vars-open-lst
      (true-listp vars)
      :rule-classes :type-prescription
      :fn all-vars-open-lst))

  (verify-guards all-vars-open))
