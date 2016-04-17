; Terms
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains utilities for manipulating ACL2 terms.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/top" :dir :system)

(local (set-default-parents term-manipulation))

(program)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc term-manipulation
  :parents (kestrel-system-utilities system-utilities)
  :short "Utilities to manipulate <see topic='@(url term)'>terms</see>.")

(std::deflist legal-variable-listp (x)
  (legal-variablep x)
  :short
  "True iff @('x') is a @('nil')-terminated list of legal variable names."
  :long
  "<p>
  See @('legal-variablep') in the ACL2 source code).
  </p>"
  :true-listp t
  :elementp-of-nil nil)

(define pseudo-lambda-expr-p (x)
  :returns (yes/no booleanp)
  :short
  "True iff @('x') satisfies the conditions of lambda expressions
  in <see topic='@(url pseudo-termp)'>pseudo-terms</see>."
  :long
  "<p>
  @('x') must be a @('nil')-terminated list of exactly three elements,
  whose first element is the symbol @('lambda'),
  whose second element is a list of symbols,
  and whose third element is a pseudo-term.
  </p>"
  (and (true-listp x)
       (eql (len x) 3)
       (eq (first x) 'lambda)
       (symbol-listp (second x))
       (pseudo-termp (third x))))

(define lambda-expr-closedp ((lambd pseudo-lambda-expr-p))
  :returns (yes/no booleanp)
  :short
  "True iff the lambda expression is closed, i.e. it has no free variables."
  (subsetp (all-vars (lambda-body lambd))
           (lambda-formals lambd)))

(define pseudo-functionp (x)
  :returns (yes/no booleanp)
  :short
  "True iff @('x') satisfies the conditions of functions
  in <see topic='@(url pseudo-termp)'>pseudo-terms</see>."
  :long
  "<p>
  @('x') must be a symbol or a pseudo-lambda-expression.
  These are the possible values of the first element of
  a pseudo-term that is not a variable or a quoted constant
  (i.e. a pseudo-term that is a function application).
  </p>"
  (or (symbolp x)
      (pseudo-lambda-expr-p x)))

(define apply-term ((pfun pseudo-functionp) (terms pseudo-term-listp))
  :guard (or (symbolp pfun)
             (eql (len terms)
                  (len (lambda-formals pfun))))
  :returns (term pseudo-termp)
  :short
  "Apply pseudo-function to list of pseudo-terms, obtaining a pseudo-term."
  :long
  "<p>
  If the pseudo-function is a lambda expression,
  a beta reduction is performed.
  </p>"
  (cond ((symbolp pfun) (cons-term pfun terms))
        (t (subcor-var (lambda-formals pfun) terms (lambda-body pfun)))))

(defsection apply-term*
  :short
  "Apply pseudo-function to pseudo-terms, obtaining a pseudo-term."
  :long
  "<p>
  If the pseudo-function is a lambda expression,
  a beta reduction is performed.
  </p>
  @(defs apply-term*)"
  (defmacro apply-term* (pfun &rest terms)
    `(apply-term ,pfun (list ,@terms))))
