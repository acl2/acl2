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

(defines dumb-occur-var-open
  :parents (std/system/term-queries)
  :short "Check if a variable occurs free in a term
          that may contain non-closed (i.e. open) lambda expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "When trivial lambda-bound variables are removed from a term
     via @(tsee remove-trivial-vars),
     some lambda expressions may not be closed.
     For checking whether a variable occurs free in this kind of terms,
     the system utility @(tsee dumb-occur-var) is inadequate,
     because it skips over lambda expressions, assuming they are closed,
     as is the case in ACL2's internal translated form.")
   (xdoc::p
    "Thus, we define a utility similar to @(tsee dumb-occur-var)
     that does not just skip over lambda expressions.
     Instead, it skips over lambda expressions only if
     the variable is among the formal parameters of the lambda expression,
     because in that case the variable is bound in the lambda expression.
     Otherwise, it examines the body of the lambda expression.
     This is the standard treatment of lambda expressions
     in languages where lambda expressions are not necessarily closed.")
   (xdoc::@def "dumb-occur-var-open")
   (xdoc::@def "dumb-occur-var-open-lst"))

  (define dumb-occur-var-open ((var symbolp) (term pseudo-termp))
    :returns (yes/no booleanp)
    (b* (((when (eq var term)) t)
         ((when (variablep term)) nil)
         ((when (fquotep term)) nil)
         (fn (ffn-symb term)))
      (or (dumb-occur-var-open-lst var (fargs term))
          (and (flambdap fn)
               (not (member-eq var (lambda-formals fn)))
               (dumb-occur-var-open var (lambda-body fn))))))

  (define dumb-occur-var-open-lst ((var symbolp) (terms pseudo-term-listp))
    :returns (yes/no booleanp)
    (cond ((endp terms) nil)
          (t (or (dumb-occur-var-open var (car terms))
                 (dumb-occur-var-open-lst var (cdr terms)))))))
