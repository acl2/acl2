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

(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines all-free/bound-vars
  :parents (std/system/term-queries)
  :short "Return all the free and bound variables that occur in a term."
  :long
  (xdoc::topstring
   (xdoc::p
    "The returned list of variables is in no particular order,
     but it has no duplicates,
     because we use @(tsee union-eq) to join variable lists.")
   (xdoc::p
    "This utility is in contrast with the built-in @(tsee all-vars),
     which returns only the free variables.")
   (xdoc::@def "all-free/bound-vars")
   (xdoc::@def "all-free/bound-vars-lst"))

  (define all-free/bound-vars ((term pseudo-termp))
    :returns (vars symbol-listp :hyp :guard)
    (cond ((variablep term) (list term))
          ((fquotep term) nil)
          (t (b* ((fn/lambda (ffn-symb term))
                  (fn/lambda-vars (and (flambdap fn/lambda)
                                       (union-eq (lambda-formals fn/lambda)
                                                 (all-free/bound-vars
                                                  (lambda-body fn/lambda)))))
                  (args-vars (all-free/bound-vars-lst (fargs term))))
               (union-eq fn/lambda-vars args-vars)))))

  (define all-free/bound-vars-lst ((terms pseudo-term-listp))
    :returns (vars symbol-listp :hyp :guard)
    (cond ((endp terms) nil)
          (t (union-eq (all-free/bound-vars (car terms))
                       (all-free/bound-vars-lst (cdr terms))))))

  :verify-guards nil ; done below
  ///
  (verify-guards all-free/bound-vars))
