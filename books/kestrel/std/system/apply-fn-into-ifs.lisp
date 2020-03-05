; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "apply-term")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define apply-fn-into-ifs ((fn pseudo-termfnp) (term pseudo-termp))
  :guard (or (symbolp fn)
             (= (len (lambda-formals fn)) 1))
  :returns (new-term "A @(tsee pseudo-termp).")
  :verify-guards nil
  :parents (std/system/term-transformations)
  :short "Apply a function symbol or lambda expression to the term,
          pushing the function into the @(tsee if) branches."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is not an @(tsee if), the function is applied to the term.
     Otherwise, the function is applied to the `then' and `else' branches,
     and recursively to their `then' and `else' branches
     if those are @(tsee if)s as well.
     For instance, applying a symbol @('f') to @('(if a (if b c d) e)')
     results in @('(if a (if b (f c) (f d)) (f e))')."))
  (b* (((when (variablep term)) (apply-term* fn term))
       ((when (fquotep term)) (apply-term* fn term))
       ((unless (eq (ffn-symb term) 'if)) (apply-term* fn term))
       ((unless (= (len (fargs term)) 3))
        (raise "Internal error: ~
                the IF term ~x0 does not have 3 arguments."
               term)))
    (cons-term 'if (list (fargn term 1)
                         (apply-fn-into-ifs fn (fargn term 2))
                         (apply-fn-into-ifs fn (fargn term 3))))))
