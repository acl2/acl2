; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "pseudo-termfnp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define apply-term ((fn pseudo-termfnp) (terms pseudo-term-listp))
  :guard (or (symbolp fn)
             (= (len terms)
                (len (lambda-formals fn))))
  :returns (term "A @(tsee pseudo-termp).")
  :parents (std/system/term-transformations)
  :short "Apply a function symbol or a lambda expression to a list of terms,
          obtaining a term."
  :long
  (xdoc::topstring-p
   "This utility is similar to @(tsee cons-term),
    but it performs a beta reduction when @('fn') is a lambda expression.")
  (cond ((symbolp fn) (cons-term fn terms))
        (t (subcor-var (lambda-formals fn) terms (lambda-body fn))))
  :guard-hints (("Goal" :in-theory (enable pseudo-termfnp pseudo-lambdap))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection apply-term*
  :parents (term-utilities)
  :short "Apply a function symbol or a lambda expression to zero or more terms,
          obtaining a term."
  :long
  (xdoc::topstring
   (xdoc::p
    "This utility is similar to @(tsee cons-term*),
     but it performs a beta reduction when @('fn') is a lambda expressions.
     It is a macro version of @(tsee apply-term).")
   (xdoc::@def "apply-term*"))
  (defmacro apply-term* (fn &rest terms)
    `(apply-term ,fn (list ,@terms))))
