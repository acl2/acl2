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

(define fapply-term ((fn pseudo-termfnp) (terms pseudo-term-listp))
  :guard (or (symbolp fn)
             (= (len terms)
                (len (lambda-formals fn))))
  :returns (term "A @(tsee pseudo-termp).")
  :parents (std/system/term-transformations)
  :short "Variant of @(tsee apply-term) that performs no simplification."
  :long
  (xdoc::topstring-p
   "The meaning of the starting @('f') in the name of this utility
    is analogous to @(tsee fcons-term) compared to @(tsee cons-term).")
  (cond ((symbolp fn) (fcons-term fn terms))
        (t (fsubcor-var (lambda-formals fn) terms (lambda-body fn))))
  :guard-hints (("Goal" :in-theory (enable pseudo-termfnp pseudo-lambdap))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection fapply-term*
  :parents (term-utilities)
  :short "Variant of @(tsee apply-term*) that performs no simplification."
  :long
  (xdoc::topstring
   (xdoc::p
    "The meaning of the starting @('f') in the name of this utility
     is analogous to @(tsee fcons-term) compared to @(tsee cons-term).")
   (xdoc::@def "fapply-term*"))
  (defmacro fapply-term* (fn &rest terms)
    `(fapply-term ,fn (list ,@terms))))
