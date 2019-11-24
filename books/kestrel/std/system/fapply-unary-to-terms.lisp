; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "fapply-term")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fapply-unary-to-terms ((fn pseudo-termfnp)
                               (terms pseudo-term-listp))
  :guard (or (symbolp fn)
             (= 1 (len (lambda-formals fn))))
  :returns (applied-terms "A @(tsee pseudo-term-listp).")
  :parents (std/system/term-transformations)
  :short "Variant of @(tsee apply-unary-to-terms)
          that performs no simplification."
  :long
  (xdoc::topstring-p
   "The meaning of the starting @('f') in the name of this utility
    is analogous to @(tsee fcons-term) compared to @(tsee cons-term).")
  (fapply-unary-to-terms-aux fn terms nil)
  :verify-guards nil

  :prepwork
  ((define fapply-unary-to-terms-aux ((fn pseudo-termfnp)
                                      (terms pseudo-term-listp)
                                      (rev-result pseudo-term-listp))
     :guard (or (symbolp fn)
                (= 1 (len (lambda-formals fn))))
     :returns (final-result "A @(tsee pseudo-term-listp).")
     (cond ((endp terms) (reverse rev-result))
           (t (fapply-unary-to-terms-aux fn
                                         (cdr terms)
                                         (cons (fapply-term* fn (car terms))
                                               rev-result))))
     :verify-guards nil)))
