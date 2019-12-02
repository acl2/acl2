; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "apply-term")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define apply-unary-to-terms ((fn pseudo-termfnp) (terms pseudo-term-listp))
  :guard (or (symbolp fn)
             (= 1 (len (lambda-formals fn))))
  :returns (applied-terms "A @(tsee pseudo-term-listp).")
  :parents (std/system/term-transformations)
  :short "Apply a function symbol or a unary lambda expression
          to each element of a list of terms,
          obtaining a list of corresponding terms."
  (apply-unary-to-terms-aux fn terms nil)
  :verify-guards nil

  :prepwork
  ((define apply-unary-to-terms-aux ((fn pseudo-termfnp)
                                     (terms pseudo-term-listp)
                                     (rev-result pseudo-term-listp))
     :guard (or (symbolp fn)
                (= 1 (len (lambda-formals fn))))
     :returns (final-result "A @(tsee pseudo-term-listp).")
     (cond ((endp terms) (reverse rev-result))
           (t (apply-unary-to-terms-aux fn
                                        (cdr terms)
                                        (cons (apply-term* fn (car terms))
                                              rev-result))))
     :verify-guards nil)))
