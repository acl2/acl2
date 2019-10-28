; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "pseudo-lambdap")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pseudo-termfnp (x)
  :returns (yes/no booleanp)
  :parents (std/system/term-function-recognizers)
  :short
  (xdoc::topstring
   "Recognize pseudo-term-functions,
    i.e. functions in "
   (xdoc::seetopic "pseudo-termp" "pseudo-terms")
   ".")
  (or (symbolp x)
      (pseudo-lambdap x))
  ///

  (defrule pseudo-termfnp-when-symbolp
    (implies (symbolp x)
             (pseudo-termfnp x)))

  (defrule pseudo-termfnp-when-pseudo-lambdap
    (implies (pseudo-lambdap x)
             (pseudo-termfnp x)))

  (defrule pseudo-termfnp-of-car-when-pseudo-termp
    (implies (and (pseudo-termp term)
                  (consp term))
             (pseudo-termfnp (car term)))
    :enable pseudo-lambdap)

  (defrule pseudo-termp-of-cons-when-pseudo-termfnp
    (implies (and (pseudo-termfnp fn)
                  (pseudo-term-listp terms)
                  (or (atom fn)
                      (equal (len terms) (len (lambda-formals fn))))
                  (not (eq fn 'quote)))
             (pseudo-termp (cons fn terms)))
    :enable pseudo-lambdap))
