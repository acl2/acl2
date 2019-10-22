; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pseudo-lambdap (x)
  :returns (yes/no booleanp)
  :parents (std/system/term-function-recognizers)
  :short
  (xdoc::topstring
   "Recognize pseudo-lambda-expressions,
    i.e. lambda expressions in "
   (xdoc::seetopic "pseudo-termp" "pseudo-terms")
   ".")
  :long
  (xdoc::topstring-p
   "This definition mirrors
    the relevant portion of the definition of @(tsee pseudo-termp).")
  (and (true-listp x)
       (= (len x) 3)
       (eq (first x) 'lambda)
       (symbol-listp (second x))
       (pseudo-termp (third x)))
  ///

  (defrule pseudo-lambdap-of-car-when-pseudo-termp
    (implies (and (pseudo-termp term)
                  (consp term)
                  (consp (car term)))
             (pseudo-lambdap (car term))))

  (defrule pseudo-termp-of-cons-when-pseudo-lambdap
    (implies (and (pseudo-lambdap lambd)
                  (pseudo-term-listp terms)
                  (equal (len terms) (len (lambda-formals lambd))))
             (pseudo-termp (cons lambd terms)))))
