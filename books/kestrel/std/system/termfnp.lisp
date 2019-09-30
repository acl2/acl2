; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "lambdap")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define termfnp (x (wrld plist-worldp-with-formals))
  :returns (yes/no booleanp)
  :parents (std/system/term-function-recognizers)
  :short
  (xdoc::topstring
   "Recognize valid "
   (xdoc::seetopic "term" "translated")
   " term functions,
    i.e. functions in valid translated terms.")
  (or (and (symbolp x)
           (function-symbolp x wrld))
      (lambdap x wrld))
  ///

  (defrule termfnp-when-termp
    (implies (and (termp term wrld)
                  (consp term)
                  (consp (car term)))
             (termfnp (car term) wrld)))

  (defrule termp-when-termfnp
    (implies (and (termfnp fn wrld)
                  (term-listp terms wrld)
                  (equal (len terms) (arity fn wrld))
                  (not (eq fn 'quote)))
             (termp (cons fn terms) wrld))
    :enable (arity lambdap)))
