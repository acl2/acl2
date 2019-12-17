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

(local (include-book "kestrel/std/system/all-vars" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lambdap (x (wrld plist-worldp-with-formals))
  :returns (yes/no booleanp)
  :parents (std/system/term-function-recognizers)
  :short
  (xdoc::topstring
   "Recognize valid "
   (xdoc::seetopic "term" "translated")
   " lambda expression,
    i.e. lambda expressions in valid translated terms.")
  :long
  (xdoc::topstring-p
   "This definition mirrors
    the relevant portion of the definition of @(tsee termp).")
  (and (true-listp x)
       (= (len x) 3)
       (eq (first x) 'lambda)
       (arglistp (second x))
       (termp (third x) wrld)
       (null (set-difference-eq (all-vars (third x)) (second x))))
  ///

  (defrule lambdap-when-termp
    (implies (and (termp term wrld)
                  (consp term)
                  (consp (car term)))
             (lambdap (car term) wrld)))

  (defrule termp-when-lambdap
    (implies (and (lambdap lambd wrld)
                  (term-listp terms wrld)
                  (equal (len terms) (len (lambda-formals lambd))))
             (termp (cons lambd terms) wrld)))

  (defrule not-lambdap-of-nil
    (not (lambdap nil wrld))))
