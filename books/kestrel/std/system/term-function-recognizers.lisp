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

(local (include-book "kestrel/utilities/system/all-vars-theorems" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc term-function-recognizers
  :parents (std/system)
  :short "Recognizers of functions in terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "In translated @(see term)s,
     the `functions' that are applied to argument terms are
     function symbols and lambda expressions.")
   (xdoc::p
    "The built-in predicates @(tsee pseudo-termp) and @(tsee termp)
     recognize pseudo-terms and valid translated terms.
     The following predicates recognize
     lambda expressions in pseudo-terms and in valid translated terms,
     as well as functions (in the sense above)
     in pseudo-terms and in valid translated terms.")
   (xdoc::p
    "Note that the built-in predicate @(tsee symbolp) recognizes
     functions in pseudo-terms that are not lambda expressions,
     and that the predicate @(tsee function-symbolp) recognizes
     functions in valid translated terms that are not lambda expressions
     (the latter has guard @(tsee symbolp),
     so it must be actually preceded by a call of @(tsee symbolp)
     in guard-verified code).
     These predicates, with the ones below,
     provide ways to recognize all kinds of functions in terms.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pseudo-lambdap (x)
  :returns (yes/no booleanp)
  :parents (term-function-recognizers)
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
       (int= (len x) 3)
       (eq (first x) 'lambda)
       (symbol-listp (second x))
       (pseudo-termp (third x)))
  ///

  (defrule pseudo-lambdap-when-pseudo-termp
    (implies (and (pseudo-termp term)
                  (consp term)
                  (consp (car term)))
             (pseudo-lambdap (car term))))

  (defrule pseudo-termp-when-pseudo-lambdap
    (implies (and (pseudo-lambdap lambd)
                  (pseudo-term-listp terms)
                  (equal (len terms) (len (lambda-formals lambd))))
             (pseudo-termp (cons lambd terms)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pseudo-termfnp (x)
  :returns (yes/no booleanp)
  :parents (term-function-recognizers)
  :short
  (xdoc::topstring
   "Recognize pseudo-term-functions,
    i.e. functions in "
   (xdoc::seetopic "pseudo-termp" "pseudo-terms")
   ".")
  (or (symbolp x)
      (pseudo-lambdap x))
  ///

  (defrule pseudo-termfnp-when-pseudo-termp
    (implies (and (pseudo-termp term)
                  (consp term))
             (pseudo-termfnp (car term)))
    :enable pseudo-lambdap)

  (defrule pseudo-termp-when-pseudo-termfnp
    (implies (and (pseudo-termfnp fn)
                  (pseudo-term-listp terms)
                  (or (atom fn)
                      (equal (len terms) (len (lambda-formals fn))))
                  (not (eq fn 'quote)))
             (pseudo-termp (cons fn terms)))
    :enable pseudo-lambdap))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lambdap (x (wrld plist-worldp-with-formals))
  :returns (yes/no booleanp)
  :parents (term-function-recognizers)
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
       (int= (len x) 3)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define termfnp (x (wrld plist-worldp-with-formals))
  :returns (yes/no booleanp)
  :parents (term-function-recognizers)
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
