; Term Function Recognizers
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "all-vars-theorems"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc term-function-recognizers
  :parents (term-utilities system-utilities-non-built-in)
  :short "Recognizers of functions in terms."
  :long
  "<p>
   In translated @(see term)s,
   the `functions' that are applied to argument terms are
   function symbols and lambda expressions.
   </p>
   <p>
   The predicates @(tsee pseudo-termp) and @(tsee termp)
   recognize pseudo-terms and valid translated terms.
   The following predicates recognize
   lambda expressions in pseudo-terms and in valid translated terms,
   as well as functions (in the sense above)
   in pseudo-terms and in valid translated terms.
   </p>
   <p>
   Note that the predicate @(tsee symbolp) recognizes
   functions in pseudo-terms that are not lambda expressions,
   and the predicate @(tsee function-namep) recognizes
   functions in valid translated terms that are not lambda expressions.
   </p>")

(define pseudo-lambdap (x)
  :returns (yes/no booleanp)
  :parents (term-utilities term-function-recognizers)
  :short "Recognize pseudo-lambda-expressions,
          i.e. lambda expressions in
          <see topic='@(url pseudo-termp)'>pseudo-terms</see>."
  :long
  "<p>
   This definition mirrors
   the relevant portion of the definition of @(tsee pseudo-termp).
   </p>"
  (and (true-listp x)
       (= (len x) 3)
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

(define pseudo-termfnp (x)
  :returns (yes/no booleanp)
  :parents (term-utilities term-function-recognizers)
  :short "Recognize pseudo-term-functions,
          i.e. functions in
          <see topic='@(url pseudo-termp)'>pseudo-terms</see>."
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

(define lambdap (x (wrld plist-worldp-with-formals))
  :returns (yes/no booleanp)
  :parents (term-utilities term-function-recognizers)
  :short "Recognize valid
          <see topic='@(url term)'>translated</see> lambda expression,
          i.e. lambda expressions in valid translated terms."
  :long
  "<p>
   This definition mirrors
   the relevant portion of the definition of @(tsee termp).
   </p>"
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

(define termfnp (x (wrld plist-worldp-with-formals))
  :returns (yes/no booleanp)
  :parents (term-utilities term-function-recognizers)
  :short "Recognize valid
          <see topic='@(url term)'>translated</see> term functions,
          i.e. functions in valid translated terms."
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

(std::deflist pseudo-lambda-listp (x)
  (pseudo-lambdap x)
  :parents (term-utilities term-function-recognizers)
  :short "Recognize true lists of
          <see topic='@(url pseudo-lambdap)'>pseudo-lambda-expressions</see>."
  :elementp-of-nil nil
  :true-listp t)

(std::deflist pseudo-termfn-listp (x)
  (pseudo-termfnp x)
  :parents (term-utilities term-function-recognizers)
  :short "Recognize true lists of
          <see topic='@(url pseudo-termfnp)'>pseudo-term-functions</see>."
  :elementp-of-nil t
  :true-listp t)

(std::deflist lambda-listp (x wrld)
  (lambdap x wrld)
  :guard (plist-worldp-with-formals wrld)
  :parents (term-utilities term-function-recognizers)
  :short "Recognize true lists of valid
          <see topic='@(url lambdap)'>translated lambda expressions</see>."
  :elementp-of-nil nil
  :true-listp t)

(std::deflist termfn-listp (x wrld)
  (termfnp x wrld)
  :guard (plist-worldp-with-formals wrld)
  :parents (term-utilities term-function-recognizers)
  :short "Recognize true lists of
          valid <see topic='@(url termfnp)'>translated term functions</see>."
  :long
  "<p>
   We would need stronger world assumptions for @(':elementp-of-nil nil'),
   so with the current weaker world assumptions we leave the default,
   i.e. @(':elementp-of-nil :unknown').
   </p>"
  :true-listp t)
