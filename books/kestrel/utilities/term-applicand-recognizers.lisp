; Term Applicand Recognizers
;
; Copyright (C) 2016-2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)

(local (include-book "all-vars-theorems"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc term-applicand-recognizers
  :parents (term-utilities system-utilities)
  :short "Recognizers of term applicands."
  :long
  "<p>
   In translated @(see term)s,
   applicands are lambda expressions and function names.
   They are applied to argument terms.
   </p>
   <p>
   The built-in predicates @(tsee pseudo-termp) and @(tsee termp)
   recognize pseudo-terms and terms.
   The following predicates recognize lambda expressions and applicands
   in pseudo-terms and terms.
   </p>")

(define pseudo-lambdap (x)
  :returns (yes/no booleanp)
  :parents (term-utilities term-applicand-recognizers)
  :short "Recognize pseudo-lambda-expressions,
          i.e. lambda expressions of
          <see topic='@(url pseudo-termp)'>pseudo-terms</see>."
  :long
  "<p>
   Check whether @('x') is
   a @('nil')-terminated list of exactly three elements,
   whose first element is the symbol @('lambda'),
   whose second element is a list of symbols, and
   whose third element is a pseudo-term.
   </p>"
  (and (true-listp x)
       (= (len x) 3)
       (eq (first x) 'lambda)
       (symbol-listp (second x))
       (pseudo-termp (third x))))

(define pseudo-fn/lambda-p (x)
  :returns (yes/no booleanp)
  :parents (term-utilities term-applicand-recognizers)
  :short "Recognize pseudo-applicands,
          i.e. symbols and pseudo-lambda-expressions."
  :long
  "<p>
   Check whether @('x') is a symbol or a
   <see topic='@(url pseudo-lambdap)'>pseudo-lambda-expression</see>.
   These are the possible values of the first element of
   a <see topic='@(url pseudo-termp)'>pseudo-term</see>
   that is not a variable or a quoted constant
   (i.e. a pseudo-term that is a function application).
   </p>"
  (or (symbolp x)
      (pseudo-lambdap x)))

(define lambdap (x (wrld plist-worldp-with-formals))
  :returns (yes/no booleanp)
  :parents (term-utilities term-applicand-recognizers)
  :short "Recognize valid
          <see topic='@(url term)'>translated</see> lambda expression."
  :long
  "<p>
   Check whether @('x') is a @('nil')-terminated list of exactly three elements,
   whose first element is the symbol @('lambda'),
   whose second element is a list of legal variable symbols without duplicates,
   and whose third element is a valid translated term
   whose free variables are all among the ones in the second element.
   </p>"
  (and (true-listp x)
       (= (len x) 3)
       (eq (first x) 'lambda)
       (arglistp (second x))
       (termp (third x) wrld)
       (subsetp-eq (all-vars (third x))
                   (second x))))

(define fn/lambda-p (x (wrld plist-worldp-with-formals))
  :returns (yes/no booleanp)
  :parents (term-utilities term-applicand-recognizers)
  :short "Recognize valid applicands,
          i.e. function symbols and
          <see topic='@(url term)'>translated</see> lambda expression."
  (or (and (symbolp x)
           (function-symbolp x wrld))
      (lambdap x wrld)))
