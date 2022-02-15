; Yul Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "kestrel/fty/defresult" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ errors
  :parents (language)
  :short "Errors used in the formalization of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "When we formalize static and dynamic semantics of Yul,
     our ACL2 functions return error values in certain circumstances.
     An example is when a variable is referenced that is not accessible.")
   (xdoc::p
    "We use @(tsee fty::defresult) and companion utilities
     to handle errors in our Yul formalization."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define resulterr-limitp (x)
  :returns (yes/no booleanp)
  :short "Recognize limit errors."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in the "
    (xdoc::seetopic "dynamic-semantics" "dynamic semantics")
    ", the ACL2 functions that formalize the execution of Yul code
     take an artificial limit counter as input,
     and return an error when that limit is exhausted.
     This is one of several kinds of errors that may be returned
     by those ACL2 functions, which formalize a defensive dynamic semantics.")
   (xdoc::p
    "Here we define a predicate that recognizes limit errors,
     i.e. values of type @(tsee resulterr)
     whose information starts with the keyword @(':limit').
     The adequacy of this predicate definition depends on
     the definition of the ACL2 execution functions for Yul,
     in particular the fact that they return error limits of this form.
     This predicate must be adapted if that form changes."))
  (and (resulterrp x)
       (b* ((info (fty::resulterr->info x)))
         (and (consp info)
              (eq (car info) :limit)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define resulterr-nonlimitp (x)
  :returns (yes/no booleanp)
  :short "Recognize non-limit errors."
  :long
  (xdoc::topstring
   (xdoc::p
    "This recognizes all the errors
     that are not recognized by @(tsee resulterr-limitp).
     See that recognizer's documentation."))
  (and (resulterrp x)
       (not (resulterr-limitp x))))
