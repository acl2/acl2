; C Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "kestrel/fty/defflatsum" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-errors
  :parents (atc-implementation)
  :short "Error values used in the formalization of C for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "When we formalize static and dynamic semantics of C,
     our ACL2 functions return error values in certain circumstances.
     An example is when a run-time in our defensive dynamic semantics fails,
     e.g. due to a value having the wrong type for an operator.
     Another example is when some static constraints fail,
     e.g. a variable is referenced in some code without being in scope.")
   (xdoc::p
    "These ACL2 functions return different kinds of values
     when they do not fail.
     Thus, the return types of these functions include
     both those values and error values.")
   (xdoc::p
    "We introduce a fixtype for error values,
     which will be used in all those ACL2 functions.")
   (xdoc::p
    "We also introduce a macro to generate a fixtype that consists of
     a specified fixtype for the non-error values
     and the error fixtype.
     This is somewhat analogous to Rust's @('Result') type,
     but with a fixed type for the error type parameter."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod error
  :short "Fixtype of errors."
  :long
  (xdoc::topstring
   (xdoc::p
    "In order to be flexible in the kind of error information we return,
     we define this fixtype as a wrapper of any ACL2 value, at least for now.
     We may restrict this a bit later, e.g. to impose more structure."))
  ((info any))
  :tag :error
  :pred errorp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ fty::defresult (type desc)
  :short "Introduce a fixtype of result types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a flat sum of the specified fixtype
     and the error fixtype.
     Thus, the specified fixtype must be disjoint from the error fixtype,
     which is easily satisfied if values of the specified fixtype
     do not start with @(':error')."))
  `(fty::defflatsum ,(add-suffix type "-RESULT")
     :short ,(str::cat "Fixtype of " desc " and errors.")
     (:ok ,type)
     (:err error)
     :pred ,(add-suffix type "-RESULTP")))
