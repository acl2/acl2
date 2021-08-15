; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "kestrel/fty/defflatsum" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ errors
  :parents (yul)
  :short "Error values used in the formalization of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "When we formalize static and dynamic semantics of Yul,
     our ACL2 functions return error values in certain circumstances.
     An example is when a variable is referenced that is not accessible.")
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

(defsection defresult
  :short "Introduce a fixtype of result types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a flat sum of the specified fixtype
     and the error fixtype.
     Thus, the specified fixtype must be disjoint from the error fixtype,
     which is easily satisfied if values of the specified fixtype
     do not start with @(':error').")
   (xdoc::p
    "We also generate a theorem to conclude that a value is of the original type
     when it is of the new type and not an error.
     We disable it by default so that
     we do not always backchain to the result type
     when trying to prove the base type,
     in contexts where the result type may not be used at all."))

  (define defresult-fn (type desc name enable (wrld plist-worldp))
    :returns event ; PSEUDO-EVENT-FORMP
    :mode :program
    (b* ((fty-table (fty::get-fixtypes-alist wrld))
         (fty-info (fty::find-fixtype type fty-table))
         (typep (fty::fixtype->pred fty-info))
         (name (or name type))
         (name-result (add-suffix name "-RESULT"))
         (name-resultp (add-suffix name "-RESULTP"))
         (short (str::cat "Fixtype of " desc " and errors."))
         (typep-when-name-resultp-and-not-errorp
          (acl2::packn-pos (list typep '-when- name-resultp '-and-not-errorp)
                           name)))
      `(encapsulate ()
         (fty::defflatsum ,name-result
           :short ,short
           (:ok ,type)
           (:err error)
           :pred ,name-resultp
           ,@(and enable
                  `(:prepwork
                    ((defrulel disjoint
                       (implies (errorp x)
                                (not (,typep x)))
                       :enable ,enable)))))
         (defruled ,typep-when-name-resultp-and-not-errorp
           (implies (and (,name-resultp x)
                         (not (errorp x)))
                    (,typep x))
           :enable ,name-resultp))))

  (defmacro defresult (type desc &key name enable)
    `(make-event (defresult-fn ',type ',desc ',name ',enable (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-b*-binder ok
  :short "@(tsee b*) binder for checking and propagating errors."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is somewhat similar to @(tsee acl2::patind-er),
     but it is for values of "
    (xdoc::seetopic "defresult" "result types")
    ". It checks whether the bound expresion is an error,
     returning the error if the check succeeds.
     Otherwise, it proceeds with the rest of the computation."))
  :decls
  ((declare (xargs :guard (acl2::destructure-guard ok args acl2::forms 1))))
  :body
  `(b* ((patbinder-ok-fresh-variable-for-result ,(car acl2::forms))
        ((when (errorp patbinder-ok-fresh-variable-for-result))
         patbinder-ok-fresh-variable-for-result)
        (,(car args) patbinder-ok-fresh-variable-for-result))
     ,acl2::rest-expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult nat "natural numbers")
