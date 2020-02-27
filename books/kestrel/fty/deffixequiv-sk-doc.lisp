; FTY Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "deffixequiv-sk")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc deffixequiv-sk

  :parents (fty deffixequiv)

  :short "A variant of @(tsee deffixequiv) for @(tsee defun-sk) functions."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "The macro @(tsee deffixequiv) automates the generation of theorems
      saying that a function fixes its arguments to certain types.
      That macro provides the ability to supply hints,
      which are often not needed if the function
      explicitly fixes the arguments (by calling fixing functions)
      or implicitly does so by calling functions that do
      (for which the fixing theorems have already been proved.")

    (xdoc::p
     "However, when @(tsee defun-sk) functions
      similarly, explicitly or implicitly, fix their arguments,
      hints are needed in order to prove the fixing theorems.
      Unsurprisingly, these hints have a boilerplate form
      that can be derived from the function.")

    (xdoc::p
     "This macro, @('deffixequiv-sk'), generates these hints.
      More precisely, it generates a @(tsee deffixequiv)
      that includes the hints derived from the function.")

    (xdoc::p
     "If you find that this macro fails,
      please notify the implementor.
      Future versions of this macro may also allow the user
      to specify additional hints (besides the generated ones)
      to help prove the fixing properties."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form-auto deffixequiv-sk)

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@('fn')"
     (xdoc::p
      "A symbol that specifies the @(tsee defun-sk) function."))

    (xdoc::desc
     "@(':args') &mdash; default @('nil')"
     (xdoc::p
      "A list of doublets @('((arg1 pred1) ... (argn predn))')
       where each @('argi') is an argument of @('fn')
       and @('predi') is the predicate that the argument is fixed to.
       The @('argi') symbols must all be distinct.")
     (xdoc::p
      "This syntax is similar to @(tsee deffixequiv).
       Note that the @('predi') symbols must be predicates,
       not fixtype names.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::p
     "A call")
    (xdoc::codeblock
     "(deffixequiv :args ((arg1 pred1) ... (argn predn)) :hints ...)")
    (xdoc::p
     "where @('...') are hints generated from the function.
      The exact form of and motivation for these hints will be described
      in upcoming extensions of this documentation."))))
