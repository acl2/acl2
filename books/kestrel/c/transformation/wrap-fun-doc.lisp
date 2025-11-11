; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ wrap-fun
  :parents (transformation-tools)
  :short "A C-to-C transformation to introduce a function wrapper."
  :long
  (xdoc::topstring
    (xdoc::evmac-section-intro
      (xdoc::p
        "This transformation introduces ``function wrappers'' &mdash; i.e.
         new functions which do nothing but call the function they ``wrap.''
         All subsequent occurrences of the original functions in the function
         position of direct function calls (i.e., function calls not invoking a
         function pointer) are replaced with the wrapper function. The wrapper
         functions are defined with internal linkage."))
    (xdoc::evmac-section-form
      (xdoc::codeblock
        "(wrap-fun const-old"
        "          const-new"
        "          :targets ... ; required"
        "  )"
        ))
    (xdoc::evmac-section-inputs
      (xdoc::desc
        "@('const-old')"
        (xdoc::p
          "Specifies the code to be transformed.")
        (xdoc::p
          "This must be a symbol that names an existing ACL2 constant
          that contains a  validated code ensemble,
          i.e. a value of type @(tsee code-ensemble)
          whose translation unit ensemble results from "
          (xdoc::seetopic "c$::validator" "validation")
          ", and in particular containing "
          (xdoc::seetopic "c$::validation-information" "validation information")
          ". This constant could result from @(tsee c$::input-files),
          or from some other "
          (xdoc::seetopic "transformation-tools" "transformation")
          "."))
      (xdoc::desc
        "@('const-new')"
        (xdoc::p
          "Specifies the name of the constant for the transformed code.")
        (xdoc::p
          "This must be a symbol that is valid name for a new ACL2 constant."))
      (xdoc::desc
        "@(':targets') &mdash; no default"
        (xdoc::p
          "Either a string list, or an alist from strings to optional strings.
           When an alist is provided, each key of the alist denotes the
           identifier of a function for which we will define a wrapper. The key
           is optionally associated with a wrapper name. If no wrapper name is
           provided, a fresh name will be generated. When a string list is
           provided, it is interpreted as if it were an alist with all elements
           of the list associated to @('nil').")))
    (xdoc::section
      "Current Limitations"
      (xdoc::p
        "The following are temporary limitations which will hopefully be removed
         in the future with improvements to the implementation.")
      (xdoc::ul
        (xdoc::li
          "Target functions with a non-prototype signature are
           unsupported. This includes both ``old style'' function definitions
           and the special case of a function declaration with an empty
           parameter list that is not part of a function definition.")
        (xdoc::li
          "Target functions with a variadic signature are unsupported.
           Eventually, we may support such functions by looking ahead for all
           direct invocations and generating a wrapper for each necessary
           arity.")
        (xdoc::li
          "A translation unit may have multiple declarations of a function,
           some of which fall in the supported set, and some in the
           unsupported. In such cases, the function wrapper is defined
           immediately after the first supported function declaration. Any
           function call occurring earlier in the translation unit will not be
           transformed into calls of the wrapper.")
        (xdoc::li
          "The search for declarations of the target function occurs at file
           scope. Function declarations in block scopes will not be found.")
        (xdoc::li
          "For a wrapper to be defined, a declaration must be found in the
           translation unit. "
          (xdoc::seetopic "c$::gcc-builtins" "Built-in")
          " functions which are used without declaration are unsupported.")
        (xdoc::li
          "No mechanism is provided to differentiate functions of the same
          name.")
        (xdoc::li
          "The function wrapper is not substituted for the original function in
           function pointers. This is a conservative measure to ensure
           correctness. Imagine that a function pointer is compared for
           equality against itself. If one of those function pointers were to
           be replaced with a pointer to the wrapper, but not the other, this
           comparison would now yield @('0'). Thus, we cannot substitute
           function pointers unless we can rule out this possibility. In
           theory, it is possible in practice to establish such a comparison
           won't happen in many cases. For instance, if we have the full
           program and we substitute all mentions of the target function
           outside of the wrapper. Or, if we have a partial program but we
           perform some basic escape analysis to establish the modified
           function pointers do not escape the visible program fragment.")))))
