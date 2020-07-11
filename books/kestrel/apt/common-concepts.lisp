; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ common-concepts
  :parents (apt)
  :short "Concepts that are common to different APT transformations."
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc redundancy
  :short "Notion of redundancy for APT transformations."
  :long
  (xdoc::topstring
   (xdoc::p
    "A call of an APT transformation is redundant if and only if
     it is identical to a previous successful call of the same transformation
     whose @(':show-only') input is not @('t'),
     except that the two calls may differ in
     their @(':print') and @(':show-only') inputs.
     These options do not affect the generated events,
     and thus they are ignored for the purpose of redundancy.")
   (xdoc::p
    "A call of an APT transformation whose @(':show-only') input is @('t')
     does not generate any event.
     No successive call may be redundant with such a call.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc definedness
  :short "Notion of definedness of functions for some APT transformations."
  :long
  (xdoc::topstring
   (xdoc::p
    "As far as certain APT transformations are concerned,
     an ACL2 named function is defined if and only if
     it has a non-@('nil') unnormalized body.
     This notion of definedness applies to the APT transformations
     whose user documentation links to this XDOC topic
     from the place where the definedness requirement is stated.")
   (xdoc::p
    "The unnormalized body of a named function is
     the @('acl2::unnormalized-body') property of the function symbol.
     The value of this property is
     the " (xdoc::seetopic "acl2::term" "translated term") " obtained
     from the function body that appears (in untranslated form)
     in the @(tsee defun) event that introduces the function.
     This is the case not only for user-defined functions,
     but also for built-in defined ACL2 functions,
     whose introducing @(tsee defun) events can be seen
     via " (xdoc::seetopic "acl2::pe" "@(':pe')") ".")
   (xdoc::p
    "A valid untranslated term never translates to @('nil').
     The untranslated term @('nil') translates to @('\'nil'), a quoted constant.
     Valid variable symbols do not include @('nil'),
     so @('nil') is not a valid translated variable term;
     it satisfies @(tsee pseudo-termp)
     (which captures a superset of the valid translated terms),
     but it does not satisfy @(tsee termp).
     Therefore, the unnormalized body of a defined function cannot be @('nil'):
     testing the @('acl2::unnormalized-body') property against @('nil')
     is therefore a good way to check
     whether a function is defined in the APT transformations
     that use this notion of definedness.")
   (xdoc::p
    "However, the built-in program-mode functions are defined
     but do not have an unnormalized body.
     Thus, the APT transformations that use this notion of definedness
     would not regard these functions as being defined.
     Nonetheless,
     all such transformations require the functions to be logic-mode,
     thus excluding (built-in or non-built-in) program-mode functions.")
   (xdoc::p
    "The system utility @(tsee acl2::ubody) (or @(tsee acl2::ubody+))
     retrieves the unnormalized body of a function.
     It is a specialization of the built-in @(tsee body) system utility,
     which retrieves the unnormalized or normalized body of a function.
     based on the flag passed as argument.
     The normalized body of a function may differ from the unnormalized one
     because the former may be obtained from the latter
     via some simplifications.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc function-name-generation
  :short "How APT transformations generate function names."
  :long
  (xdoc::topstring
   (xdoc::p
    "APT transformations normally generate
     transformed functions from existing functions.
     The names of the generated functions may be specified explicitly,
     or may be automatically generated from the names of the existing functions,
     according to some rules.
     Certain APT transformations do that according to the rules described here.
     These rules apply only to the APT transformations
     whose user documentation explicitly references this XDOC topic.")
   (xdoc::p
    "The name generation rules described here are based on "
    (xdoc::seetopic "acl2::numbered-names" "numbered names")
    ": see their topic first.
     Roughly speaking, the application of an APT transformation
     to a target function whose name is a numbered name
     generates a new function with the next numbered name,
     i.e. the numbered name with the same base as the target function
     and with the smallest index greater than the one of the target function
     that makes the new function's name fresh, i.e. valid for a new function.
     Such an index is often one plus the index of the target function,
     but in general it may be larger if that name already happens to exist
     (which would not be a recommended way to organize an APT derivation,
     but cannot be prevented in general).")
   (xdoc::p
    "Certain APT transformations, when applied to a target function,
     generate a single new function.
     These transformations have a @(':new-name') input, which is
     either @(':auto') (the default) to specify automatic name generation,
     or an explicitly specified symbol to use for the new function.
     When the @(':new-name') input is @(':auto'),
     the name of the new function is determined
     just as explained in the previous paragraph.")
   (xdoc::p
    "Certain APT transformations may generate, besides the new function,
     also an additional wrapper function,
     This happens when the new function has different arguments
     (i.e. different in number and/or in types)
     from the target function:
     the wrapper function has
     the same number and types of arguments as the target function,
     and calls the new function with suitable arguments,
     i.e. it ``wraps'' the new function to match the old function.
     The wrapper function is optional:
     these transformations have a @(':wrapper') boolean input
     that specifies whether the wrapper function is generated (@('t'))
     or not (@('nil'), the default).
     When the @(':wrapper') input is @('nil'),
     only the new function is generated,
     and when the @(':new-name') input is @(':auto')
     its name is again generated as explained above.")
   (xdoc::p
    "If instead the @(':wrapper') input is @('t'),
     then another input of the transformation, @(':wrapper-name'),
     becomes relevant
     (this input may be present only if @(':wrapper') is @('nil')).
     Similarly to @(':new-name'), also @(':wrapper-name') may be
     either @(':auto') to specify automatic name generation
     or a symbol to use as the wrapper function name.
     Note that one of @(':new-name') and @(':wrapper-name') may be @(':auto'),
     but not the other.
     The rules for automatic name generation are as follows:")
   (xdoc::ul
    (xdoc::li
     "If neither @(':new-name') nor @(':wrapper-name') is @(':auto'),
      then there is actually no automatic name generation.")
    (xdoc::li
     "If @(':new-name') is @(':auto') but @(':wrapper-name') is not,
      the name of the new function is determined as above,
      with the additional constraint that the new index must be such that
      the resulting name is distinct from
      the explicitly specified wrapper function name.
      In a well-structured APT derivation,
      this additional constraint is expected to be normally satisfied
      by one plus the index of the target function.")
    (xdoc::li
     "If @(':wrapper-name') is @(':auto') but @(':new-name') is not,
      the rules are the same as the previous case,
      but with the roles of the new and wrapper function names swapped.
      That is, the wrapper function name is a numberd name
      whose base is the same as the target function,
      and whose index is the smallest one that is
      greater than the index of the target function
      and also distinct from the explicitly specified new function name.")
    (xdoc::li
     "If both @(':new-name') and @(':wrapper-name') are @(':auto'),
      then both the new and wrapper function names are numbered names,
      determined as follows.
      The base of the new function's name is
      the concatenation of the target function's name followed by @('-aux').
      The base of the wrapper function's name is
      the same as the target function's name.
      The index of both new and wrapper function names is the smallest one
      that is greater than the one of the target function
      and that makes both the new and wrapper function names fresh.
      In well-structured APT derivations,
      this index is normally expected to be
      just one plus the target function's index."))
   (xdoc::p
    "The @('-aux') in the new function name in the last case above
     means `auxiliary', which is a common naming convention
     for the ``loop'' of a function (in this case, the wrapper function).")))
