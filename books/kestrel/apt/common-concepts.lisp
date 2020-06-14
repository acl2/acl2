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
