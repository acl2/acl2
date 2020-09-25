; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defund-sk
  :parents (std::std/util-extensions std/util defun-sk)
  :short "Define a function with quantifier
          and disable it and its associated rewrite rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is exactly like a @(tsee defun-sk), except for two differences:")
   (xdoc::ul
    (xdoc::li
     "It also generates an event to disable the function definition.
      Thus, this macro is consistent with built-in macros like
      @(tsee defund) and @(tsee defund-nx).")
    (xdoc::li
     "It also supports a @(':thm-enable') input, @('nil') by default,
      that is used to generate, when @('nil'), an event to disable
      the rewrite rule associated to the function.
      This rewrite rule is the one
      whose name is controlled by the @(':thm-name') option;
      thus, the @(':thm-enable') option of @('defund-sk2')
      is named consistently.
      No disabling event is generated if @(':thm-enable') is @('t');
      the rewrite rule is left enabled."))))
