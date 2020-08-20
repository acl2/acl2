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
    "This is exactly like a @(tsee defun-sk),
     but it also generates an event to disable
     the function definition and its associated rewrite rule.
     The rewrite rule associated to a @(tsee defun-sk)
     is the one whose name is controlled by the @(':thm-name') option.
     When the function is constrained (i.e. @(':constrain') is @('t')),
     it does not have a definition, but it has a definition rule:
     this is the one being disabled by @('defund-sk').")))
