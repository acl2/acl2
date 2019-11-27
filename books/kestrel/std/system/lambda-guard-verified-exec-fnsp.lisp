; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "guard-verified-exec-fnsp")
(include-book "pseudo-lambdap")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lambda-guard-verified-exec-fnsp ((lambd pseudo-lambdap)
                                         (wrld plist-worldp))
  :returns (yes/no "A @(tsee booleanp).")
  :mode :program
  :parents (std/system/term-queries)
  :short "Check if a lambda expression calls only guard-verified functions
          for execution."
  :long
  (xdoc::topstring-p
   "The name of this function is consistent with
    the name of @(tsee guard-verified-exec-fnsp).")
  (guard-verified-exec-fnsp (lambda-body lambd) wrld))
