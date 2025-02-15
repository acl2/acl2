; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-conditional-expressions
  :parents (atc-shallow-embedding)
  :short "Representation of C conditional expressions for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "C conditional expressions and statements are both non-strict,
     so they both have to be represented by @(tsee if) in ACL2.
     To provide control on which @(tsee if)s represent conditional statements
     and which @(tsee if)s represent conditional expressions,
     we provide a function @(tsee condexpr) that is just identity
     but can be used to wrap an @(tsee if) to signify that
     it represents a C conditional expression instead of statement.
     Without that wrapper, an @(tsee if) represents a conditional statement,
     which is more common than a conditional expression in C."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define condexpr (x)
  :short "Wrapper to represent C conditional expressions."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-conditional-expressions).")
  x)
