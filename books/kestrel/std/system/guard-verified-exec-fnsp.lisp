; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define guard-verified-exec-fnsp ((term pseudo-termp) (wrld plist-worldp))
  :returns (yes/no "A @(tsee booleanp).")
  :mode :program
  :parents (std/system/term-queries)
  :short "Check if a term calls only guard-verified functions for execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "Check if all the functions that occur in the term, except possibly
     the ones in the @(':logic') subterms of @(tsee mbe)s
     and the ones called via @(tsee ec-call),
     are guard-verified.
     The purpose of this function is to check whether a term
     could be potentially guard-verified.")
   (xdoc::p
    "The name of this function is consistent with
     the name of @(tsee guard-verified-fnsp).")
   (xdoc::p
    "The @('all-fnnames-exec') built-in system utility
     returns all the function symbols except
     the ones in the @(':logic') subterms of @(tsee mbe)s
     and the ones called via @(tsee ec-call)
     (see the ACL2 source code).
     The @('collect-non-common-lisp-compliants') built-in system utility
     returns all the ones that are not guard-verified
     (see the ACL2 source code)."))
  (null (collect-non-common-lisp-compliants (all-fnnames-exec term) wrld)))
