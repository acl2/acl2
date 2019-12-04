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

(define all-non-gv-exec-ffn-symbs ((term pseudo-termp) (wrld plist-worldp))
  :returns (final-ans "A @(tsee symbol-listp).")
  :mode :program
  :parents (std/system/term-queries)
  :short "Non-guard-verified functions called by a term for execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are all the non-guard-verified functions that occur in the term,
     except those that occur in the @(':logic') subterms of @(tsee mbe)s
     and those called via @(tsee ec-call).
     This is because, in order for a function to be guard-verified,
     the functions that occurs in such subterms do not have to be guard-verified.
     If this function returns @('nil'),
     the term could be potentially guard-verified.")
   (xdoc::p
    "The name of this function is consistent with
     the name of @('all-ffn-symbs') in the ACL2 source code.")
   (xdoc::p
    "The @('all-fnnames-exec') built-in system utility
     returns all the function symbols except
     the ones in the @(':logic') subterms of @(tsee mbe)s
     and the ones called via @(tsee ec-call)
     (see the ACL2 source code).
     The @('collect-non-common-lisp-compliants') built-in system utility
     returns all the ones that are not guard-verified
     (see the ACL2 source code)."))
  (collect-non-common-lisp-compliants (all-fnnames-exec term) wrld))
