; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define thm-formula ((thm symbolp) (wrld plist-worldp))
  :returns (formula "A @(tsee pseudo-termp).")
  :parents (std/system/theorem-queries)
  :short "Formula of a named theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a specialization of @(tsee formula) to named theorems,
     for which the second argument of @(tsee formula) is immaterial.
     Since @(tsee formula) is in program mode only because of
     the code that handles the cases in which the first argument
     is not the name of a theorem,
     we avoid calling @(tsee formula) and instead replicate
     the code that handles the case in which
     the first argument is the name of a theorem;
     thus, this utility is in logic mode and guard-verified.")
   (xdoc::p
    "See @(tsee thm-formula+) for an enhanced variant of this utility."))
  (getpropc thm 'theorem nil wrld))
