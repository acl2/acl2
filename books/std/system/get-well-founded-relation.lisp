; Standard System Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-well-founded-relation ((fn symbolp) (wrld plist-worldp))
  :returns (well-founded-relation "A @(tsee symbolp).")
  :verify-guards nil
  :parents (std/system/function-queries)
  :short "Well-founded relation of a named logic-mode recursive function."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see well-founded-relation-rule)
     for a discussion of well-founded relations in ACL2,
     including the @(':well-founded-relation') rule class.")
   (xdoc::p
    "See @(tsee get-well-founded-relation+) for
     an enhanced variant of this utility.")
   (xdoc::p
    "This is called @('get-well-founded-relation')
     instead of just @('well-founded-relation')
     to avoid a topic conflict with the XDOC manual."))
  (b* ((justification (getpropc fn 'justification nil wrld)))
    (access justification justification :rel)))
