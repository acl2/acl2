; System Utilities -- Event Form Lists
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/deflist" :dir :system)
(include-book "event-forms")

(include-book "system/pseudo-event-form-listp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist pseudo-event-form-listp (x)
  (pseudo-event-formp x)
  :parents (event-forms)
  :short "Recognize true lists whose elements all have the
          <see topic='@(url pseudo-event-formp)'>basic structure
          of an event form</see>."
  :long (xdoc::topstring-@def "pseudo-event-form-listp")
  :true-listp t
  :elementp-of-nil nil)
