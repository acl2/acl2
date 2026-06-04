; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "list-theorems")
(include-book "nat-list-operations")
(include-book "integer-list-operations")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ library-extensions
  :parents (remora)
  :short "Library extensions for Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used in the Remora library but are more general,
     and should be moved to more general libraries eventually."))
  :order-subtopics (list-theorems
                    nat-list-operations
                    integer-list-operations))
