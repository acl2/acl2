; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "arithmetic")
(include-book "lists")
(include-book "nat-lists")
(include-book "integer-lists")
(include-book "oset-omaps")
(include-book "unit-types")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ library-extensions
  :parents (remora)
  :short "Library extensions for Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used in the Remora library but are more general,
     and should be moved to more general libraries eventually."))
  :order-subtopics (arithmetic
                    lists
                    nat-lists
                    integer-lists
                    oset-omap-theorems
                    unit-types))
