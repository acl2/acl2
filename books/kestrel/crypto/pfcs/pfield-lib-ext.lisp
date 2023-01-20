; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "kestrel/prime-fields/fe-listp" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ prime-field-library-extensions
  :parents (prime-field-constraint-systems)
  :short "Extensions of the prime fields library."
  :long
  (xdoc::topstring
   (xdoc::p
    "These may be moved to the prime fields library."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled true-listp-when-fe-listp
  (implies (fe-listp x p)
           (true-listp x)))

(defruled nat-listp-when-fe-listp
  (implies (fe-listp x p)
           (nat-listp x)))
