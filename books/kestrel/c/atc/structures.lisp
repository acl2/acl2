; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "values")

(include-book "../language/tag-environments")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-structures
  :parents (atc-dynamic-semantics)
  :short "A model of C structures for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "Structures are modeled as the @(':struct') kind of @(tsee value).
     Here we introduce some functions over structures."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define member-value-to-type ((member member-valuep))
  :returns (meminfo member-typep)
  :short "Turn a member value into the corresponding member type."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @(tsee member-type) is the static counterpart of
     a @(tsee member-value)."))
  (make-member-type :name (member-value->name member)
                    :type (type-of-value (member-value->value member)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection member-values-to-types (x)
  :guard (member-value-listp x)
  :returns (infos member-type-listp)
  :short "Lift @(tsee member-value-to-type) to lists."
  (member-value-to-type x)
  ///
  (fty::deffixequiv member-values-to-types
    :args ((x member-value-listp))))
