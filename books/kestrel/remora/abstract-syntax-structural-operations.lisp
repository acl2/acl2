; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-derived-fixtypes")

(include-book "defsort/duplicated-members" :dir :system)
(include-book "std/util/defprojection" :dir :system)

(local (include-book "std/typed-lists/string-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-structural-operations
  :parents (abstract-syntax)
  :short "Structural operations on ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are purely structural operations,
     e.g. lifting from elements to lists.
     They could be probably generated from the fixtype definitions."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist sort-list-dimp (x)
  :guard (sort-listp x)
  :short "Check if all the sorts in a list are @(':dim')."
  (sort-case x :dim))

;;;;;;;;;;;;;;;;;;;;

(std::deflist sort-list-shapep (x)
  :guard (sort-listp x)
  :short "Check if all the sorts in a list are @(':shape')."
  (sort-case x :shape))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist kind-list-arrayp (x)
  :guard (kind-listp x)
  :short "Check if all the kinds in a list are @(':array')."
  (kind-case x :array))

;;;;;;;;;;;;;;;;;;;;

(std::deflist kind-list-atomp (x)
  :guard (kind-listp x)
  :short "Check if all the kinds in a list are @(':atom')."
  (kind-case x :atom))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection index-const-list ((x nat-listp))
  :returns (indices index-listp)
  :short "Lift @(tsee index-const) to lists."
  (index-const x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection sorted-var-list->var ((x sorted-var-listp))
  :returns (strings string-listp)
  :short "Lift @(tsee sorted-var->var) to lists."
  (sorted-var->var x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection kinded-var-list->var ((x kinded-var-listp))
  :returns (strings string-listp)
  :short "Lift @(tsee kinded-var->var) to lists."
  (kinded-var->var x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection kinded-var-list->kind ((x kinded-var-listp))
  :returns (kinds kind-listp)
  :short "Lift @(tsee kinded-var->kind) to lists."
  (kinded-var->kind x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection typed-var-list->var ((x typed-var-listp))
  :returns (strings string-listp)
  :short "Lift @(tsee typed-var->var) to lists."
  (typed-var->var x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection type+index-list->type ((x type+index-listp))
  :returns (types type-listp)
  :short "Lift @(tsee type+index->type) to lists."
  (type+index->type x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection type+index-list->index ((x type+index-listp))
  :returns (indices index-listp)
  :short "Lift @(tsee type+index->index) to lists."
  (type+index->index x))
