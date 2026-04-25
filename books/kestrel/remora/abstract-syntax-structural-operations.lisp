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
     At least some of these could be generated from the fixtype definitions."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection dim-const-list ((x nat-listp))
  :returns (dims dim-listp)
  :short "Lift @(tsee dim-const) to lists."
  (dim-const x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection shape-dim-list ((x dim-listp))
  :returns (shapes shape-listp)
  :short "Lift @(tsee shape-dim) to lists."
  (shape-dim x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(std::defprojection typed-var-list->type ((x typed-var-listp))
  :returns (types type-listp)
  :short "Lift @(tsee typed-var->type) to lists."
  (typed-var->type x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection type+shape-list->type ((x type+shape-listp))
  :returns (types type-listp)
  :short "Lift @(tsee type+shape->type) to lists."
  (type+shape->type x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection type+shape-list->shape ((x type+shape-listp))
  :returns (ispaces shape-listp)
  :short "Lift @(tsee type+shape->shape) to lists."
  (type+shape->shape x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-param->name ((param ispace-paramp))
  :returns (name stringp)
  :short "Name of an ispace parameter."
  :long
  (xdoc::topstring
   (xdoc::p
    "Both summands have a string field,
     which is the name of the variable."))
  (ispace-param-case param
                     :dim param.name
                     :shape param.name))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection ispace-param-list->name ((x ispace-param-listp))
  :returns (names string-listp)
  :short "Lift @(tsee ispace-param->name) to lists."
  (ispace-param->name x))
