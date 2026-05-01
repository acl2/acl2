; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-core")
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
  (shape-dim x)

  ///

  (defrule shape-list-corep-of-shape-dim-list
    (shape-list-corep (shape-dim-list dims))
    :induct t
    :enable abstract-syntax-corep-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection base-lit-int-list ((x int-lit-listp))
  :returns (lits base-lit-listp)
  :short "Lift @(tsee base-lit-int) to lists."
  (base-lit-int x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection atom-base-list ((x base-lit-listp))
  :returns (atoms atom-listp)
  :short "Lift @(tsee atom-base) to lists."
  (atom-base x)

  ///

  (defrule atom-list-corep-of-atom-base-list
    (atom-list-corep (atom-base-list lits))
    :induct t
    :enable abstract-syntax-corep-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection var+type-list->var ((x var+type-listp))
  :returns (strings string-listp)
  :short "Lift @(tsee var+type->var) to lists."
  (var+type->var x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection var+type-list->type ((x var+type-listp))
  :returns (types type-listp)
  :short "Lift @(tsee var+type->type) to lists."
  (var+type->type x))

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

(define ispace-var->name ((var ispace-varp))
  :returns (name stringp)
  :short "Name of an ispace variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "Both summands have a string field,
     which is the name of the variable."))
  (ispace-var-case var
                   :dim var.name
                   :shape var.name))

;;;;;;;;;;;;;;;;;;;;

(std::defprojection ispace-var-list->name ((x ispace-var-listp))
  :returns (names string-listp)
  :short "Lift @(tsee ispace-var->name) to lists."
  (ispace-var->name x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-var->name ((var type-varp))
  :returns (name stringp)
  :short "Name of a type variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "Both summands have a string field,
     which is the name of the variable."))
  (type-var-case var
                 :atom var.name
                 :array var.name))

;;;;;;;;;;;;;;;;;;;;

(std::defprojection type-var-list->name ((x type-var-listp))
  :returns (names string-listp)
  :short "Lift @(tsee type-var->name) to lists."
  (type-var->name x))
