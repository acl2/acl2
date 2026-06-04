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
(include-book "lists")

(include-book "defsort/duplicated-members" :dir :system)
(include-book "kestrel/typed-lists-light/nat-list-listp" :dir :system)
(include-book "std/util/defprojection" :dir :system)

(local (include-book "std/typed-lists/string-listp" :dir :system))

(acl2::controlled-configuration)

(local (in-theory (enable* ast-corep-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-structurals
  :parents (abstract-syntax)
  :short "Structural operations and theorems on ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are purely structural operations and theorems,
     e.g. lifting from elements to lists.
     At least some of these could be generated from the fixtype definitions."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist expr-list-case-array (x)
  :short "Check if all the expressions in a list
          are in the @(':array') summand."
  :guard (expr-listp x)
  (expr-case x :array))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist expr-list-case-frame (x)
  :short "Check if all the expressions in a list
          are in the @(':frame') summand."
  :guard (expr-listp x)
  (expr-case x :frame))

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
    :induct t))

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
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection expr-array-list->dims ((x expr-listp))
  :guard (expr-list-case-array x)
  :returns (dimss nat-list-listp)
  :short "Lift @(tsee expr-array->dims) to lists."
  (expr-array->dims x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection expr-array-list->atoms ((x expr-listp))
  :guard (expr-list-case-array x)
  :returns (atomss atom-list-listp)
  :short "Lift @(tsee expr-array->atoms) to lists."
  (expr-array->atoms x)

  ///

  (defrule atom-list-list-corep-of-expr-array-list->atoms
    (implies (and (expr-list-corep exprs)
                  (expr-list-case-array exprs))
             (atom-list-list-corep (expr-array-list->atoms exprs)))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection expr-frame-list->dims ((x expr-listp))
  :guard (expr-list-case-frame x)
  :returns (dimss nat-list-listp)
  :short "Lift @(tsee expr-frame->dims) to lists."
  (expr-frame->dims x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection expr-frame-list->exprs ((x expr-listp))
  :guard (expr-list-case-frame x)
  :returns (exprss expr-list-listp)
  :short "Lift @(tsee expr-frame->exprs) to lists."
  (expr-frame->exprs x)

  ///

  (defrule expr-list-list-corep-of-expr-frame-list->exprs
    (implies (and (expr-list-corep exprs)
                  (expr-list-case-frame exprs))
             (expr-list-list-corep (expr-frame-list->exprs exprs)))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-atomp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type has the atom kind."
  (type-case type
             :var (type-var-case type.var :atom)
             :base t
             :array nil
             :bracket nil
             :fun t
             :forall t
             :pi t
             :sigma t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-append-all ((exprss expr-list-listp))
  :returns (exprs expr-listp)
  :short "Append all the lists of expressions in a list, in that order."
  (cond ((endp exprss) nil)
        (t (append (expr-list-fix (car exprss))
                   (expr-append-all (cdr exprss)))))

  ///

  (defrule expr-list-corep-of-expr-append-all
    (equal (expr-list-corep (expr-append-all exprss))
           (expr-list-list-corep exprss))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom-append-all ((atomss atom-list-listp))
  :returns (atoms atom-listp)
  :short "Append all the lists of atoms in a list, in that order."
  (cond ((endp atomss) nil)
        (t (append (atom-list-fix (car atomss))
                   (atom-append-all (cdr atomss)))))

  ///

  (defrule atom-list-corep-of-atom-append-all
    (equal (atom-list-corep (atom-append-all atomss))
           (atom-list-list-corep atomss))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule expr-listp-of-append-all
  :short "Type of @(tsee append-all) applied to lists of lists of expressions."
  (implies (expr-list-listp lists)
           (expr-listp (append-all lists)))
  :induct t
  :enable append-all)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule atom-listp-of-append-all
  :short "Type of @(tsee append-all) applied to lists of lists of atoms."
  (implies (atom-list-listp lists)
           (atom-listp (append-all lists)))
  :induct t
  :enable append-all)
