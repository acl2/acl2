; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-validity")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ispace-validity-derived-rules
  :parents (static-semantics)
  :short "Derived inference rules for ispace validity."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are consequences of the defining rules in @(see ispace-validity).
     For now, they are the defining rules combined by kind of AST."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dim-validity-rules-by-kind
  :short "Defining rules of dimension validity, combined by kind of dimension."
  :long
  (xdoc::topstring
   (xdoc::p
    "The defining rules conclude the validity of a constructor application,
     e.g. @('(dim-var name)').
     These rules conclude the validity of a generic dimension,
     with hypotheses about the kind of dimension, e.g. @('(dim-case dim :var)').
     Thus, they are more applicable as rewrite rules in some proofs.")
   (xdoc::p
    "We prove one derived rule
     that combines the stronger rules
     into one applicable to a generic dimension.
     Its hypothesis mirrors the rules, by kind.
     The proof instantiates the stronger rules
     with the fields of the dimension,
     after enumerating the possible kinds of the dimension."))

  (defruled dim-ok-by-kind
    (implies (and (dimp dim)
                  (ispace-var-setp ivars)
                  (dim-case dim
                            :var (set::in (ispace-var-dim dim.name) ivars)
                            :const t
                            :add (dims-ok ivars dim.dims)
                            :mul (dims-ok ivars dim.dims)
                            :sub (and (consp dim.dims)
                                      (dims-ok ivars dim.dims))))
             (dim-ok ivars dim))
    :use ((:instance dim-kind-possibilities (x dim))
          (:instance dim-ok-var! (name (dim-var->name dim)))
          (:instance dim-ok-const! (val (dim-const->val dim)))
          (:instance dim-ok-add! (dims (dim-add->dims dim)))
          (:instance dim-ok-mul! (dims (dim-mul->dims dim)))
          (:instance dim-ok-sub! (dims (dim-sub->dims dim))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection shape-validity-rules-by-kind
  :short "Defining rules of shape validity, combined by kind of shape."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are analogous to @(see dim-validity-rules-by-kind)."))

  (defruled shape-ok-by-kind
    (implies (and (shapep shape)
                  (ispace-var-setp ivars)
                  (shape-case shape
                              :var (set::in (ispace-var-shape shape.name) ivars)
                              :dims (dims-ok ivars shape.dims)
                              :append (shapes-ok ivars shape.shapes)
                              :splice (ispaces-ok ivars shape.ispaces)))
             (shape-ok ivars shape))
    :use ((:instance shape-kind-possibilities (x shape))
          (:instance shape-ok-var! (name (shape-var->name shape)))
          (:instance shape-ok-dims! (dims (shape-dims->dims shape)))
          (:instance shape-ok-append! (shapes (shape-append->shapes shape)))
          (:instance shape-ok-splice! (ispaces (shape-splice->ispaces shape))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ispace-validity-rules-by-kind
  :short "Defining rules of ispace validity, combined by kind of ispace."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are analogous to @(see dim-validity-rules-by-kind)."))

  (defruled ispace-ok-by-kind
    (implies (and (ispacep ispace)
                  (ispace-case ispace
                               :dim (dim-ok ivars ispace.dim)
                               :shape (shape-ok ivars ispace.shape)))
             (ispace-ok ivars ispace))
    :use ((:instance ispace-kind-possibilities (x ispace))
          (:instance ispace-ok-dim! (dim (ispace-dim->dim ispace)))
          (:instance ispace-ok-shape! (shape (ispace-shape->shape ispace))))))
