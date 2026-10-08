; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "static-environments")

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ispace-validator
  :parents (static-semantics)
  :short "Validator of ispaces, including dimensions and shapes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This implements the specification in @(see ispace-validity)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-dims
  :short "Check dimensions and lists of dimensions."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-dim ((dim dimp) (ienv ispace-senvp))
    :returns (yes/no booleanp)
    :parents (ispace-validator check-dims)
    :short "Check a dimension."
    :long
    (xdoc::topstring
     (xdoc::p
      "We return @('t') if the check is successful, otherwise @('nil').")
     (xdoc::p
      "A variable must be in the environment.")
     (xdoc::p
      "Any constant is valid.")
     (xdoc::p
      "Any addition of valid dimensions is valid.")
     (xdoc::p
      "Any multiplication of valid dimensions is valid.")
     (xdoc::p
      "Any non-empty subtraction of valid dimensions is valid."))
    (dim-case
     dim
     :var (consp (omap::assoc (ispace-var-dim dim.name)
                              (ispace-senv->ispaces ienv)))
     :const t
     :add (check-dim-list dim.dims ienv)
     :mul (check-dim-list dim.dims ienv)
     :sub (and (check-dim-list dim.dims ienv)
               (consp dim.dims)))
    :measure (dim-count dim))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-dim-list ((dims dim-listp) (ienv ispace-senvp))
    :returns (yes/no booleanp)
    :parents (ispace-validator check-dims)
    :short "Check a list of dimensions."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check each dimension in turn,
       returning @('t') iff they are all valid."))
    (or (endp dims)
        (and (check-dim (car dims) ienv)
             (check-dim-list (cdr dims) ienv)))
    :measure (dim-list-count dims))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  (fty::deffixequiv-mutual check-dims))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-shapes/ispaces
  :short "Check shapes, ispaces, and lists thereof."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-shape ((shape shapep) (ienv ispace-senvp))
    :returns (yes/no booleanp)
    :parents (ispace-validator check-shapes/ispaces)
    :short "Check a shape."
    :long
    (xdoc::topstring
     (xdoc::p
      "We return @('t') if the check is successful, otherwise @('nil').")
     (xdoc::p
      "A variable must be in the environment.")
     (xdoc::p
      "A shape consisting of dimensions is valid
       iff all the dimensions are valid.")
     (xdoc::p
      "A concatenation of shapes is valid
       iff all the shapes are valid.")
     (xdoc::p
      "A splicing of ispaces is valid
       iff all the ispaces are valid."))
    (shape-case
     shape
     :var (consp (omap::assoc (ispace-var-shape shape.name)
                              (ispace-senv->ispaces ienv)))
     :dims (check-dim-list shape.dims ienv)
     :append (check-shape-list shape.shapes ienv)
     :splice (check-ispace-list shape.ispaces ienv))
    :measure (shape-count shape))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-shape-list ((shapes shape-listp) (ienv ispace-senvp))
    :returns (yes/no booleanp)
    :parents (ispace-validator check-shapes/ispaces)
    :short "Check a list of shapes."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check each shape in turn,
       returning @('t') iff they are all valid."))
    (or (endp shapes)
        (and (check-shape (car shapes) ienv)
             (check-shape-list (cdr shapes) ienv)))
    :measure (shape-list-count shapes))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-ispace ((ispace ispacep) (ienv ispace-senvp))
    :returns (yes/no booleanp)
    :parents (ispace-validator check-shapes/ispaces)
    :short "Check an ispace."
    :long
    (xdoc::topstring
     (xdoc::p
      "An ispace that is a dimension is valid
       iff the dimension is valid.")
     (xdoc::p
      "An ispace that is a shape is valid
       iff the shape is valid."))
    (ispace-case
     ispace
     :dim (check-dim ispace.dim ienv)
     :shape (check-shape ispace.shape ienv))
    :measure (ispace-count ispace))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-ispace-list ((ispaces ispace-listp) (ienv ispace-senvp))
    :returns (yes/no booleanp)
    :parents (ispace-validator check-shapes/ispaces)
    :short "Check a list of ispaces."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check each ispace in turn,
       returning @('t') iff they are all valid."))
    (or (endp ispaces)
        (and (check-ispace (car ispaces) ienv)
             (check-ispace-list (cdr ispaces) ienv)))
    :measure (ispace-list-count ispaces))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  (fty::deffixequiv-mutual check-shapes/ispaces))
