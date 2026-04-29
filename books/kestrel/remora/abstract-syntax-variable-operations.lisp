; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-structural-operations")

(include-book "kestrel/fty/deffold-map" :dir :system)
(include-book "kestrel/fty/deffold-reduce" :dir :system)
(include-book "kestrel/fty/string-set" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-variable-operations
  :parents (abstract-syntax)
  :short "Operations on ASTs related to variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "These include substitutions of variables with other ASTs,
     as well as variable renamings.")
   (xdoc::p
    "The substitutions are represented as maps
     from strings (variable names) to ASTs.
     Since ispaces have distinct dimension and shape variables,
     we use two separate maps for ispace variable substitutions,
     one for dimension variables and one for shape variables.")
   (xdoc::p
    "The renamings are represented as maps from strings to strings.")
   (xdoc::p
    "Dimensions contain dimension variables,
     but no shape or type or term variables;
     so they only need one substitusion or renaming map
     All the variables in a dimension are free,
     because dimensions have no binders.")
   (xdoc::p
    "Shapes and ispaces contain dimension and shape variables,
     but no type or term variables;
     so they need two substitution or renaming maps.
     All the variables in a shape or ispace are free,
     because shapes and ispaces have no binders.")
   (xdoc::p
    "Types contain ispace (dimension and shape) and type variables,
     but no term variables;
     so they need three substitution or renaming maps in general,
     but we provide separate substitution and renaming operations
     for ispace and type variables in types.
     Types have binders for both ispace and type variables,
     so the operations apply to the free ispace and type variables;
     when encountering bound variables,
     they are removed from the substitution and renaming maps.")
   (xdoc::p
    "We also plan to add substitution and renaming operations
     on expressions and atoms,
     involving not only ispace and type variables,
     but also term variables.")
   (xdoc::p
    "We need to double-check, and possibly revise,
     the treatment of the boxing and unboxing constructs."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim/shape-names-of-ispace-vars ((vars ispace-var-listp))
  :returns (mv (dim-vars string-setp) (shape-vars string-setp))
  :short "Extract the sets of dimension and shape variables
          from a list of ispace variables."
  (b* (((when (endp vars)) (mv nil nil))
       ((mv dim-vars shape-vars) (dim/shape-names-of-ispace-vars (cdr vars)))
       (param (car vars)))
    (ispace-var-case
     param
     :dim (mv (set::insert param.name dim-vars) shape-vars)
     :shape (mv dim-vars (set::insert param.name shape-vars))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom/array-names-of-type-vars ((vars type-var-listp))
  :returns (mv (atom-vars string-setp) (array-vars string-setp))
  :short "Extract the sets of atom and array variables
          from a list of type variables."
  (b* (((when (endp vars)) (mv nil nil))
       ((mv atom-vars array-vars) (atom/array-names-of-type-vars (cdr vars)))
       (var (car vars)))
    (type-var-case
     var
     :atom (mv (set::insert var.name atom-vars) array-vars)
     :array (mv atom-vars (set::insert var.name array-vars))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map subst-dim-vars
  :short "Substitute dimension variables in dimensions and lists of dimensions."
  :types (dims)
  :extra-args ((subst string-dim-mapp))
  :override
  ((dim :var (b* ((subst (string-dim-map-fix subst))
                  (var+dim (omap::assoc dim.name subst)))
               (if var+dim
                   (cdr var+dim)
                 (dim-var dim.name))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map subst-ispace-vars
  :short "Substitute (free) ispace (i.e. dimension and shape) variables
          in shapes, ispaces, (atom and array) types, and lists thereof."
  :types (shapes
          ispace
          ispace-list
          atom/array-types
          atom-type-list
          type
          type-list)
  :extra-args ((dim-subst string-dim-mapp)
               (shape-subst string-shape-mapp))
  :override
  ((shape :var (b* ((shape-subst (string-shape-map-fix shape-subst))
                    (var+shape (omap::assoc shape.name shape-subst)))
                 (if var+shape
                     (cdr var+shape)
                   (shape-var shape.name))))
   (shape :dim (shape-dim (dim-subst-dim-vars shape.dim dim-subst)))
   (shape :dims (shape-dims (dim-list-subst-dim-vars shape.dims dim-subst)))
   (ispace :dim (ispace-dim (dim-subst-dim-vars ispace.dim dim-subst)))
   (atom-type :pi
              (b* (((mv bound-dim-vars bound-shape-vars)
                    (dim/shape-names-of-ispace-vars atom-type.params))
                   (dim-subst
                    (omap::delete* bound-dim-vars
                                   (string-dim-map-fix dim-subst)))
                   (shape-subst
                    (omap::delete* bound-shape-vars
                                   (string-shape-map-fix shape-subst))))
                (make-atom-type-pi
                 :params atom-type.params
                 :body (array-type-subst-ispace-vars atom-type.body
                                                     dim-subst
                                                     shape-subst))))
   (atom-type :sigma
              (b* (((mv bound-dim-vars bound-shape-vars)
                    (dim/shape-names-of-ispace-vars atom-type.params))
                   (dim-subst
                    (omap::delete* bound-dim-vars
                                   (string-dim-map-fix dim-subst)))
                   (shape-subst
                    (omap::delete* bound-shape-vars
                                   (string-shape-map-fix shape-subst))))
                (make-atom-type-sigma
                 :params atom-type.params
                 :body (array-type-subst-ispace-vars atom-type.body
                                                     dim-subst
                                                     shape-subst))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map subst-type-vars
  :short "Substitute (free) type variables
          in (atom and array) types and lists thereof."
  :types (atom/array-types
          atom-type-list
          type
          type-list)
  :extra-args ((atom-subst string-atomtype-mapp)
               (array-subst string-arraytype-mapp))
  :override
  ((atom-type :var
              (b* ((atom-subst (string-atomtype-map-fix atom-subst))
                   (var+type (omap::assoc atom-type.name atom-subst)))
                (if var+type
                    (cdr var+type)
                  (atom-type-var atom-type.name))))
   (atom-type :forall
              (b* (((mv bound-atom-vars bound-array-vars)
                    (atom/array-names-of-type-vars atom-type.params))
                   (atom-subst
                    (omap::delete* bound-atom-vars
                                   (string-atomtype-map-fix atom-subst)))
                   (array-subst
                    (omap::delete* bound-array-vars
                                   (string-arraytype-map-fix array-subst))))
                (make-atom-type-forall
                 :params atom-type.params
                 :body (array-type-subst-type-vars atom-type.body
                                                   atom-subst
                                                   array-subst))))
   (array-type :var
               (b* ((array-subst (string-arraytype-map-fix array-subst))
                    (var+type (omap::assoc array-type.name array-subst)))
                 (if var+type
                     (cdr var+type)
                   (array-type-var array-type.name))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map rename-dim-vars
  :short "Rename dimension variables in dimensions and lists of dimensions."
  :types (dims)
  :extra-args ((renam string-string-mapp))
  :override
  ((dim :var (b* ((renam (string-string-map-fix renam))
                  (var+name (omap::assoc dim.name renam)))
               (if var+name
                   (dim-var (cdr var+name))
                 (dim-var dim.name))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map rename-ispace-vars
  :short "Rename (free) ispace (i.e. dimension and shape) variables
          in shapes, ispaces, (atom and array) types, and lists thereof."
  :types (shapes
          ispace
          ispace-list
          atom/array-types
          atom-type-list
          type
          type-list)
  :extra-args ((dim-renam string-string-mapp)
               (shape-renam string-string-mapp))
  :override
  ((shape :var (b* ((shape-renam (string-string-map-fix shape-renam))
                    (var+name (omap::assoc shape.name shape-renam)))
                 (if var+name
                     (shape-var (cdr var+name))
                   (shape-var shape.name))))
   (shape :dim (shape-dim (dim-rename-dim-vars shape.dim dim-renam)))
   (shape :dims (shape-dims (dim-list-rename-dim-vars shape.dims dim-renam)))
   (ispace :dim (ispace-dim (dim-rename-dim-vars ispace.dim dim-renam)))
   (atom-type :pi
              (b* (((mv bound-dim-vars bound-shape-vars)
                    (dim/shape-names-of-ispace-vars atom-type.params))
                   (dim-renam
                    (omap::delete* bound-dim-vars
                                   (string-string-map-fix dim-renam)))
                   (shape-renam
                    (omap::delete* bound-shape-vars
                                   (string-string-map-fix shape-renam))))
                (make-atom-type-pi
                 :params atom-type.params
                 :body (array-type-rename-ispace-vars atom-type.body
                                                      dim-renam
                                                      shape-renam))))
   (atom-type :sigma
              (b* (((mv bound-dim-vars bound-shape-vars)
                    (dim/shape-names-of-ispace-vars atom-type.params))
                   (dim-renam
                    (omap::delete* bound-dim-vars
                                   (string-string-map-fix dim-renam)))
                   (shape-renam
                    (omap::delete* bound-shape-vars
                                   (string-string-map-fix shape-renam))))
                (make-atom-type-sigma
                 :params atom-type.params
                 :body (array-type-rename-ispace-vars atom-type.body
                                                      dim-renam
                                                      shape-renam))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map rename-type-vars
  :short "Rename (free) type variables
          in (atom and array) types and lists thereof."
  :types (atom/array-types
          atom-type-list
          type
          type-list)
  :extra-args ((atom-renam string-string-mapp)
               (array-renam string-string-mapp))
  :override
  ((atom-type :var
              (b* ((atom-renam (string-string-map-fix atom-renam))
                   (var+name (omap::assoc atom-type.name atom-renam)))
                (if var+name
                    (atom-type-var (cdr var+name))
                  (atom-type-var atom-type.name))))
   (atom-type :forall
              (b* (((mv bound-atom-vars bound-array-vars)
                    (atom/array-names-of-type-vars atom-type.params))
                   (atom-renam
                    (omap::delete* bound-atom-vars
                                   (string-string-map-fix atom-renam)))
                   (array-renam
                    (omap::delete* bound-array-vars
                                   (string-string-map-fix array-renam))))
                (make-atom-type-forall
                 :params atom-type.params
                 :body (array-type-rename-type-vars atom-type.body
                                                    atom-renam
                                                    array-renam))))
   (array-type :var
               (b* ((array-renam (string-string-map-fix array-renam))
                    (var+name (omap::assoc array-type.name array-renam)))
                 (if var+name
                     (array-type-var (cdr var+name))
                   (array-type-var array-type.name))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce free-ispace-vars
  :short "Set of free ispace variables in
          ispaces,
          (atom and array) types,
          variables with types,
          expressions,
          atoms,
          and lists thereof."
  :types (dims
          shapes
          ispace
          ispace-list
          atom/array-types
          atom-type-list
          type
          type-list
          var+type
          exprs/atoms)
  :result ispace-var-setp
  :default nil
  :combine set::union
  :override
  ((dim :var (set::insert (ispace-var-dim dim.name) nil))
   (shape :var (set::insert (ispace-var-shape shape.name) nil))
   (atom-type :pi
              (set::difference (array-type-free-ispace-vars atom-type.body)
                               (set::mergesort atom-type.params)))
   (atom-type :sigma
              (set::difference (array-type-free-ispace-vars atom-type.body)
                               (set::mergesort atom-type.params)))
   (expr :unbox
         (set::union (expr-free-ispace-vars expr.target)
                     (set::difference (expr-free-ispace-vars expr.body)
                                      (set::mergesort expr.ispaces))))
   (atom :ispace-abs
         (set::difference (expr-free-ispace-vars atom.body)
                          (set::mergesort atom.params)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce free-type-vars
  :short "Set of free type variables in
          (atom and array) types,
          variables with types,
          expressions,
          atoms,
          and lists thereof."
  :types (atom/array-types
          atom-type-list
          type
          type-list
          var+type
          exprs/atoms)
  :result type-var-setp
  :default nil
  :combine set::union
  :override
  ((atom-type :var (set::insert (type-var-atom atom-type.name) nil))
   (atom-type :forall (set::difference (array-type-free-type-vars atom-type.body)
                                       (set::mergesort atom-type.params)))
   (array-type :var (set::insert (type-var-array array-type.name) nil))
   (atom :type-abs (set::difference (expr-free-type-vars atom.body)
                                    (set::mergesort atom.params)))))
