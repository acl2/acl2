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
     but also term variables."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vars-of-ispace-params ((params ispace-param-listp))
  :returns (mv (dim-vars string-setp) (shape-vars string-setp))
  :short "Extract the sets of dimension and shape variables
          from a list of ispace parameters."
  (b* (((when (endp params)) (mv nil nil))
       ((mv dim-vars shape-vars) (vars-of-ispace-params (cdr params)))
       (param (car params)))
    (ispace-param-case
     param
     :dim (mv (set::insert param.name dim-vars) shape-vars)
     :shape (mv dim-vars (set::insert param.name shape-vars))))
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
          in shapes, ispaces, types, and lists thereof."
  :types (shapes ispace ispace-list types)
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
   (type :pi
         (b* (((mv bound-dim-vars bound-shape-vars)
               (vars-of-ispace-params type.params))
              (dim-subst
               (omap::delete* bound-dim-vars
                              (string-dim-map-fix dim-subst)))
              (shape-subst
               (omap::delete* bound-shape-vars
                              (string-shape-map-fix shape-subst))))
           (make-type-pi
            :params type.params
            :type (type-subst-ispace-vars type.type dim-subst shape-subst))))
   (type :sigma
         (b* (((mv bound-dim-vars bound-shape-vars)
               (vars-of-ispace-params type.params))
              (dim-subst
               (omap::delete* bound-dim-vars
                              (string-dim-map-fix dim-subst)))
              (shape-subst
               (omap::delete* bound-shape-vars
                              (string-shape-map-fix shape-subst))))
           (make-type-sigma
            :params type.params
            :type (type-subst-ispace-vars type.type dim-subst shape-subst))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map subst-type-vars
  :short "Substitute (free) type variables in types and lists of types."
  :types (types)
  :extra-args ((subst string-type-mapp))
  :override
  ((type :var (b* ((subst (string-type-map-fix subst))
                   (var+type (omap::assoc type.name subst)))
                (if var+type
                    (cdr var+type)
                  (type-var type.name))))
   (type :forall (b* ((bound-vars
                       (set::mergesort (kinded-var-list->var type.vars)))
                      (subst (omap::delete* bound-vars
                                            (string-type-map-fix subst))))
                   (make-type-forall
                    :vars type.vars
                    :type (type-subst-type-vars type.type subst))))))

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
          in shapes, ispaces, types, and lists thereof."
  :types (shapes ispace ispace-list types)
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
   (type :pi
         (b* (((mv bound-dim-vars bound-shape-vars)
               (vars-of-ispace-params type.params))
              (dim-renam
               (omap::delete* bound-dim-vars
                              (string-string-map-fix dim-renam)))
              (shape-renam
               (omap::delete* bound-shape-vars
                              (string-string-map-fix shape-renam))))
           (make-type-pi
            :params type.params
            :type (type-rename-ispace-vars type.type dim-renam shape-renam))))
   (type :sigma
         (b* (((mv bound-dim-vars bound-shape-vars)
               (vars-of-ispace-params type.params))
              (dim-renam
               (omap::delete* bound-dim-vars
                              (string-string-map-fix dim-renam)))
              (shape-renam
               (omap::delete* bound-shape-vars
                              (string-string-map-fix shape-renam))))
           (make-type-sigma
            :params type.params
            :type (type-rename-ispace-vars type.type dim-renam shape-renam))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map rename-type-vars
  :short "Rename (free) type variables in types and lists of types."
  :types (types)
  :extra-args ((renam string-string-mapp))
  :override
  ((type :var (b* ((renam (string-string-map-fix renam))
                   (var+name (omap::assoc type.name renam)))
                (if var+name
                    (type-var (cdr var+name))
                  (type-var type.name))))
   (type :forall (b* ((bound-vars
                       (set::mergesort (kinded-var-list->var type.vars)))
                      (renam (omap::delete* bound-vars
                                            (string-string-map-fix renam))))
                   (make-type-forall
                    :vars type.vars
                    :type (type-rename-type-vars type.type renam))))))
