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
     Since indices have distinct dimension and shape variables,
     we use two separate maps for index variable substitutions,
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
    "Shapes and indices contain dimension and shape variables,
     but no type or term variables;
     so they need two substitution or renaming maps.
     All the variables in a shape or index are free,
     because shapes and indices have no binders.")
   (xdoc::p
    "Types contain index (dimension and shape) and type variables,
     but no term variables;
     so they need three substitution or renaming maps in general,
     but we provide separate substitution and renaming operations
     for index and type variables in types.
     Types have binders for both index and type variables,
     so the operations apply to the free index and type variables;
     when encountering bound variables,
     they are removed from the substitution and renaming maps.")
   (xdoc::p
    "We also plan to add substitution and renaming operations
     on expressions and atoms,
     involving not only index and type variables,
     but also term variables."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vars-of-index-params ((params index-param-listp))
  :returns (mv (dim-vars string-setp) (shape-vars string-setp))
  :short "Extract the sets of dimension and shape variables
          from a list of index parameters."
  (b* (((when (endp params)) (mv nil nil))
       ((mv dim-vars shape-vars) (vars-of-index-params (cdr params)))
       (param (car params)))
    (index-param-case
     param
     :dim (mv (set::insert param.name dim-vars) shape-vars)
     :shape (mv dim-vars (set::insert param.name shape-vars))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines subst-vars-in-dims
  :short "Substitute variables in dimensions and lists of dimensions."

  ;;;;;;;;;;;;;;;;;;;;

  (define subst-vars-in-dim ((dim dimp) (subst string-dim-mapp))
    :returns (new-dim dimp)
    :parents (abstract-syntax-variable-operations subst-vars-in-dims)
    :short "Substitute variables in a dimension."
    (dim-case
     dim
     :var (b* ((subst (string-dim-map-fix subst))
               (var+dim (omap::assoc dim.name subst)))
            (if var+dim
                (cdr var+dim)
              (dim-var dim.name)))
     :const (dim-const dim.value)
     :add (dim-add (subst-vars-in-dim-list dim.dims subst)))
    :measure (dim-count dim))

  ;;;;;;;;;;;;;;;;;;;;

  (define subst-vars-in-dim-list ((dims dim-listp) (subst string-dim-mapp))
    :returns (new-dims dim-listp)
    :parents (abstract-syntax-variable-operations subst-vars-in-dims)
    :short "Substitute variables in a list of dimensions."
    (cond ((endp dims) nil)
          (t (cons (subst-vars-in-dim (car dims) subst)
                   (subst-vars-in-dim-list (cdr dims) subst))))
    :measure (dim-list-count dims)

    ///

    (defret len-of-subst-vars-in-dim-list
      (equal (len new-dims)
             (len dims))
      :hints (("Goal" :induct (len dims) :in-theory (enable len)))))

  ;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual subst-vars-in-dims))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines subst-vars-in-shapes
  :short "Substitute variables in shapes and lists of shapes."

  ;;;;;;;;;;;;;;;;;;;;

  (define subst-vars-in-shape ((shape shapep)
                               (subst-dim string-dim-mapp)
                               (subst-shape string-shape-mapp))
    :returns (new-shape shapep)
    :parents (abstract-syntax-variable-operations subst-vars-in-shapes)
    :short "Substitute variables in a shape."
    (shape-case
     shape
     :var (b* ((subst-shape (string-shape-map-fix subst-shape))
               (var+shape (omap::assoc shape.name subst-shape)))
            (if var+shape
                (cdr var+shape)
              (shape-var shape.name)))
     :dim (shape-dim (subst-vars-in-dim shape.dim subst-dim))
     :dims (shape-dims (subst-vars-in-dim-list shape.dims subst-dim))
     :append (shape-append
              (subst-vars-in-shape-list shape.shapes subst-dim subst-shape))
     :splice (shape-splice
              (subst-vars-in-shape-list shape.shapes subst-dim subst-shape)))
    :measure (shape-count shape))

  ;;;;;;;;;;;;;;;;;;;;

  (define subst-vars-in-shape-list ((shapes shape-listp)
                                    (subst-dim string-dim-mapp)
                                    (subst-shape string-shape-mapp))
    :returns (new-shapes shape-listp)
    :parents (abstract-syntax-variable-operations subst-vars-in-shapes)
    :short "Substitute variables in a list of shapes."
    (cond ((endp shapes) nil)
          (t (cons (subst-vars-in-shape (car shapes)
                                        subst-dim subst-shape)
                   (subst-vars-in-shape-list (cdr shapes)
                                             subst-dim subst-shape))))
    :measure (shape-list-count shapes)

    ///

    (defret len-of-subst-vars-in-shape-list
      (equal (len new-shapes)
             (len shapes))
      :hints (("Goal" :induct (len shapes) :in-theory (enable len)))))

  ;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual subst-vars-in-shapes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subst-vars-in-index ((index indexp)
                             (subst-dim string-dim-mapp)
                             (subst-shape string-shape-mapp))
  :returns (new-index indexp)
  :short "Substitute variables in an index."
  (index-case
   index
   :dim (index-dim (subst-vars-in-dim index.dim subst-dim))
   :shape (index-shape
           (subst-vars-in-shape index.shape subst-dim subst-shape))))

;;;;;;;;;;;;;;;;;;;;

(define subst-vars-in-index-list ((indices index-listp)
                                  (subst-dim string-dim-mapp)
                                  (subst-shape string-shape-mapp))
  :returns (new-indices index-listp)
  :short "Substitute variables in a list of indices."
  (cond ((endp indices) nil)
        (t (cons
            (subst-vars-in-index (car indices) subst-dim subst-shape)
            (subst-vars-in-index-list (cdr indices) subst-dim subst-shape))))

  ///

  (defret len-of-subst-vars-in-index-list
    (equal (len new-indices)
           (len indices))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines subst-free-index-vars-in-types
  :short "Substitute free index variables in types and lists of types."

  (define subst-free-index-vars-in-type ((type typep)
                                         (subst-dim string-dim-mapp)
                                         (subst-shape string-shape-mapp))
    :returns (new-type typep)
    :parents (abstract-syntax-variable-operations
              subst-free-index-vars-in-types)
    :short "Substitute free index variables in a type."
    (type-case
     type
     :var
     (type-var type.name)
     :base
     (type-base type.type)
     :array
     (make-type-array
      :type (subst-free-index-vars-in-type type.type subst-dim subst-shape)
      :shape (subst-vars-in-shape type.shape subst-dim subst-shape))
     :fun
     (make-type-fun
      :in (subst-free-index-vars-in-type-list type.in subst-dim subst-shape)
      :out (subst-free-index-vars-in-type type.out subst-dim subst-shape))
     :forall
     (make-type-forall
      :vars type.vars
      :type (subst-free-index-vars-in-type type.type subst-dim subst-shape))
     :pi
     (b* (((mv bound-dim-vars bound-shape-vars)
           (vars-of-index-params type.params))
          (subst-dim
           (omap::delete* bound-dim-vars (string-dim-map-fix subst-dim)))
          (subst-shape
           (omap::delete* bound-shape-vars (string-shape-map-fix subst-shape))))
       (make-type-pi
        :params type.params
        :type (subst-free-index-vars-in-type type.type subst-dim subst-shape)))
     :sigma
     (b* (((mv bound-dim-vars bound-shape-vars)
           (vars-of-index-params type.params))
          (subst-dim
           (omap::delete* bound-dim-vars (string-dim-map-fix subst-dim)))
          (subst-shape
           (omap::delete* bound-shape-vars (string-shape-map-fix subst-shape))))
       (make-type-sigma
        :params type.params
        :type (subst-free-index-vars-in-type type.type subst-dim subst-shape))))
    :measure (type-count type))

  (define subst-free-index-vars-in-type-list ((types type-listp)
                                              (subst-dim string-dim-mapp)
                                              (subst-shape string-shape-mapp))
    :returns (new-types type-listp)
    :parents (abstract-syntax-variable-operations
              subst-free-index-vars-in-types)
    :short "Substitute free index variables in a list of types."
    (cond ((endp types) nil)
          (t (cons (subst-free-index-vars-in-type (car types)
                                                  subst-dim
                                                  subst-shape)
                   (subst-free-index-vars-in-type-list (cdr types)
                                                       subst-dim
                                                       subst-shape))))
    :measure (type-list-count types)

    ///

    (defret len-of-subst-free-index-vars-in-type-list
      (equal (len new-types)
             (len types))
      :hints (("Goal" :induct (len types) :in-theory (enable len)))))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual subst-free-index-vars-in-types))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines subst-free-type-vars-in-types
  :short "Substitute free type variables in types."

  (define subst-free-type-vars-in-type ((type typep) (subst string-type-mapp))
    :returns (new-type typep)
    :parents (abstract-syntax-variable-operations
              subst-free-type-vars-in-types)
    :short "Substitute free index variables in a type."
    (type-case
     type
     :var (b* ((subst (string-type-map-fix subst))
               (var+type (omap::assoc type.name subst)))
            (if var+type
                (cdr var+type)
              (type-var type.name)))
     :base (type-base type.type)
     :array (make-type-array
             :type (subst-free-type-vars-in-type type.type subst)
             :shape type.shape)
     :fun (make-type-fun
           :in (subst-free-type-vars-in-type-list type.in subst)
           :out (subst-free-type-vars-in-type type.out subst))
     :forall (b* ((bound-vars (set::mergesort (kinded-var-list->var type.vars)))
                  (subst (omap::delete* bound-vars
                                        (string-type-map-fix subst))))
               (make-type-forall
                :vars type.vars
                :type (subst-free-type-vars-in-type type.type subst)))
     :pi (make-type-pi
          :params type.params
          :type (subst-free-type-vars-in-type type.type subst))
     :sigma (make-type-sigma
             :params type.params
             :type (subst-free-type-vars-in-type type.type subst)))
    :measure (type-count type))

  (define subst-free-type-vars-in-type-list ((types type-listp)
                                             (subst string-type-mapp))
    :returns (new-types type-listp)
    :parents (abstract-syntax-variable-operations
              subst-free-type-vars-in-types)
    :short "Substitute free index variables in a list of types."
    (cond ((endp types) nil)
          (t (cons (subst-free-type-vars-in-type (car types) subst)
                   (subst-free-type-vars-in-type-list (cdr types) subst))))
    :measure (type-list-count types)

    ///

    (defret len-of-subst-free-type-vars-in-type-list
      (equal (len new-types)
             (len types))
      :hints (("Goal" :induct (len types) :in-theory (enable len)))))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual subst-free-type-vars-in-types))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines rename-vars-in-dims
  :short "Rename variables in dimensions and lists of dimensions."

  ;;;;;;;;;;;;;;;;;;;;

  (define rename-vars-in-dim ((dim dimp) (renaming string-string-mapp))
    :returns (new-dim dimp)
    :parents (abstract-syntax-variable-operations rename-vars-in-dims)
    :short "Rename variables in a dimension."
    (dim-case
     dim
     :var (b* ((renaming (string-string-map-fix renaming))
               (var+name (omap::assoc dim.name renaming)))
            (if var+name
                (dim-var (cdr var+name))
              (dim-var dim.name)))
     :const (dim-const dim.value)
     :add (dim-add (rename-vars-in-dim-list dim.dims renaming)))
    :measure (dim-count dim))

  ;;;;;;;;;;;;;;;;;;;;

  (define rename-vars-in-dim-list ((dims dim-listp)
                                   (renaming string-string-mapp))
    :returns (new-dims dim-listp)
    :parents (abstract-syntax-variable-operations rename-vars-in-dims)
    :short "Rename variables in a list of dimensions."
    (cond ((endp dims) nil)
          (t (cons (rename-vars-in-dim (car dims) renaming)
                   (rename-vars-in-dim-list (cdr dims) renaming))))
    :measure (dim-list-count dims)

    ///

    (defret len-of-rename-vars-in-dim-list
      (equal (len new-dims)
             (len dims))
      :hints (("Goal" :induct (len dims) :in-theory (enable len)))))

  ;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual rename-vars-in-dims))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines rename-vars-in-shapes
  :short "Rename variables in shapes and lists of shapes."

  ;;;;;;;;;;;;;;;;;;;;

  (define rename-vars-in-shape ((shape shapep)
                                (renaming-dim string-string-mapp)
                                (renaming-shape string-string-mapp))
    :returns (new-shape shapep)
    :parents (abstract-syntax-variable-operations rename-vars-in-shapes)
    :short "Rename variables in a shape."
    (shape-case
     shape
     :var (b* ((renaming-shape (string-string-map-fix renaming-shape))
               (var+name (omap::assoc shape.name renaming-shape)))
            (if var+name
                (shape-var (cdr var+name))
              (shape-var shape.name)))
     :dim (shape-dim (rename-vars-in-dim shape.dim renaming-dim))
     :dims (shape-dims (rename-vars-in-dim-list shape.dims renaming-dim))
     :append (shape-append (rename-vars-in-shape-list shape.shapes
                                                      renaming-dim
                                                      renaming-shape))
     :splice (shape-splice (rename-vars-in-shape-list shape.shapes
                                                      renaming-dim
                                                      renaming-shape)))
    :measure (shape-count shape))

  ;;;;;;;;;;;;;;;;;;;;

  (define rename-vars-in-shape-list ((shapes shape-listp)
                                     (renaming-dim string-string-mapp)
                                     (renaming-shape string-string-mapp))
    :returns (new-shapes shape-listp)
    :parents (abstract-syntax-variable-operations rename-vars-in-shapes)
    :short "Rename variables in a list of shapes."
    (cond ((endp shapes) nil)
          (t (cons (rename-vars-in-shape (car shapes)
                                         renaming-dim renaming-shape)
                   (rename-vars-in-shape-list (cdr shapes)
                                              renaming-dim renaming-shape))))
    :measure (shape-list-count shapes)

    ///

    (defret len-of-rename-vars-in-shape-list
      (equal (len new-shapes)
             (len shapes))
      :hints (("Goal" :induct (len shapes) :in-theory (enable len)))))

  ;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual rename-vars-in-shapes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rename-vars-in-index ((index indexp)
                              (renaming-dim string-string-mapp)
                              (renaming-shape string-string-mapp))
    :returns (new-index indexp)
    :short "Rename variables in an index."
    (index-case
     index
     :dim (index-dim (rename-vars-in-dim index.dim renaming-dim))
     :shape (index-shape
             (rename-vars-in-shape index.shape renaming-dim renaming-shape))))

;;;;;;;;;;;;;;;;;;;;

(define rename-vars-in-index-list ((indices index-listp)
                                   (renaming-dim string-string-mapp)
                                   (renaming-shape string-string-mapp))
  :returns (new-indices index-listp)
  :short "Rename variables in a list of indices."
  (cond ((endp indices) nil)
        (t (cons (rename-vars-in-index (car indices)
                                       renaming-dim
                                       renaming-shape)
                 (rename-vars-in-index-list (cdr indices)
                                            renaming-dim
                                            renaming-shape))))

  ///

  (defret len-of-rename-vars-in-index-list
    (equal (len new-indices)
           (len indices))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines rename-free-index-vars-in-types
  :short "Rename free index variables in types."

  ;;;;;;;;;;;;;;;;;;;;

  (define rename-free-index-vars-in-type ((type typep)
                                          (renaming-dim string-string-mapp)
                                          (renaming-shape string-string-mapp))
    :returns (new-type typep)
    :parents (abstract-syntax-variable-operations
              rename-free-index-vars-in-types)
    :short "Rename free index variables in a type."
    (type-case
     type
     :var
     (type-var type.name)
     :base
     (type-base type.type)
     :array
     (make-type-array
      :type (rename-free-index-vars-in-type type.type
                                            renaming-dim
                                            renaming-shape)
      :shape (rename-vars-in-shape type.shape
                                   renaming-dim
                                   renaming-shape))
     :fun
     (make-type-fun
      :in (rename-free-index-vars-in-type-list type.in
                                               renaming-dim
                                               renaming-shape)
      :out (rename-free-index-vars-in-type type.out
                                           renaming-dim
                                           renaming-shape))
     :forall
     (make-type-forall
      :vars type.vars
      :type (rename-free-index-vars-in-type type.type
                                            renaming-dim
                                            renaming-shape))
     :pi
     (b* (((mv bound-dim-vars bound-shape-vars)
           (vars-of-index-params type.params))
          (renaming-dim
           (omap::delete* bound-dim-vars
                          (string-string-map-fix renaming-dim)))
          (renaming-shape
           (omap::delete* bound-shape-vars
                          (string-string-map-fix renaming-shape))))
       (make-type-pi
        :params type.params
        :type (rename-free-index-vars-in-type type.type
                                              renaming-dim
                                              renaming-shape)))
     :sigma
     (b* (((mv bound-dim-vars bound-shape-vars)
           (vars-of-index-params type.params))
          (renaming-dim
           (omap::delete* bound-dim-vars
                          (string-string-map-fix renaming-dim)))
          (renaming-shape
           (omap::delete* bound-shape-vars
                          (string-string-map-fix renaming-shape))))
       (make-type-sigma
        :params type.params
        :type (rename-free-index-vars-in-type type.type
                                              renaming-dim
                                              renaming-shape))))
    :measure (type-count type))

  ;;;;;;;;;;;;;;;;;;;;

  (define rename-free-index-vars-in-type-list
    ((types type-listp)
     (renaming-dim string-string-mapp)
     (renaming-shape string-string-mapp))
    :returns (new-types type-listp)
    :parents (abstract-syntax-variable-operations
              rename-free-index-vars-in-types)
    :short "Rename free index variables in a list of types."
    (cond ((endp types) nil)
          (t (cons (rename-free-index-vars-in-type (car types)
                                                   renaming-dim
                                                   renaming-shape)
                   (rename-free-index-vars-in-type-list (cdr types)
                                                        renaming-dim
                                                        renaming-shape))))
    :measure (type-list-count types)

    ///

    (defret len-of-rename-free-index-vars-in-type-list
      (equal (len new-types)
             (len types))
      :hints (("Goal" :induct (len types) :in-theory (enable len)))))

  ;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual rename-free-index-vars-in-types))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines rename-free-type-vars-in-types
  :short "Rename free type variables in types."

  (define rename-free-type-vars-in-type ((type typep)
                                         (renaming string-string-mapp))
    :returns (new-type typep)
    :parents (abstract-syntax-variable-operations
              rename-free-type-vars-in-types)
    :short "Rename free type variables in a type."
    (type-case
     type
     :var (b* ((renaming (string-string-map-fix renaming))
               (var+type (omap::assoc type.name renaming)))
            (if var+type
                (type-var (cdr var+type))
              (type-var type.name)))
     :base (type-base type.type)
     :array (make-type-array
             :type (rename-free-type-vars-in-type type.type renaming)
             :shape type.shape)
     :fun (make-type-fun
           :in (rename-free-type-vars-in-type-list type.in renaming)
           :out (rename-free-type-vars-in-type type.out renaming))
     :forall (b* ((bound-vars (set::mergesort (kinded-var-list->var type.vars)))
                  (renaming (omap::delete* bound-vars
                                        (string-string-map-fix renaming))))
               (make-type-forall
                :vars type.vars
                :type (rename-free-type-vars-in-type type.type renaming)))
     :pi (make-type-pi
          :params type.params
          :type (rename-free-type-vars-in-type type.type renaming))
     :sigma (make-type-sigma
             :params type.params
             :type (rename-free-type-vars-in-type type.type renaming)))
    :measure (type-count type))

  (define rename-free-type-vars-in-type-list ((types type-listp)
                                              (renaming string-string-mapp))
    :returns (new-types type-listp)
    :parents (abstract-syntax-variable-operations
              rename-free-type-vars-in-types)
    :short "Rename free type variables in a list of types."
    (cond ((endp types) nil)
          (t (cons (rename-free-type-vars-in-type (car types) renaming)
                   (rename-free-type-vars-in-type-list (cdr types) renaming))))
    :measure (type-list-count types)

    ///

    (defret len-of-rename-free-type-vars-in-type-list
      (equal (len new-types)
             (len types))
      :hints (("Goal" :induct (len types) :in-theory (enable len)))))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual rename-free-type-vars-in-types))
