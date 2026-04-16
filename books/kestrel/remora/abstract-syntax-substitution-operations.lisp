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

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-substitution-operations
  :parents (abstract-syntax)
  :short "Substitution operations in ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "We defines various categories of substitution operations on ASTs.
     The substitution themselves are reified as maps."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines subst-vars-in-indices
  :short "Substitute variables in indices."
  :long
  (xdoc::topstring
   (xdoc::p
    "The substitution is specified by a map from strings to indices.
     The only variables in an index are index variables.
     All the variables in an index are free,
     because indices have no binders."))

  (define subst-vars-in-index ((index indexp) (subst string-index-mapp))
    :returns (new-index indexp)
    :parents (abstract-syntax-substitution-operations subst-vars-in-indices)
    :short "Substitute variables in an index."
    (index-case
     index
     :var (b* ((subst (string-index-map-fix subst))
               (var+index (omap::assoc index.name subst)))
            (if var+index
                (cdr var+index)
              (index-var index.name)))
     :const (index-const index.value)
     :shape (index-shape (subst-vars-in-index-list index.indices subst))
     :add (index-add (subst-vars-in-index-list index.indices subst))
     :append (index-append (subst-vars-in-index-list index.indices subst)))
    :measure (index-count index))

  (define subst-vars-in-index-list ((indices index-listp)
                                    (subst string-index-mapp))
    :returns (new-indices index-listp)
    :parents (abstract-syntax-substitution-operations subst-vars-in-indices)
    :short "Substitute variables in a list of indices."
    (cond ((endp indices) nil)
          (t (cons (subst-vars-in-index (car indices) subst)
                   (subst-vars-in-index-list (cdr indices) subst))))
    :measure (index-list-count indices)

    ///

    (defret len-of-subst-vars-in-index-list
      (equal (len new-indices)
             (len indices))
      :hints (("Goal" :induct (len indices) :in-theory (enable len)))))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual subst-vars-in-indices))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines subst-free-index-vars-in-types
  :short "Substitute free index variables in types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The substitution is specified by a map from strings to indices,
     and is performed on the free variables in the indices in the types.
     When encountering a binder of index variables,
     the bound variables are removed from the map."))

  (define subst-free-index-vars-in-type ((type typep) (subst string-index-mapp))
    :returns (new-type typep)
    :parents (abstract-syntax-substitution-operations
              subst-free-index-vars-in-types)
    :short "Substitute free index variables in a type."
    (type-case
     type
     :var (type-var type.name)
     :base (type-base type.type)
     :array (make-type-array
             :type (subst-free-index-vars-in-type type.type subst)
             :index (subst-vars-in-index type.index subst))
     :fun (make-type-fun
           :in (subst-free-index-vars-in-type-list type.in subst)
           :out (subst-free-index-vars-in-type type.out subst))
     :forall (make-type-forall
              :vars type.vars
              :type (subst-free-index-vars-in-type type.type subst))
     :pi (b* ((bound-vars (set::mergesort (sorted-var-list->var type.vars)))
              (subst (omap::delete* bound-vars
                                    (string-index-map-fix subst))))
           (make-type-pi
            :vars type.vars
            :type (subst-free-index-vars-in-type type.type subst)))
     :sigma (b* ((bound-vars (set::mergesort (sorted-var-list->var type.vars)))
                 (subst (omap::delete* bound-vars
                                       (string-index-map-fix subst))))
              (make-type-sigma
               :vars type.vars
               :type (subst-free-index-vars-in-type type.type subst))))
    :measure (type-count type))

  (define subst-free-index-vars-in-type-list ((types type-listp)
                                              (subst string-index-mapp))
    :returns (new-types type-listp)
    :parents (abstract-syntax-substitution-operations
              subst-free-index-vars-in-types)
    :short "Substitute free index variables in a list of types."
    (cond ((endp types) nil)
          (t (cons (subst-free-index-vars-in-type (car types) subst)
                   (subst-free-index-vars-in-type-list (cdr types) subst))))
    :measure (type-list-count types)

    ///

    (defret len-of-subst-free-index-vars-in-type-list
      (equal (len new-types)
             (len types))
      :hints (("Goal" :induct (len types) :in-theory (enable len)))))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual subst-free-index-vars-in-types))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines subst-free-type-vars-in-types
  :short "Substitute free type variables in types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The substitution is specified by a map from strings to types,
     and is performed on the free variables in the types.
     When encountering a binder of type variables,
     the bound variables are removed from the map."))

  (define subst-free-type-vars-in-type ((type typep) (subst string-type-mapp))
    :returns (new-type typep)
    :parents (abstract-syntax-substitution-operations
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
             :index type.index)
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
          :vars type.vars
          :type (subst-free-type-vars-in-type type.type subst))
     :sigma (make-type-sigma
             :vars type.vars
             :type (subst-free-type-vars-in-type type.type subst)))
    :measure (type-count type))

  (define subst-free-type-vars-in-type-list ((types type-listp)
                                             (subst string-type-mapp))
    :returns (new-types type-listp)
    :parents (abstract-syntax-substitution-operations
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
