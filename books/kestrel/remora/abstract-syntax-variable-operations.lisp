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

(include-book "kestrel/fty/string-string-map" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-variable-operations
  :parents (abstract-syntax)
  :short "Operations on ASTs related to variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "These include substitutions of variables with other ASTs,
     as well as variable renamings."))
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
    :parents (abstract-syntax-variable-operations subst-vars-in-indices)
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
    :parents (abstract-syntax-variable-operations subst-vars-in-indices)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
    :parents (abstract-syntax-variable-operations
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
    :parents (abstract-syntax-variable-operations
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(defines rename-vars-in-indices
  :short "Rename variables in indices."
  :long
  (xdoc::topstring
   (xdoc::p
    "The renaming is specified by a map from strings to strings.
     The only variables in an index are index variables.
     All the variables in an index are free,
     because indices have no binders."))

  (define rename-vars-in-index ((index indexp) (renaming string-string-mapp))
    :returns (new-index indexp)
    :parents (abstract-syntax-variable-operations rename-vars-in-indices)
    :short "Rename variables in an index."
    (index-case
     index
     :var (b* ((renaming (string-string-map-fix renaming))
               (var+name (omap::assoc index.name renaming)))
            (if var+name
                (index-var (cdr var+name))
              (index-var index.name)))
     :const (index-const index.value)
     :shape (index-shape (rename-vars-in-index-list index.indices renaming))
     :add (index-add (rename-vars-in-index-list index.indices renaming))
     :append (index-append (rename-vars-in-index-list index.indices renaming)))
    :measure (index-count index))

  (define rename-vars-in-index-list ((indices index-listp)
                                     (renaming string-string-mapp))
    :returns (new-indices index-listp)
    :parents (abstract-syntax-variable-operations rename-vars-in-indices)
    :short "Rename variables in a list of indices."
    (cond ((endp indices) nil)
          (t (cons (rename-vars-in-index (car indices) renaming)
                   (rename-vars-in-index-list (cdr indices) renaming))))
    :measure (index-list-count indices)

    ///

    (defret len-of-rename-vars-in-index-list
      (equal (len new-indices)
             (len indices))
      :hints (("Goal" :induct (len indices) :in-theory (enable len)))))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual rename-vars-in-indices))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines rename-free-index-vars-in-types
  :short "Rename free index variables in types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The reanming is specified by a map from strings to strings,
     and is performed on the free variables in the indices in the types.
     When encountering a binder of index variables,
     the bound variables are removed from the map."))

  (define rename-free-index-vars-in-type ((type typep)
                                          (renaming string-string-mapp))
    :returns (new-type typep)
    :parents (abstract-syntax-variable-operations
              rename-free-index-vars-in-types)
    :short "Rename free index variables in a type."
    (type-case
     type
     :var (type-var type.name)
     :base (type-base type.type)
     :array (make-type-array
             :type (rename-free-index-vars-in-type type.type renaming)
             :index (rename-vars-in-index type.index renaming))
     :fun (make-type-fun
           :in (rename-free-index-vars-in-type-list type.in renaming)
           :out (rename-free-index-vars-in-type type.out renaming))
     :forall (make-type-forall
              :vars type.vars
              :type (rename-free-index-vars-in-type type.type renaming))
     :pi (b* ((bound-vars (set::mergesort (sorted-var-list->var type.vars)))
              (renaming (omap::delete* bound-vars
                                    (string-string-map-fix renaming))))
           (make-type-pi
            :vars type.vars
            :type (rename-free-index-vars-in-type type.type renaming)))
     :sigma (b* ((bound-vars (set::mergesort (sorted-var-list->var type.vars)))
                 (renaming (omap::delete* bound-vars
                                       (string-string-map-fix renaming))))
              (make-type-sigma
               :vars type.vars
               :type (rename-free-index-vars-in-type type.type renaming))))
    :measure (type-count type))

  (define rename-free-index-vars-in-type-list ((types type-listp)
                                               (renaming string-string-mapp))
    :returns (new-types type-listp)
    :parents (abstract-syntax-variable-operations
              rename-free-index-vars-in-types)
    :short "Rename free index variables in a list of types."
    (cond ((endp types) nil)
          (t (cons (rename-free-index-vars-in-type (car types) renaming)
                   (rename-free-index-vars-in-type-list (cdr types) renaming))))
    :measure (type-list-count types)

    ///

    (defret len-of-rename-free-index-vars-in-type-list
      (equal (len new-types)
             (len types))
      :hints (("Goal" :induct (len types) :in-theory (enable len)))))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual rename-free-index-vars-in-types))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines rename-free-type-vars-in-types
  :short "Rename free type variables in types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The renaming is specified by a map from strings to strings,
     and is performed on the free variables in the types.
     When encountering a binder of type variables,
     the bound variables are removed from the map."))

  (define rename-free-type-vars-in-type ((type typep)
                                         (renaming string-string-mapp))
    :returns (new-type typep)
    :parents (abstract-syntax-variable-operations
              rename-free-type-vars-in-types)
    :short "Reanem free index variables in a type."
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
             :index type.index)
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
          :vars type.vars
          :type (rename-free-type-vars-in-type type.type renaming))
     :sigma (make-type-sigma
             :vars type.vars
             :type (rename-free-type-vars-in-type type.type renaming)))
    :measure (type-count type))

  (define rename-free-type-vars-in-type-list ((types type-listp)
                                              (renaming string-string-mapp))
    :returns (new-types type-listp)
    :parents (abstract-syntax-variable-operations
              rename-free-type-vars-in-types)
    :short "Rename free index variables in a list of types."
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
