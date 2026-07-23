; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "evaluation")
(include-book "unique-names")

(include-book "kestrel/utilities/defopeners" :dir :system)

(include-book "portcullis")
(include-book "oset-omaps")

(local (include-book "std/omaps/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ renaming-evaluation
  :parents (unique-names-validation)
  :short "Evaluation is invariant under variable renaming:
          the structurally recursive levels."
  :long
  (xdoc::topstring
   (xdoc::p
    "This book begins the proof of
     @('eval-top-expr-of-expr-uniquify-names')
     (see @(see unique-names-validation)) with its structurally recursive
     levels: the evaluation of dimensions, shapes, ispaces, and types,
     under a renaming of the ispace variables.
     The values produced by the first three levels (integers, lists of
     naturals, ispace values) contain no abstract syntax, so evaluating a
     renamed AST yields results literally equal to the original ones.
     Type values may embed abstract syntax (the bodies of universal,
     product, and sum types) along with dynamic environments captured
     for its free variables, so evaluating a renamed type yields the
     @('renaming') of the original type value, where renaming a type value
     (see @(tsee type-value-rename-ispace-vars)) renames the abstract
     syntax embedded in it and, recursively, the captured environments.")
   (xdoc::p
    "The correspondence between the two dynamic environments is expressed
     by the relations @(tsee denv-ispace-vars-renamed-p) and
     @(tsee denv-type-vars-ispace-renamed-p): looking up (the renaming of)
     a variable in the new environment yields the (renaming of the)
     association of the original variable in the old environment.  These
     relations hold, in particular, when the new environment is obtained
     from the old one by injectively renaming its keys and values; phrasing
     the theorems with relations instead of key-renaming functions keeps
     them independent of how the environments are built up during the
     eventual induction over expression evaluation.")
   (xdoc::p
    "The type-level theorems are proved in two phases: first that the
     renamed evaluation errs exactly when the original does, and then, with
     the first phase available as rewrite rules, that on success the
     renamed evaluation yields the renamed value.  (A single combined
     statement makes the inductive hypotheses equalities that the prover
     does not reliably use to relate the error tests of the two
     evaluations.)")
   (xdoc::p
    "The same development is then carried out for renamings of type
     variables: the evaluation of dimensions, shapes, and ispaces is
     unchanged (it depends on the environment only through the
     ispace-variable map, which such a renaming does not touch), and the
     evaluation of a type with renamed type variables yields the
     corresponding renaming of the type value.")
   (xdoc::p
    "For expression values, which embed abstract syntax in lambda values
     and boxes as well as type values in several places, this book provides
     the value side of the renamings of all the namespaces: renaming
     expression variables (@(tsee expr-value-rename-expr-vars)), ispace
     variables (@(tsee expr-value-rename-ispace-vars)), and type variables
     (@(tsee expr-value-rename-type-vars)) in expression values, and proofs
     that the operations on values used by the evaluator's
     rank-polymorphic application machinery --- the dimension operations
     @(tsee check-dims-of-expr-value), @(tsee expr-value-wfp), @(tsee
     dims-of-expr-value), and @(tsee cells-at-depth-in-expr-value), the
     array builders @(tsee expr-value-with-empty-dim) and @(tsee
     expr-value-with-nonempty-dims), and the frame lifting @(tsee
     lift-expr-value-to-frame) --- commute with each of these renamings.")
   (xdoc::p
    "The book also proves the preservation of the environment relations
     under the extensions of the dynamic environment performed by the
     evaluation of binds: extensions in namespaces other than the one a
     relation constrains preserve it unconditionally, while extensions in
     the constrained namespace require the renaming to be injective
     (see @(tsee rename-var-string-injective-p)), a property that the
     uniquification traversal will eventually discharge from the freshness
     of the names it generates.")
   (xdoc::p
    "The final sections begin the treatment of the environment relations
     under the renamings reduced at binders (as performed by lambda
     applications, which remove the parameters from the renamings in
     scope): the renaming of an environment is related to the environment
     itself (establishing the relations for the captured environment of an
     applied closure), and the ispace and expression relations under the
     full maps carry over to the relations under the reduced maps when the
     bound variables are added to both environments.  For the expression
     relation, whose entries carry renamed values, the transition rests on
     a stability property: a renaming depends only on its associations at
     the free expression variables of the thing renamed (see @(tsee
     expr-value-free-expr-vars) for the value-level notion, which includes
     the captured environments), so reducing the map by bound names that
     do not occur among those free variables --- as guaranteed by the
     freshness of the uniquified names --- does not change the renaming.
     Still to come: the analogous stability and transitions for the
     ispace- and type-variable renamings of type and expression values,
     and the main mutual induction over
     @(see eval-exprs/atoms/binds)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffixequiv rename-var-string
  :hints (("Goal" :in-theory (enable rename-var-string))))

(define rename-ispace-var ((var ispace-varp)
                           (dim-renam string-string-mapp)
                           (shape-renam string-string-mapp))
  :returns (new-var ispace-varp)
  :short "Rename an ispace variable:
          a dimension variable through the dimension renaming,
          a shape variable through the shape renaming."
  (ispace-var-case
   var
   :dim (ispace-var-dim (rename-var-string var.name dim-renam))
   :shape (ispace-var-shape (rename-var-string var.name shape-renam)))

  ///

  (fty::deffixequiv rename-ispace-var))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::defun-sk denv-ispace-vars-renamed-p (new-denv denv dim-renam shape-renam)
  (forall (var)
          (implies
           (ispace-varp var)
           (equal (omap::assoc (rename-ispace-var var dim-renam shape-renam)
                               (ispace-denv->ispaces new-denv))
                  (b* ((pair (omap::assoc var (ispace-denv->ispaces denv))))
                    (and pair
                         (cons (rename-ispace-var var dim-renam shape-renam)
                               (cdr pair)))))))
  :rewrite :direct)

(in-theory (disable denv-ispace-vars-renamed-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Evaluation of renamed dimensions.

(defthm-eval-dims-flag
  (defthm eval-dim-of-dim-rename-dim-vars
    (implies (denv-ispace-vars-renamed-p new-denv denv dim-renam shape-renam)
             (equal (eval-dim (dim-rename-dim-vars dim dim-renam) new-denv)
                    (eval-dim dim denv)))
    :flag eval-dim)
  (defthm eval-dim-list-of-dim-list-rename-dim-vars
    (implies (denv-ispace-vars-renamed-p new-denv denv dim-renam shape-renam)
             (equal (eval-dim-list (dim-list-rename-dim-vars dims dim-renam)
                                   new-denv)
                    (eval-dim-list dims denv)))
    :flag eval-dim-list)
  :hints
  (("Goal"
    :in-theory (enable eval-dim
                       eval-dim-list
                       dim-rename-dim-vars
                       dim-list-rename-dim-vars
                       rename-var-string
                       rename-ispace-var
                       ispace-denv-lookup-ispace))
   (and acl2::stable-under-simplificationp
        '(:use ((:instance denv-ispace-vars-renamed-p-necc
                           (var (ispace-var-dim (dim-var->name dim)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Evaluation of renamed shapes and ispaces.

(defthm-eval-shapes/ispaces-flag
  (defthm eval-shape-of-shape-rename-ispace-vars
    (implies (denv-ispace-vars-renamed-p new-denv denv dim-renam shape-renam)
             (equal (eval-shape (shape-rename-ispace-vars shape
                                                          dim-renam
                                                          shape-renam)
                                new-denv)
                    (eval-shape shape denv)))
    :flag eval-shape)
  (defthm eval-shape-list-of-shape-list-rename-ispace-vars
    (implies (denv-ispace-vars-renamed-p new-denv denv dim-renam shape-renam)
             (equal (eval-shape-list (shape-list-rename-ispace-vars shapes
                                                                    dim-renam
                                                                    shape-renam)
                                     new-denv)
                    (eval-shape-list shapes denv)))
    :flag eval-shape-list)
  (defthm eval-ispace-of-ispace-rename-ispace-vars
    (implies (denv-ispace-vars-renamed-p new-denv denv dim-renam shape-renam)
             (equal (eval-ispace (ispace-rename-ispace-vars ispace
                                                            dim-renam
                                                            shape-renam)
                                 new-denv)
                    (eval-ispace ispace denv)))
    :flag eval-ispace)
  (defthm eval-ispace-list-of-ispace-list-rename-ispace-vars
    (implies (denv-ispace-vars-renamed-p new-denv denv dim-renam shape-renam)
             (equal (eval-ispace-list (ispace-list-rename-ispace-vars ispaces
                                                                      dim-renam
                                                                      shape-renam)
                                      new-denv)
                    (eval-ispace-list ispaces denv)))
    :flag eval-ispace-list)
  :hints
  (("Goal"
    :in-theory (enable eval-shape
                       eval-shape-list
                       eval-ispace
                       eval-ispace-list
                       shape-rename-ispace-vars
                       shape-list-rename-ispace-vars
                       ispace-rename-ispace-vars
                       ispace-list-rename-ispace-vars
                       rename-var-string
                       rename-ispace-var
                       ispace-denv-lookup-ispace))
   (and acl2::stable-under-simplificationp
        '(:use ((:instance denv-ispace-vars-renamed-p-necc
                           (var (ispace-var-shape
                                 (shape-var->name shape)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Renaming of ispace variables in type values.
;
; The type values of universal, product, and sum types embed abstract syntax
; (the body of the abstraction) together with a captured dynamic environment
; for its free variables, so evaluating a renamed type does not in general
; yield a value equal to the original: it yields the RENAMING of the original
; value, where renaming a type value renames the abstract syntax embedded in
; it, mirroring exactly what AST-RENAME-ISPACE-VARS does to the corresponding
; types (in particular, reducing the renaming at Pi and Sigma binders), and
; renames the captured environment: the keys of its ispace map (whose values
; are ground), and, recursively, the type values in its type-variable map
; (whose keys are not ispace variables and are thus untouched).  The captured
; environment is renamed under the full (unreduced) maps, because it binds
; the variables that are free in the whole abstraction, i.e. outside the
; scope of the parameters.

(define ispace-var-ispace-value-map-rename-ispace-vars
  ((map ispace-var-ispace-value-mapp)
   (dim-renam string-string-mapp)
   (shape-renam string-string-mapp))
  :returns (new-map ispace-var-ispace-value-mapp)
  :short "Rename the ispace variable keys of
          a map from ispace variables to ispace values."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ispace values are ground, so only the keys are renamed."))
  :measure (omap::size (ispace-var-ispace-value-map-fix map))
  :hints (("Goal" :in-theory (enable omap::size)))
  (b* ((map (ispace-var-ispace-value-map-fix map))
       ((when (omap::emptyp map)) nil)
       ((mv var ival) (omap::head map)))
    (omap::update (rename-ispace-var var dim-renam shape-renam)
                  ival
                  (ispace-var-ispace-value-map-rename-ispace-vars
                   (omap::tail map) dim-renam shape-renam)))
  :verify-guards :after-returns

  ///

  (fty::deffixequiv ispace-var-ispace-value-map-rename-ispace-vars))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-denv-rename-ispace-vars ((denv ispace-denvp)
                                        (dim-renam string-string-mapp)
                                        (shape-renam string-string-mapp))
  :returns (new-denv ispace-denvp)
  :short "Rename ispace variables in an ispace dynamic environment."
  (change-ispace-denv
   denv
   :ispaces (ispace-var-ispace-value-map-rename-ispace-vars
             (ispace-denv->ispaces denv) dim-renam shape-renam))

  ///

  (fty::deffixequiv ispace-denv-rename-ispace-vars))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines type-value-rename-ispace-vars
  ;; The flag function is used by theorems in other books
  ;; (see unique-names-validation.lisp).
  :flag-local nil

  (define type-value-rename-ispace-vars ((tval type-valuep)
                                         (dim-renam string-string-mapp)
                                         (shape-renam string-string-mapp))
    :returns (new-tval type-valuep)
    :parents (renaming-evaluation type-value-rename-ispace-vars)
    :short "Rename ispace variables in a type value."
    :measure (type-value-count tval)
    (type-value-case
     tval
     :base (type-value-fix tval)
     :array (make-type-value-array
             :elem (type-value-rename-ispace-vars tval.elem
                                                  dim-renam
                                                  shape-renam)
             :dims tval.dims)
     :fun (make-type-value-fun
           :in (type-value-list-rename-ispace-vars tval.in
                                                   dim-renam
                                                   shape-renam)
           :out (type-value-rename-ispace-vars tval.out
                                               dim-renam
                                               shape-renam))
     :forall (make-type-value-forall
              :param tval.param
              :body (type-rename-ispace-vars tval.body dim-renam shape-renam)
              :denv (type-denv-rename-ispace-vars tval.denv
                                                  dim-renam
                                                  shape-renam))
     :pi (b* (((mv & & body-dim-renam body-shape-renam)
               (dim/shape-rename-remove-bound (set::insert tval.param nil)
                                              dim-renam
                                              shape-renam)))
           (make-type-value-pi
            :param tval.param
            :body (type-rename-ispace-vars tval.body
                                           body-dim-renam
                                           body-shape-renam)
            :denv (type-denv-rename-ispace-vars tval.denv
                                                dim-renam
                                                shape-renam)))
     :sigma (b* (((mv & & body-dim-renam body-shape-renam)
                  (dim/shape-rename-remove-bound (set::insert tval.param nil)
                                                 dim-renam
                                                 shape-renam)))
              (make-type-value-sigma
               :param tval.param
               :body (type-rename-ispace-vars tval.body
                                              body-dim-renam
                                              body-shape-renam)
               :denv (type-denv-rename-ispace-vars tval.denv
                                                   dim-renam
                                                   shape-renam)))))

  (define type-value-list-rename-ispace-vars ((tvals type-value-listp)
                                              (dim-renam string-string-mapp)
                                              (shape-renam string-string-mapp))
    :returns (new-tvals type-value-listp)
    :parents (renaming-evaluation type-value-rename-ispace-vars)
    :short "Rename ispace variables in a list of type values."
    :measure (type-value-list-count tvals)
    (if (endp tvals)
        nil
      (cons (type-value-rename-ispace-vars (car tvals) dim-renam shape-renam)
            (type-value-list-rename-ispace-vars (cdr tvals)
                                                dim-renam
                                                shape-renam))))

  (define type-var-type-value-map-rename-ispace-vars
    ((map type-var-type-value-mapp)
     (dim-renam string-string-mapp)
     (shape-renam string-string-mapp))
    :returns (new-map type-var-type-value-mapp)
    :parents (renaming-evaluation type-value-rename-ispace-vars)
    :short "Rename ispace variables in the type values of
            a map from type variables to type values."
    :long
    (xdoc::topstring
     (xdoc::p
      "The keys are type variables, untouched by an ispace renaming,
       so only the values are renamed."))
    :measure (type-var-type-value-map-count map)
    (b* ((map (type-var-type-value-map-fix map))
         ((when (omap::emptyp map)) nil)
         ((mv var tval) (omap::head map)))
      (omap::update var
                    (type-value-rename-ispace-vars tval dim-renam shape-renam)
                    (type-var-type-value-map-rename-ispace-vars
                     (omap::tail map) dim-renam shape-renam))))

  (define type-denv-rename-ispace-vars ((denv type-denvp)
                                        (dim-renam string-string-mapp)
                                        (shape-renam string-string-mapp))
    :returns (new-denv type-denvp)
    :parents (renaming-evaluation type-value-rename-ispace-vars)
    :short "Rename ispace variables in a type dynamic environment."
    :measure (type-denv-count denv)
    (make-type-denv
     :ienv (ispace-denv-rename-ispace-vars (type-denv->ienv denv)
                                           dim-renam
                                           shape-renam)
     :types (type-var-type-value-map-rename-ispace-vars
             (type-denv->types denv) dim-renam shape-renam)))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual type-value-rename-ispace-vars)

  ;; (defret not-reserrp-of-type-value-rename-ispace-vars
  ;;   (not (reserrp new-tval))
  ;;   :fn type-value-rename-ispace-vars
  ;;   :hints (("Goal" :in-theory (enable not-reserrp-when-type-valuep))))

  ;; (defret not-reserrp-of-type-value-list-rename-ispace-vars
  ;;   (not (reserrp new-tvals))
  ;;   :fn type-value-list-rename-ispace-vars
  ;;   :hints (("Goal" :in-theory (enable not-reserrp-when-type-value-listp))))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The type-variable map of the new environment associates, to each type
; variable (whose name is untouched by an ispace renaming), the renaming of
; the type value associated to it in the old environment.

(acl2::defun-sk denv-type-vars-ispace-renamed-p (new-denv denv
                                                          dim-renam
                                                          shape-renam)
  (forall (var)
          (implies
           (type-varp var)
           (equal (omap::assoc var (type-denv->types new-denv))
                  (b* ((pair (omap::assoc var (type-denv->types denv))))
                    (and pair
                         (cons var
                               (type-value-rename-ispace-vars
                                (cdr pair) dim-renam shape-renam)))))))
  :rewrite :direct)

(in-theory (disable denv-type-vars-ispace-renamed-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Support for the type-level theorems below.
;
; Evaluating a universal, product, or sum type captures, in the resulting
; type value, the restriction of the dynamic environment to the free
; variables of the type; evaluating the RENAMED type restricts the new
; environment to the free variables of the renamed type.  The lemmas in
; this section characterize those free variables --- the free ispace
; variables of a renamed type are the elementwise renamings of the free
; ispace variables of the original type, provided the renaming captures no
; variables, while the free type variables are untouched by an ispace
; renaming --- and commute environment restriction with environment
; renaming: restricting the new environment to the renamed free variables
; yields the renaming of the restriction of the old environment to the
; original free variables.

; Elementwise renaming of a set of ispace variables.

(define ispace-var-set-rename-ispace-vars ((vars ispace-var-setp)
                                           (dim-renam string-string-mapp)
                                           (shape-renam string-string-mapp))
  :returns (new-vars ispace-var-setp)
  :short "Rename each ispace variable in a set."
  (b* (((when (set::emptyp (ispace-var-set-fix vars))) nil))
    (set::insert (rename-ispace-var (set::head vars) dim-renam shape-renam)
                 (ispace-var-set-rename-ispace-vars (set::tail vars)
                                                    dim-renam
                                                    shape-renam)))
  :prepwork ((local (in-theory (enable emptyp-of-ispace-var-set-fix))))
  :verify-guards :after-returns)

(defrule in-of-rename-ispace-var-of-ispace-var-set-rename-ispace-vars
  (implies (and (ispace-var-setp vars)
                (set::in var vars))
           (set::in (rename-ispace-var var dim-renam shape-renam)
                    (ispace-var-set-rename-ispace-vars vars
                                                       dim-renam
                                                       shape-renam)))
  :induct t
  :enable (ispace-var-set-rename-ispace-vars set::in))

(defrule ispace-var-set-rename-ispace-vars-of-insert
  (implies (and (ispace-var-setp vars)
                (ispace-varp var))
           (equal (ispace-var-set-rename-ispace-vars (set::insert var vars)
                                                     dim-renam
                                                     shape-renam)
                  (set::insert (rename-ispace-var var dim-renam shape-renam)
                               (ispace-var-set-rename-ispace-vars
                                vars dim-renam shape-renam))))
  :induct (ispace-var-set-rename-ispace-vars vars dim-renam shape-renam)
  :expand ((ispace-var-set-rename-ispace-vars (set::insert var vars)
                                              dim-renam
                                              shape-renam))
  :enable (ispace-var-set-rename-ispace-vars
           set::head-insert
           set::tail-insert))

(defrule ispace-var-set-rename-ispace-vars-of-union
  (implies (and (ispace-var-setp vars1)
                (ispace-var-setp vars2))
           (equal (ispace-var-set-rename-ispace-vars (set::union vars1 vars2)
                                                     dim-renam
                                                     shape-renam)
                  (set::union (ispace-var-set-rename-ispace-vars
                               vars1 dim-renam shape-renam)
                              (ispace-var-set-rename-ispace-vars
                               vars2 dim-renam shape-renam))))
  :induct (ispace-var-set-rename-ispace-vars vars1 dim-renam shape-renam)
  :enable (ispace-var-set-rename-ispace-vars set::union))

; Membership in the name components of a set of ispace variables.

(defrule in-of-dim-names-of-ispace-vars
  (implies (ispace-var-setp vars)
           (equal (set::in name
                           (mv-nth 0 (dim/shape-names-of-ispace-vars vars)))
                  (and (stringp name)
                       (set::in (ispace-var-dim name) vars))))
  :induct t
  :enable (dim/shape-names-of-ispace-vars
           equal-of-ispace-var-dim
           set::in))

(defrule in-of-shape-names-of-ispace-vars
  (implies (ispace-var-setp vars)
           (equal (set::in name
                           (mv-nth 1 (dim/shape-names-of-ispace-vars vars)))
                  (and (stringp name)
                       (set::in (ispace-var-shape name) vars))))
  :induct t
  :enable (dim/shape-names-of-ispace-vars
           equal-of-ispace-var-shape
           set::in))

; The free ispace variables of dimensions are all dimension variables.

(defrulel setp-of-dim-names-of-ispace-vars
  (set::setp (mv-nth 0 (dim/shape-names-of-ispace-vars vars)))
  :use string-setp-of-dim/shape-names-of-ispace-vars.dim-names
  :disable string-setp-of-dim/shape-names-of-ispace-vars.dim-names)

(defrulel setp-of-shape-names-of-ispace-vars
  (set::setp (mv-nth 1 (dim/shape-names-of-ispace-vars vars)))
  :use string-setp-of-dim/shape-names-of-ispace-vars.shape-names
  :disable string-setp-of-dim/shape-names-of-ispace-vars.shape-names)

(defrule dim-names-of-ispace-vars-of-union
  (implies (and (ispace-var-setp vars1)
                (ispace-var-setp vars2))
           (equal (mv-nth 0 (dim/shape-names-of-ispace-vars
                             (set::union vars1 vars2)))
                  (set::union
                   (mv-nth 0 (dim/shape-names-of-ispace-vars vars1))
                   (mv-nth 0 (dim/shape-names-of-ispace-vars vars2)))))
  :enable (set::double-containment set::pick-a-point-subset-strategy))

(defrule shape-names-of-ispace-vars-of-union
  (implies (and (ispace-var-setp vars1)
                (ispace-var-setp vars2))
           (equal (mv-nth 1 (dim/shape-names-of-ispace-vars
                             (set::union vars1 vars2)))
                  (set::union
                   (mv-nth 1 (dim/shape-names-of-ispace-vars vars1))
                   (mv-nth 1 (dim/shape-names-of-ispace-vars vars2)))))
  :enable (set::double-containment set::pick-a-point-subset-strategy))

(defrule dim-names-of-ispace-vars-of-insert
  (implies (and (ispace-varp var)
                (ispace-var-setp vars))
           (equal (mv-nth 0 (dim/shape-names-of-ispace-vars
                             (set::insert var vars)))
                  (if (ispace-var-case var :dim)
                      (set::insert (ispace-var-dim->name var)
                                   (mv-nth 0 (dim/shape-names-of-ispace-vars
                                              vars)))
                    (mv-nth 0 (dim/shape-names-of-ispace-vars vars)))))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy
           equal-of-ispace-var-dim))

(defrule shape-names-of-ispace-vars-of-insert
  (implies (and (ispace-varp var)
                (ispace-var-setp vars))
           (equal (mv-nth 1 (dim/shape-names-of-ispace-vars
                             (set::insert var vars)))
                  (if (ispace-var-case var :shape)
                      (set::insert (ispace-var-shape->name var)
                                   (mv-nth 1 (dim/shape-names-of-ispace-vars
                                              vars)))
                    (mv-nth 1 (dim/shape-names-of-ispace-vars vars)))))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy
           equal-of-ispace-var-shape))

(defthm-dims-free-ispace-vars-flag
  (defthm shape-names-of-dim-free-ispace-vars
    (equal (mv-nth 1 (dim/shape-names-of-ispace-vars
                          (dim-free-ispace-vars dim)))
           nil)
    :flag dim-free-ispace-vars)
  (defthm shape-names-of-dim-list-free-ispace-vars
    (equal (mv-nth 1 (dim/shape-names-of-ispace-vars
                          (dim-list-free-ispace-vars dim-list)))
           nil)
    :flag dim-list-free-ispace-vars)
  :hints (("Goal" :in-theory (enable dim-free-ispace-vars
                                     dim-list-free-ispace-vars
                                     dim/shape-names-of-ispace-vars
                                     set::union))))

; Renaming a set of dimension variables does not depend on
; the shape renaming.

(defruled ispace-var-set-rename-ispace-vars-when-no-shape-vars
  (implies (and (syntaxp (not (equal shape-renam ''nil)))
                (ispace-var-setp vars)
                (equal (mv-nth 1 (dim/shape-names-of-ispace-vars vars)) nil))
           (equal (ispace-var-set-rename-ispace-vars vars
                                                     dim-renam
                                                     shape-renam)
                  (ispace-var-set-rename-ispace-vars vars dim-renam nil)))
  :induct (ispace-var-set-rename-ispace-vars vars dim-renam shape-renam)
  :enable (ispace-var-set-rename-ispace-vars
           dim/shape-names-of-ispace-vars
           rename-ispace-var))

; The free ispace variables of a renamed dimension are the renamings of
; the free ispace variables of the dimension.  (Dimensions have no binders,
; so there is no capture to worry about.)

(defthm-dims-rename-dim-vars-flag
  (defthm free-ispace-vars-of-dim-rename-dim-vars
    (equal (dim-free-ispace-vars (dim-rename-dim-vars dim renam))
           (ispace-var-set-rename-ispace-vars (dim-free-ispace-vars dim)
                                              renam
                                              nil))
    :flag dim-rename-dim-vars)
  (defthm free-ispace-vars-of-dim-list-rename-dim-vars
    (equal (dim-list-free-ispace-vars (dim-list-rename-dim-vars dim-list renam))
           (ispace-var-set-rename-ispace-vars
            (dim-list-free-ispace-vars dim-list)
            renam
            nil))
    :flag dim-list-rename-dim-vars)
  :hints (("Goal" :in-theory (enable dim-rename-dim-vars
                                     dim-list-rename-dim-vars
                                     dim-free-ispace-vars
                                     dim-list-free-ispace-vars
                                     ispace-var-set-rename-ispace-vars
                                     rename-ispace-var
                                     rename-var-string))))

; The same for shapes and ispaces, which have no binders either.

(defthm-shapes/ispaces-rename-ispace-vars-flag
  (defthm free-ispace-vars-of-shape-rename-ispace-vars
    (equal (shape-free-ispace-vars
            (shape-rename-ispace-vars shape dim-renam shape-renam))
           (ispace-var-set-rename-ispace-vars (shape-free-ispace-vars shape)
                                              dim-renam
                                              shape-renam))
    :flag shape-rename-ispace-vars)
  (defthm free-ispace-vars-of-shape-list-rename-ispace-vars
    (equal (shape-list-free-ispace-vars
            (shape-list-rename-ispace-vars shape-list dim-renam shape-renam))
           (ispace-var-set-rename-ispace-vars
            (shape-list-free-ispace-vars shape-list)
            dim-renam
            shape-renam))
    :flag shape-list-rename-ispace-vars)
  (defthm free-ispace-vars-of-ispace-rename-ispace-vars
    (equal (ispace-free-ispace-vars
            (ispace-rename-ispace-vars ispace dim-renam shape-renam))
           (ispace-var-set-rename-ispace-vars (ispace-free-ispace-vars ispace)
                                              dim-renam
                                              shape-renam))
    :flag ispace-rename-ispace-vars)
  (defthm free-ispace-vars-of-ispace-list-rename-ispace-vars
    (equal (ispace-list-free-ispace-vars
            (ispace-list-rename-ispace-vars ispace-list dim-renam shape-renam))
           (ispace-var-set-rename-ispace-vars
            (ispace-list-free-ispace-vars ispace-list)
            dim-renam
            shape-renam))
    :flag ispace-list-rename-ispace-vars)
  :hints
  (("Goal" :in-theory (enable shape-rename-ispace-vars
                              shape-list-rename-ispace-vars
                              ispace-rename-ispace-vars
                              ispace-list-rename-ispace-vars
                              shape-free-ispace-vars
                              shape-list-free-ispace-vars
                              ispace-free-ispace-vars
                              ispace-list-free-ispace-vars
                              ispace-var-set-rename-ispace-vars-when-no-shape-vars
                              ispace-var-set-rename-ispace-vars
                              rename-ispace-var
                              rename-var-string))))

; Renaming under maps with the bound variables removed, then removing the
; bound variables, is the same as removing the bound variables and then
; renaming under the full maps, provided the renaming captures none of the
; bound variables.  This is the key lemma for the Pi and Sigma binders.

(defruledl not-in-bound-of-renamed-dim-name
  (implies (and (ispace-var-setp bound)
                (set::emptyp
                 (set::intersect
                  (mv-nth 0 (dim/shape-names-of-ispace-vars bound))
                  (omap::values
                   (omap::delete*
                    (mv-nth 0 (dim/shape-names-of-ispace-vars bound))
                    (string-string-map-fix dim-renam)))))
                (stringp name)
                (not (set::in (ispace-var-dim name) bound))
                (omap::assoc name (string-string-map-fix dim-renam)))
           (not (set::in
                 (ispace-var-dim
                  (cdr (omap::assoc name (string-string-map-fix dim-renam))))
                 bound)))
  :use ((:instance omap::cdr-assoc-in-values
                   (omap::key name)
                   (omap::map (omap::delete*
                               (mv-nth 0 (dim/shape-names-of-ispace-vars
                                          bound))
                               (string-string-map-fix dim-renam))))
        (:instance set::never-in-empty
                   (set::a (cdr (omap::assoc name
                                        (string-string-map-fix dim-renam))))
                   (set::x (set::intersect (mv-nth 0 (dim/shape-names-of-ispace-vars bound))
                                           (omap::values
                       (omap::delete*
                        (mv-nth 0 (dim/shape-names-of-ispace-vars bound))
                        (string-string-map-fix dim-renam))))))))

(defruledl not-in-bound-of-renamed-shape-name
  (implies (and (ispace-var-setp bound)
                (set::emptyp
                 (set::intersect
                  (mv-nth 1 (dim/shape-names-of-ispace-vars bound))
                  (omap::values
                   (omap::delete*
                    (mv-nth 1 (dim/shape-names-of-ispace-vars bound))
                    (string-string-map-fix shape-renam)))))
                (stringp name)
                (not (set::in (ispace-var-shape name) bound))
                (omap::assoc name (string-string-map-fix shape-renam)))
           (not (set::in
                 (ispace-var-shape
                  (cdr (omap::assoc name
                                    (string-string-map-fix shape-renam))))
                 bound)))
  :use ((:instance omap::cdr-assoc-in-values
                   (omap::key name)
                   (omap::map (omap::delete*
                               (mv-nth 1 (dim/shape-names-of-ispace-vars
                                          bound))
                               (string-string-map-fix shape-renam))))
        (:instance set::never-in-empty
                   (set::a (cdr (omap::assoc name
                                        (string-string-map-fix
                                         shape-renam))))
                   (set::x (set::intersect (mv-nth 1 (dim/shape-names-of-ispace-vars bound))
                                           (omap::values
                       (omap::delete*
                        (mv-nth 1 (dim/shape-names-of-ispace-vars bound))
                        (string-string-map-fix shape-renam))))))))

(defruled ispace-var-set-rename-ispace-vars-of-difference
  (implies
   (and (ispace-var-setp vars)
        (ispace-var-setp bound)
        (renaming-no-capture-p
         (mv-nth 0 (dim/shape-rename-remove-bound bound dim-renam shape-renam))
         (mv-nth 2 (dim/shape-rename-remove-bound bound dim-renam shape-renam)))
        (renaming-no-capture-p
         (mv-nth 1 (dim/shape-rename-remove-bound bound dim-renam shape-renam))
         (mv-nth 3 (dim/shape-rename-remove-bound bound
                                                  dim-renam
                                                  shape-renam))))
   (equal
    (set::difference
     (ispace-var-set-rename-ispace-vars
      vars
      (mv-nth 2 (dim/shape-rename-remove-bound bound dim-renam shape-renam))
      (mv-nth 3 (dim/shape-rename-remove-bound bound dim-renam shape-renam)))
     bound)
    (ispace-var-set-rename-ispace-vars (set::difference vars bound)
                                       dim-renam
                                       shape-renam)))
  :induct (ispace-var-set-rename-ispace-vars vars dim-renam shape-renam)
  :enable (ispace-var-set-rename-ispace-vars
           dim/shape-rename-remove-bound
           renaming-no-capture-p
           rename-ispace-var
           rename-var-string
           equal-of-ispace-var-dim
           equal-of-ispace-var-shape
           not-in-bound-of-renamed-dim-name
           not-in-bound-of-renamed-shape-name
           set::difference
           set::difference-insert-x))

; The singleton version of the previous theorem, for the unary product types,
; obtained by instantiating it with the singleton set of the bound variable
; and by bridging the set difference to a set deletion.

(local
 (defruled difference-of-insert-nil
   (equal (set::difference vars (set::insert var nil))
          (set::delete var vars))
   :enable (set::double-containment set::pick-a-point-subset-strategy)))

(defruled ispace-var-set-rename-ispace-vars-of-delete
  (implies
   (and (ispace-var-setp vars)
        (ispace-varp var)
        (renaming-no-capture-p
         (mv-nth 0 (dim/shape-rename-remove-bound (set::insert var nil)
                                                  dim-renam
                                                  shape-renam))
         (mv-nth 2 (dim/shape-rename-remove-bound (set::insert var nil)
                                                  dim-renam
                                                  shape-renam)))
        (renaming-no-capture-p
         (mv-nth 1 (dim/shape-rename-remove-bound (set::insert var nil)
                                                  dim-renam
                                                  shape-renam))
         (mv-nth 3 (dim/shape-rename-remove-bound (set::insert var nil)
                                                  dim-renam
                                                  shape-renam))))
   (equal
    (set::delete
     var
     (ispace-var-set-rename-ispace-vars
      vars
      (mv-nth 2 (dim/shape-rename-remove-bound (set::insert var nil)
                                               dim-renam
                                               shape-renam))
      (mv-nth 3 (dim/shape-rename-remove-bound (set::insert var nil)
                                               dim-renam
                                               shape-renam))))
    (ispace-var-set-rename-ispace-vars (set::delete var vars)
                                       dim-renam
                                       shape-renam)))
  :use ((:instance ispace-var-set-rename-ispace-vars-of-difference
                   (bound (set::insert var nil))))
  :enable difference-of-insert-nil)

; The free ispace variables of a renamed type are the renamings of the free
; ispace variables of the type, provided the renaming captures no variables.

(defthm-types-rename-ispace-vars-flag
  (defthm free-ispace-vars-of-type-rename-ispace-vars
    (implies (type-rename-ispace-vars-no-capture-p type dim-renam shape-renam)
             (equal (type-free-ispace-vars
                     (type-rename-ispace-vars type dim-renam shape-renam))
                    (ispace-var-set-rename-ispace-vars
                     (type-free-ispace-vars type)
                     dim-renam
                     shape-renam)))
    :flag type-rename-ispace-vars)
  (defthm free-ispace-vars-of-type-list-rename-ispace-vars
    (implies (type-list-rename-ispace-vars-no-capture-p type-list
                                                        dim-renam
                                                        shape-renam)
             (equal (type-list-free-ispace-vars
                     (type-list-rename-ispace-vars type-list
                                                   dim-renam
                                                   shape-renam))
                    (ispace-var-set-rename-ispace-vars
                     (type-list-free-ispace-vars type-list)
                     dim-renam
                     shape-renam)))
    :flag type-list-rename-ispace-vars)
  :hints
  (("Goal" :in-theory (enable type-rename-ispace-vars
                              type-list-rename-ispace-vars
                              type-free-ispace-vars
                              type-list-free-ispace-vars
                              type-rename-ispace-vars-no-capture-p
                              type-list-rename-ispace-vars-no-capture-p
                              ispace-var-set-rename-ispace-vars-of-difference
                              ispace-var-set-rename-ispace-vars-of-delete
                              ispace-var-set-rename-ispace-vars))))

; The free type variables of a type are untouched by an ispace renaming.

(defthm-types-rename-ispace-vars-flag
  (defthm free-type-vars-of-type-rename-ispace-vars
    (equal (type-free-type-vars
            (type-rename-ispace-vars type dim-renam shape-renam))
           (type-free-type-vars type))
    :flag type-rename-ispace-vars)
  (defthm free-type-vars-of-type-list-rename-ispace-vars
    (equal (type-list-free-type-vars
            (type-list-rename-ispace-vars type-list dim-renam shape-renam))
           (type-list-free-type-vars type-list))
    :flag type-list-rename-ispace-vars)
  :hints
  (("Goal" :in-theory (enable type-rename-ispace-vars
                              type-list-rename-ispace-vars
                              type-free-type-vars
                              type-list-free-type-vars))))

; Restricting an environment related to another by renaming, to the renamed
; free variables, yields the renaming of the restriction of the other
; environment to the original free variables.  We first derive a version of
; OMAP::RESTRICT that recurs over the set of keys, and two ordering lemmas.

(defruled omap-restrict-to-head-tail
  (implies (and (syntaxp (symbolp keys))
                (set::setp keys)
                (not (set::emptyp keys)))
           (equal (omap::restrict keys map)
                  (if (omap::assoc (set::head keys) map)
                      (omap::update (set::head keys)
                                    (cdr (omap::assoc (set::head keys) map))
                                    (omap::restrict (set::tail keys) map))
                    (omap::restrict (set::tail keys) map))))
  :use ((:instance omap::restrict-of-insert
                   (omap::k (set::head keys))
                   (omap::ks (set::tail keys))
                   (omap::x map))
        (:instance set::insert-head-tail (set::x keys))))

(defruled <<-of-head-when-in-tail
  (implies (set::in k (set::tail s))
           (acl2::<< (set::head s) k))
  :use (set::head-unique
        (:instance set::head-minimal-2 (set::a k) (set::x s))
        (:instance set::in-tail (set::a k) (set::x s))
        (:instance acl2::<<-trichotomy
                   (acl2::x (set::head s))
                   (acl2::y k)))
  :disable set::head-minimal-2)

(defruled <<-of-head-of-restrict-of-tail
  (implies (and (not (omap::emptyp (omap::restrict (set::tail s) map))))
           (acl2::<< (set::head s)
                     (mv-nth 0 (omap::head (omap::restrict (set::tail s)
                                                           map)))))
  :use ((:instance <<-of-head-when-in-tail
                   (k (mv-nth 0 (omap::head (omap::restrict (set::tail s)
                                                            map)))))
        (:instance omap::assoc-of-head
                   (omap::map (omap::restrict (set::tail s) map))))
  :enable omap::assoc-of-restrict
  :disable (<<-of-head-when-in-tail omap::assoc-of-head))

; Restriction of the new ispace environment to renamed variables.

(defruled ispace-denv-restrict-of-rename-when-denv-ispace-vars-renamed-p
  (implies (and (denv-ispace-vars-renamed-p new-idenv idenv
                                            dim-renam shape-renam)
                (ispace-var-setp vars))
           (equal (ispace-denv-restrict
                   (ispace-var-set-rename-ispace-vars vars
                                                      dim-renam
                                                      shape-renam)
                   new-idenv)
                  (ispace-denv-rename-ispace-vars
                   (ispace-denv-restrict vars idenv)
                   dim-renam
                   shape-renam)))
  :induct (ispace-var-set-rename-ispace-vars vars dim-renam shape-renam)
  :enable (ispace-var-set-rename-ispace-vars
           ispace-denv-restrict
           ispace-denv-rename-ispace-vars
           ispace-var-ispace-value-map-rename-ispace-vars
           omap-restrict-to-head-tail
           <<-of-head-of-restrict-of-tail))

; Restriction of the type-variable map of the new environment, whose keys
; are untouched by an ispace renaming.

(defruled restrict-of-types-when-denv-type-vars-ispace-renamed-p
  (implies (and (denv-type-vars-ispace-renamed-p new-denv denv
                                                 dim-renam shape-renam)
                (type-var-setp vars))
           (equal (omap::restrict vars (type-denv->types new-denv))
                  (type-var-type-value-map-rename-ispace-vars
                   (omap::restrict vars (type-denv->types denv))
                   dim-renam
                   shape-renam)))
  :induct (set::cardinality vars)
  :enable (set::cardinality
           type-var-type-value-map-rename-ispace-vars
           omap-restrict-to-head-tail
           <<-of-head-of-restrict-of-tail))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Evaluation of renamed types.
;
; The rewriter's heuristics decline to open TYPE-RENAME-ISPACE-VARS and
; EVAL-TYPE on the Pi and Sigma cases (the bound-variable removal changes the
; renaming arguments of the recursive calls), so we generate hypothesis-guarded
; opener rules for them.

(local (acl2::defopeners type-rename-ispace-vars))
(local (acl2::defopeners eval-type))

; Commutation of ispace-variable renaming with the currying of product
; types performed by evaluation (see pi-curried-body): renaming the curried
; body under the maps reduced by the first parameter equals currying the
; body renamed under the maps reduced by all the parameters.  The crux is
; that removing the first parameter and then the remaining ones from the
; renaming maps equals removing all the parameters at once.

(local
 (defruled mergesort-of-cons
   (equal (set::mergesort (cons a l))
          (set::insert a (set::mergesort l)))
   :enable set::mergesort))

(local
 (defruled mergesort-when-singleton
   (implies (and (consp params)
                 (not (consp (cdr params))))
            (equal (set::mergesort params)
                   (set::insert (car params) nil)))
   :expand ((set::mergesort params)
            (set::mergesort (cdr params)))))

(local
 (defruled delete*-of-delete*-fuse
   (equal (omap::delete* keys1 (omap::delete* keys2 map))
          (omap::delete* (set::union keys1 keys2) map))
   :expand ((omap::ext-equal (omap::delete* keys1 (omap::delete* keys2 map))
                             (omap::delete* (set::union keys1 keys2) map))
            (omap::ext-equal (omap::delete* (set::union keys1 keys2) map)
                             (omap::delete* keys1 (omap::delete* keys2 map))))
   :use ((:instance omap::ext-equal-becomes-equal
                    (omap::x (omap::delete* keys1 (omap::delete* keys2 map)))
                    (omap::y (omap::delete* (set::union keys1 keys2) map))))))

(local
 (defruled dim/shape-rename-remove-bound-of-insert-then-rest
   (implies (and (ispace-varp var)
                 (ispace-var-listp rest))
            (b* (((mv & & dim1 shape1)
                  (dim/shape-rename-remove-bound (set::insert var nil)
                                                 dim-renam shape-renam))
                 ((mv & & dim2 shape2)
                  (dim/shape-rename-remove-bound (set::mergesort rest)
                                                 dim1 shape1))
                 ((mv & & dimc shapec)
                  (dim/shape-rename-remove-bound (set::mergesort
                                                  (cons var rest))
                                                 dim-renam shape-renam)))
              (and (equal dim2 dimc)
                   (equal shape2 shapec))))
   :enable (dim/shape-rename-remove-bound
            delete*-of-delete*-fuse
            mergesort-of-cons)))

(defrule type-rename-ispace-vars-of-pi-curried-body
  (implies (and (ispace-var-listp params)
                (consp params))
           (b* (((mv & & dim1 shape1)
                 (dim/shape-rename-remove-bound (set::insert (car params) nil)
                                                dim-renam shape-renam))
                ((mv & & dim-all shape-all)
                 (dim/shape-rename-remove-bound (set::mergesort params)
                                                dim-renam shape-renam)))
             (equal (type-rename-ispace-vars (pi-curried-body params body)
                                             dim1 shape1)
                    (pi-curried-body params
                                     (type-rename-ispace-vars body
                                                              dim-all
                                                              shape-all)))))
  :enable (pi-curried-body
           mergesort-when-singleton)
  :use ((:instance dim/shape-rename-remove-bound-of-insert-then-rest
                   (var (car params))
                   (rest (cdr params)))))

(defrule type-rename-ispace-vars-of-sigma-curried-body
  (implies (and (ispace-var-listp params)
                (consp params))
           (b* (((mv & & dim1 shape1)
                 (dim/shape-rename-remove-bound (set::insert (car params) nil)
                                                dim-renam shape-renam))
                ((mv & & dim-all shape-all)
                 (dim/shape-rename-remove-bound (set::mergesort params)
                                                dim-renam shape-renam)))
             (equal (type-rename-ispace-vars (sigma-curried-body params body)
                                             dim1 shape1)
                    (sigma-curried-body params
                                        (type-rename-ispace-vars body
                                                                 dim-all
                                                                 shape-all)))))
  :enable (sigma-curried-body
           mergesort-when-singleton)
  :use ((:instance dim/shape-rename-remove-bound-of-insert-then-rest
                   (var (car params))
                   (rest (cdr params)))))

; The ispace-variable analogue for the currying of universal types:
; since universal types bind no ispace variables,
; the renaming maps are not reduced, and the commutation is direct.

(defrule type-rename-ispace-vars-of-forall-curried-body
  (implies (and (type-var-listp params)
                (consp params))
           (equal (type-rename-ispace-vars (forall-curried-body params body)
                                           dim-renam shape-renam)
                  (forall-curried-body params
                                       (type-rename-ispace-vars body
                                                                dim-renam
                                                                shape-renam))))
  :enable forall-curried-body)

; The analogue for the currying of term lambda abstractions
; (see lambda-curried-body), laid down ahead of that currying:
; lambda abstractions bind no ispace variables,
; but their parameter type annotations may contain ispace variables,
; so all components are renamed and the commutation is direct.

(local (acl2::defopeners expr-rename-ispace-vars))
(local (acl2::defopeners atom-rename-ispace-vars))

(defrule expr-rename-ispace-vars-of-lambda-curried-body
  (implies (and (var+type?-listp params)
                (consp params))
           (equal (expr-rename-ispace-vars
                   (lambda-curried-body params body type?)
                   dim-renam shape-renam)
                  (lambda-curried-body
                   (var+type?-list-rename-ispace-vars params
                                                      dim-renam
                                                      shape-renam)
                   (expr-rename-ispace-vars body dim-renam shape-renam)
                   (type-option-rename-ispace-vars type?
                                                   dim-renam
                                                   shape-renam))))
  :enable (lambda-curried-body
           var+type?-list-rename-ispace-vars))

; Phase 1: evaluating a renamed type errs exactly when evaluating the
; original type does.  This is proved first, and separately from the value
; equality below, so that during the induction for the latter the error
; status of the renamed evaluations can be rewritten (by the theorems below)
; to the error status of the original ones.

(defthm-eval-types-flag
  (defthm reserrp-of-eval-type-of-type-rename-ispace-vars
    (implies (and (denv-ispace-vars-renamed-p (type-denv->ienv new-denv)
                                              (type-denv->ienv denv)
                                              dim-renam shape-renam)
                  (denv-type-vars-ispace-renamed-p new-denv denv
                                                   dim-renam shape-renam))
             (iff (reserrp (eval-type (type-rename-ispace-vars type
                                                               dim-renam
                                                               shape-renam)
                                      new-denv))
                  (reserrp (eval-type type denv))))
    :flag eval-type)
  (defthm reserrp-of-eval-type-list-of-type-list-rename-ispace-vars
    (implies (and (denv-ispace-vars-renamed-p (type-denv->ienv new-denv)
                                              (type-denv->ienv denv)
                                              dim-renam shape-renam)
                  (denv-type-vars-ispace-renamed-p new-denv denv
                                                   dim-renam shape-renam))
             (iff (reserrp (eval-type-list
                            (type-list-rename-ispace-vars types
                                                          dim-renam
                                                          shape-renam)
                            new-denv))
                  (reserrp (eval-type-list types denv))))
    :flag eval-type-list)
  :hints
  (("Goal"
    :in-theory (enable eval-type
                       eval-type-list
                       type-rename-ispace-vars
                       type-list-rename-ispace-vars
                       not-reserrp-when-type-valuep
                       not-reserrp-when-type-value-listp
                       type-valuep-when-result-not-error
                       type-value-listp-when-result-not-error
                       type-denv-lookup-type))
   (and acl2::stable-under-simplificationp
        '(:use ((:instance denv-type-vars-ispace-renamed-p-necc
                           (var (type-var->var type))))))))

; Phase 2: on success, evaluating a renamed type yields the renaming of the
; original type value.

(defthm-eval-types-flag
  (defthm eval-type-of-type-rename-ispace-vars
    (implies (and (denv-ispace-vars-renamed-p (type-denv->ienv new-denv)
                                              (type-denv->ienv denv)
                                              dim-renam shape-renam)
                  (denv-type-vars-ispace-renamed-p new-denv denv
                                                   dim-renam shape-renam)
                  (type-rename-ispace-vars-no-capture-p type
                                                        dim-renam
                                                        shape-renam)
                  (not (reserrp (eval-type type denv))))
             (equal (eval-type (type-rename-ispace-vars type
                                                        dim-renam
                                                        shape-renam)
                               new-denv)
                    (type-value-rename-ispace-vars (eval-type type denv)
                                                   dim-renam
                                                   shape-renam)))
    :flag eval-type)
  (defthm eval-type-list-of-type-list-rename-ispace-vars
    (implies (and (denv-ispace-vars-renamed-p (type-denv->ienv new-denv)
                                              (type-denv->ienv denv)
                                              dim-renam shape-renam)
                  (denv-type-vars-ispace-renamed-p new-denv denv
                                                   dim-renam shape-renam)
                  (type-list-rename-ispace-vars-no-capture-p types
                                                             dim-renam
                                                             shape-renam)
                  (not (reserrp (eval-type-list types denv))))
             (equal (eval-type-list (type-list-rename-ispace-vars types
                                                                  dim-renam
                                                                  shape-renam)
                                    new-denv)
                    (type-value-list-rename-ispace-vars
                     (eval-type-list types denv)
                     dim-renam
                     shape-renam)))
    :flag eval-type-list)
  :hints
  (("Goal"
    :in-theory (enable eval-type
                       eval-type-list
                       type-rename-ispace-vars
                       type-list-rename-ispace-vars
                       type-value-rename-ispace-vars
                       type-value-list-rename-ispace-vars
                       type-rename-ispace-vars-no-capture-p
                       type-list-rename-ispace-vars-no-capture-p
                       type-denv-rename-ispace-vars
                       type-denv-restrict
                       type-free-ispace-vars
                       type-free-type-vars
                       ispace-var-set-rename-ispace-vars-of-difference
                       ispace-var-set-rename-ispace-vars-of-delete
                       ispace-denv-restrict-of-rename-when-denv-ispace-vars-renamed-p
                       restrict-of-types-when-denv-type-vars-ispace-renamed-p
                       not-reserrp-when-type-valuep
                       not-reserrp-when-type-value-listp
                       type-valuep-when-result-not-error
                       type-value-listp-when-result-not-error
                       type-denv-lookup-type))
   (and acl2::stable-under-simplificationp
        '(:use ((:instance denv-type-vars-ispace-renamed-p-necc
                           (var (type-var->var type))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Renamings of type variables.
;
; A renaming of type variables does not touch ispace variables, so the
; ispace-variable maps of the two environments are related by simple
; agreement, and the evaluation of dimensions, shapes, and ispaces (which
; depends on the environment only through that map) is unchanged.

(acl2::defun-sk denv-ispace-vars-equal-p (new-denv denv)
  (forall (var)
          (implies (ispace-varp var)
                   (equal (omap::assoc var (ispace-denv->ispaces new-denv))
                          (omap::assoc var (ispace-denv->ispaces denv)))))
  :rewrite :direct)

(in-theory (disable denv-ispace-vars-equal-p))

(defthm-eval-dims-flag
  (defthm eval-dim-when-denv-ispace-vars-equal
    (implies (denv-ispace-vars-equal-p new-denv denv)
             (equal (eval-dim dim new-denv)
                    (eval-dim dim denv)))
    :flag eval-dim)
  (defthm eval-dim-list-when-denv-ispace-vars-equal
    (implies (denv-ispace-vars-equal-p new-denv denv)
             (equal (eval-dim-list dims new-denv)
                    (eval-dim-list dims denv)))
    :flag eval-dim-list)
  :hints
  (("Goal" :in-theory (enable eval-dim eval-dim-list
                              ispace-denv-lookup-ispace))))

(defthm-eval-shapes/ispaces-flag
  (defthm eval-shape-when-denv-ispace-vars-equal
    (implies (denv-ispace-vars-equal-p new-denv denv)
             (equal (eval-shape shape new-denv)
                    (eval-shape shape denv)))
    :flag eval-shape)
  (defthm eval-shape-list-when-denv-ispace-vars-equal
    (implies (denv-ispace-vars-equal-p new-denv denv)
             (equal (eval-shape-list shapes new-denv)
                    (eval-shape-list shapes denv)))
    :flag eval-shape-list)
  (defthm eval-ispace-when-denv-ispace-vars-equal
    (implies (denv-ispace-vars-equal-p new-denv denv)
             (equal (eval-ispace ispace new-denv)
                    (eval-ispace ispace denv)))
    :flag eval-ispace)
  (defthm eval-ispace-list-when-denv-ispace-vars-equal
    (implies (denv-ispace-vars-equal-p new-denv denv)
             (equal (eval-ispace-list ispaces new-denv)
                    (eval-ispace-list ispaces denv)))
    :flag eval-ispace-list)
  :hints
  (("Goal" :in-theory (enable eval-shape
                              eval-shape-list
                              eval-ispace
                              eval-ispace-list
                              ispace-denv-lookup-ispace))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rename-type-var ((var type-varp)
                         (atom-renam string-string-mapp)
                         (array-renam string-string-mapp))
  :returns (new-var type-varp)
  :short "Rename a type variable:
          an atom-kind variable through the atom-kind renaming,
          an array-kind variable through the array-kind renaming."
  (type-var-case
   var
   :atom (type-var-atom (rename-var-string var.name atom-renam))
   :array (type-var-array (rename-var-string var.name array-renam)))

  ///

  (fty::deffixequiv rename-type-var))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Renaming of type variables in type values, mirroring what
; AST-RENAME-TYPE-VARS does to the corresponding types (in particular,
; reducing the renaming at Forall binders).  As for ispace renamings,
; the environments captured in the type values of universal, product, and
; sum types are renamed as well, under the full (unreduced) maps: the keys
; of the type-variable map are renamed and its type values are renamed
; recursively, while the ispace map is untouched (its keys are not
; type variables, and its values are ground).

(defines type-value-rename-type-vars
  ;; The flag function is used by theorems in other books
  ;; (see unique-names-validation.lisp).
  :flag-local nil

  (define type-value-rename-type-vars ((tval type-valuep)
                                       (atom-renam string-string-mapp)
                                       (array-renam string-string-mapp))
    :returns (new-tval type-valuep)
    :parents (renaming-evaluation type-value-rename-type-vars)
    :short "Rename type variables in a type value."
    :measure (type-value-count tval)
    (type-value-case
     tval
     :base (type-value-fix tval)
     :array (make-type-value-array
             :elem (type-value-rename-type-vars tval.elem
                                                atom-renam
                                                array-renam)
             :dims tval.dims)
     :fun (make-type-value-fun
           :in (type-value-list-rename-type-vars tval.in
                                                 atom-renam
                                                 array-renam)
           :out (type-value-rename-type-vars tval.out
                                             atom-renam
                                             array-renam))
     :forall (b* (((mv & & body-atom-renam body-array-renam)
                   (atom/array-rename-remove-bound (set::insert tval.param nil)
                                                   atom-renam
                                                   array-renam)))
               (make-type-value-forall
                :param tval.param
                :body (type-rename-type-vars tval.body
                                             body-atom-renam
                                             body-array-renam)
                :denv (type-denv-rename-type-vars tval.denv
                                                  atom-renam
                                                  array-renam)))
     :pi (make-type-value-pi
          :param tval.param
          :body (type-rename-type-vars tval.body atom-renam array-renam)
          :denv (type-denv-rename-type-vars tval.denv atom-renam array-renam))
     :sigma (make-type-value-sigma
             :param tval.param
             :body (type-rename-type-vars tval.body atom-renam array-renam)
             :denv (type-denv-rename-type-vars tval.denv
                                               atom-renam
                                               array-renam))))

  (define type-value-list-rename-type-vars ((tvals type-value-listp)
                                            (atom-renam string-string-mapp)
                                            (array-renam string-string-mapp))
    :returns (new-tvals type-value-listp)
    :parents (renaming-evaluation type-value-rename-type-vars)
    :short "Rename type variables in a list of type values."
    :measure (type-value-list-count tvals)
    (if (endp tvals)
        nil
      (cons (type-value-rename-type-vars (car tvals) atom-renam array-renam)
            (type-value-list-rename-type-vars (cdr tvals)
                                              atom-renam
                                              array-renam))))

  (define type-var-type-value-map-rename-type-vars
    ((map type-var-type-value-mapp)
     (atom-renam string-string-mapp)
     (array-renam string-string-mapp))
    :returns (new-map type-var-type-value-mapp)
    :parents (renaming-evaluation type-value-rename-type-vars)
    :short "Rename type variables in
            a map from type variables to type values."
    :long
    (xdoc::topstring
     (xdoc::p
      "Both the type variable keys and the type values are renamed."))
    :measure (type-var-type-value-map-count map)
    (b* ((map (type-var-type-value-map-fix map))
         ((when (omap::emptyp map)) nil)
         ((mv var tval) (omap::head map)))
      (omap::update (rename-type-var var atom-renam array-renam)
                    (type-value-rename-type-vars tval atom-renam array-renam)
                    (type-var-type-value-map-rename-type-vars
                     (omap::tail map) atom-renam array-renam))))

  (define type-denv-rename-type-vars ((denv type-denvp)
                                      (atom-renam string-string-mapp)
                                      (array-renam string-string-mapp))
    :returns (new-denv type-denvp)
    :parents (renaming-evaluation type-value-rename-type-vars)
    :short "Rename type variables in a type dynamic environment."
    :long
    (xdoc::topstring
     (xdoc::p
      "The ispace environment is untouched by a type variable renaming."))
    :measure (type-denv-count denv)
    (change-type-denv
     denv
     :types (type-var-type-value-map-rename-type-vars
             (type-denv->types denv) atom-renam array-renam)))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual type-value-rename-type-vars)

  (defret not-reserrp-of-type-value-rename-type-vars
    (not (reserrp new-tval))
    :fn type-value-rename-type-vars
    :hints (("Goal" :in-theory (enable not-reserrp-when-type-valuep))))

  (defret not-reserrp-of-type-value-list-rename-type-vars
    (not (reserrp new-tvals))
    :fn type-value-list-rename-type-vars
    :hints (("Goal" :in-theory (enable not-reserrp-when-type-value-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The type-variable map of the new environment associates, to the renaming
; of each type variable, the renaming of the type value associated to the
; variable in the old environment.

(acl2::defun-sk denv-type-vars-renamed-p (new-denv denv
                                                   atom-renam
                                                   array-renam)
  (forall (var)
          (implies
           (type-varp var)
           (equal (omap::assoc (rename-type-var var atom-renam array-renam)
                               (type-denv->types new-denv))
                  (b* ((pair (omap::assoc var (type-denv->types denv))))
                    (and pair
                         (cons (rename-type-var var atom-renam array-renam)
                               (type-value-rename-type-vars
                                (cdr pair) atom-renam array-renam)))))))
  :rewrite :direct)

(in-theory (disable denv-type-vars-renamed-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Support for the type-level theorems below, mirroring the development for
; ispace renamings: the free type variables of a type with renamed type
; variables are the elementwise renamings of the free type variables of the
; type (when the renaming captures no variables), the free ispace variables
; are untouched, and environment restriction commutes with environment
; renaming.

; Elementwise renaming of a set of type variables.

(define type-var-set-rename-type-vars ((vars type-var-setp)
                                       (atom-renam string-string-mapp)
                                       (array-renam string-string-mapp))
  :returns (new-vars type-var-setp)
  :short "Rename each type variable in a set."
  (b* (((when (set::emptyp (type-var-set-fix vars))) nil))
    (set::insert (rename-type-var (set::head vars) atom-renam array-renam)
                 (type-var-set-rename-type-vars (set::tail vars)
                                                atom-renam
                                                array-renam)))
  :prepwork ((local (in-theory (enable emptyp-of-type-var-set-fix))))
  :verify-guards :after-returns)

(defrule in-of-rename-type-var-of-type-var-set-rename-type-vars
  (implies (and (type-var-setp vars)
                (set::in var vars))
           (set::in (rename-type-var var atom-renam array-renam)
                    (type-var-set-rename-type-vars vars
                                                   atom-renam
                                                   array-renam)))
  :induct t
  :enable (type-var-set-rename-type-vars set::in))

(defrule type-var-set-rename-type-vars-of-insert
  (implies (and (type-var-setp vars)
                (type-varp var))
           (equal (type-var-set-rename-type-vars (set::insert var vars)
                                                 atom-renam
                                                 array-renam)
                  (set::insert (rename-type-var var atom-renam array-renam)
                               (type-var-set-rename-type-vars vars
                                                              atom-renam
                                                              array-renam))))
  :induct (type-var-set-rename-type-vars vars atom-renam array-renam)
  :expand ((type-var-set-rename-type-vars (set::insert var vars)
                                          atom-renam
                                          array-renam))
  :enable (type-var-set-rename-type-vars
           set::head-insert
           set::tail-insert))

(defrule type-var-set-rename-type-vars-of-union
  (implies (and (type-var-setp vars1)
                (type-var-setp vars2))
           (equal (type-var-set-rename-type-vars (set::union vars1 vars2)
                                                 atom-renam
                                                 array-renam)
                  (set::union (type-var-set-rename-type-vars
                               vars1 atom-renam array-renam)
                              (type-var-set-rename-type-vars
                               vars2 atom-renam array-renam))))
  :induct (type-var-set-rename-type-vars vars1 atom-renam array-renam)
  :enable (type-var-set-rename-type-vars set::union))

; Membership in the name components of a set of type variables.

(defrule in-of-atom-names-of-type-vars
  (implies (type-var-setp vars)
           (equal (set::in name
                           (mv-nth 0 (atom/array-names-of-type-vars vars)))
                  (and (stringp name)
                       (set::in (type-var-atom name) vars))))
  :induct t
  :enable (atom/array-names-of-type-vars
           equal-of-type-var-atom
           set::in))

(defrule in-of-array-names-of-type-vars
  (implies (type-var-setp vars)
           (equal (set::in name
                           (mv-nth 1 (atom/array-names-of-type-vars vars)))
                  (and (stringp name)
                       (set::in (type-var-array name) vars))))
  :induct t
  :enable (atom/array-names-of-type-vars
           equal-of-type-var-array
           set::in))

(local
 (defrule setp-of-atom-names-of-type-vars
   (set::setp (mv-nth 0 (atom/array-names-of-type-vars vars)))
   :use string-setp-of-atom/array-names-of-type-vars.atom-names
   :disable string-setp-of-atom/array-names-of-type-vars.atom-names))

(local
 (defrule setp-of-array-names-of-type-vars
   (set::setp (mv-nth 1 (atom/array-names-of-type-vars vars)))
   :use string-setp-of-atom/array-names-of-type-vars.array-names
   :disable string-setp-of-atom/array-names-of-type-vars.array-names))

(defrule atom-names-of-type-vars-of-insert
  (implies (and (type-varp var)
                (type-var-setp vars))
           (equal (mv-nth 0 (atom/array-names-of-type-vars
                             (set::insert var vars)))
                  (if (type-var-case var :atom)
                      (set::insert (type-var-atom->name var)
                                   (mv-nth 0 (atom/array-names-of-type-vars
                                              vars)))
                    (mv-nth 0 (atom/array-names-of-type-vars vars)))))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy
           equal-of-type-var-atom))

(defrule array-names-of-type-vars-of-insert
  (implies (and (type-varp var)
                (type-var-setp vars))
           (equal (mv-nth 1 (atom/array-names-of-type-vars
                             (set::insert var vars)))
                  (if (type-var-case var :array)
                      (set::insert (type-var-array->name var)
                                   (mv-nth 1 (atom/array-names-of-type-vars
                                              vars)))
                    (mv-nth 1 (atom/array-names-of-type-vars vars)))))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy
           equal-of-type-var-array))

; No-capture lemmas for the two type-variable namespaces.

(defruledl not-in-bound-of-renamed-atom-name
  (implies (and (type-var-setp bound)
                (set::emptyp
                 (set::intersect
                  (mv-nth 0 (atom/array-names-of-type-vars bound))
                  (omap::values
                   (omap::delete*
                    (mv-nth 0 (atom/array-names-of-type-vars bound))
                    (string-string-map-fix atom-renam)))))
                (stringp name)
                (not (set::in (type-var-atom name) bound))
                (omap::assoc name (string-string-map-fix atom-renam)))
           (not (set::in
                 (type-var-atom
                  (cdr (omap::assoc name (string-string-map-fix atom-renam))))
                 bound)))
  :use ((:instance omap::cdr-assoc-in-values
                   (omap::key name)
                   (omap::map (omap::delete*
                               (mv-nth 0 (atom/array-names-of-type-vars
                                          bound))
                               (string-string-map-fix atom-renam))))
        (:instance set::never-in-empty
                   (set::a (cdr (omap::assoc name
                                        (string-string-map-fix atom-renam))))
                   (set::x (set::intersect (mv-nth 0 (atom/array-names-of-type-vars bound))
                                           (omap::values
                       (omap::delete*
                        (mv-nth 0 (atom/array-names-of-type-vars bound))
                        (string-string-map-fix atom-renam))))))))

(defruledl not-in-bound-of-renamed-array-name
  (implies (and (type-var-setp bound)
                (set::emptyp
                 (set::intersect
                  (mv-nth 1 (atom/array-names-of-type-vars bound))
                  (omap::values
                   (omap::delete*
                    (mv-nth 1 (atom/array-names-of-type-vars bound))
                    (string-string-map-fix array-renam)))))
                (stringp name)
                (not (set::in (type-var-array name) bound))
                (omap::assoc name (string-string-map-fix array-renam)))
           (not (set::in
                 (type-var-array
                  (cdr (omap::assoc name
                                    (string-string-map-fix array-renam))))
                 bound)))
  :use ((:instance omap::cdr-assoc-in-values
                   (omap::key name)
                   (omap::map (omap::delete*
                               (mv-nth 1 (atom/array-names-of-type-vars
                                          bound))
                               (string-string-map-fix array-renam))))
        (:instance set::never-in-empty
                   (set::a (cdr (omap::assoc name
                                        (string-string-map-fix
                                         array-renam))))
                   (set::x (set::intersect (mv-nth 1 (atom/array-names-of-type-vars bound))
                                           (omap::values
                       (omap::delete*
                        (mv-nth 1 (atom/array-names-of-type-vars bound))
                        (string-string-map-fix array-renam))))))))

; The key lemma for the Forall binder.

(defruled type-var-set-rename-type-vars-of-difference
  (implies
   (and (type-var-setp vars)
        (type-var-setp bound)
        (renaming-no-capture-p
         (mv-nth 0 (atom/array-rename-remove-bound bound
                                                   atom-renam
                                                   array-renam))
         (mv-nth 2 (atom/array-rename-remove-bound bound
                                                   atom-renam
                                                   array-renam)))
        (renaming-no-capture-p
         (mv-nth 1 (atom/array-rename-remove-bound bound
                                                   atom-renam
                                                   array-renam))
         (mv-nth 3 (atom/array-rename-remove-bound bound
                                                   atom-renam
                                                   array-renam))))
   (equal
    (set::difference
     (type-var-set-rename-type-vars
      vars
      (mv-nth 2 (atom/array-rename-remove-bound bound
                                                atom-renam
                                                array-renam))
      (mv-nth 3 (atom/array-rename-remove-bound bound
                                                atom-renam
                                                array-renam)))
     bound)
    (type-var-set-rename-type-vars (set::difference vars bound)
                                   atom-renam
                                   array-renam)))
  :induct (type-var-set-rename-type-vars vars atom-renam array-renam)
  :enable (type-var-set-rename-type-vars
           atom/array-rename-remove-bound
           renaming-no-capture-p
           rename-type-var
           rename-var-string
           equal-of-type-var-atom
           equal-of-type-var-array
           not-in-bound-of-renamed-atom-name
           not-in-bound-of-renamed-array-name
           set::difference
           set::difference-insert-x))

; The type-variable analogue of the singleton (deletion) version of the
; preceding theorem (see ispace-var-set-rename-ispace-vars-of-delete):
; it is needed for the unary universal type, whose free type variables
; are obtained via a set deletion instead of a set difference.

(defruled type-var-set-rename-type-vars-of-delete
  (implies
   (and (type-var-setp vars)
        (type-varp var)
        (renaming-no-capture-p
         (mv-nth 0 (atom/array-rename-remove-bound (set::insert var nil)
                                                   atom-renam
                                                   array-renam))
         (mv-nth 2 (atom/array-rename-remove-bound (set::insert var nil)
                                                   atom-renam
                                                   array-renam)))
        (renaming-no-capture-p
         (mv-nth 1 (atom/array-rename-remove-bound (set::insert var nil)
                                                   atom-renam
                                                   array-renam))
         (mv-nth 3 (atom/array-rename-remove-bound (set::insert var nil)
                                                   atom-renam
                                                   array-renam))))
   (equal
    (set::delete
     var
     (type-var-set-rename-type-vars
      vars
      (mv-nth 2 (atom/array-rename-remove-bound (set::insert var nil)
                                                atom-renam
                                                array-renam))
      (mv-nth 3 (atom/array-rename-remove-bound (set::insert var nil)
                                                atom-renam
                                                array-renam))))
    (type-var-set-rename-type-vars (set::delete var vars)
                                   atom-renam
                                   array-renam)))
  :use ((:instance type-var-set-rename-type-vars-of-difference
                   (bound (set::insert var nil))))
  :enable difference-of-insert-nil)

; The free type variables of a type with renamed type variables are the
; renamings of the free type variables of the type, provided the renaming
; captures no variables.

(defthm-types-rename-type-vars-flag
  (defthm free-type-vars-of-type-rename-type-vars
    (implies (type-rename-type-vars-no-capture-p type atom-renam array-renam)
             (equal (type-free-type-vars
                     (type-rename-type-vars type atom-renam array-renam))
                    (type-var-set-rename-type-vars
                     (type-free-type-vars type)
                     atom-renam
                     array-renam)))
    :flag type-rename-type-vars)
  (defthm free-type-vars-of-type-list-rename-type-vars
    (implies (type-list-rename-type-vars-no-capture-p type-list
                                                      atom-renam
                                                      array-renam)
             (equal (type-list-free-type-vars
                     (type-list-rename-type-vars type-list
                                                 atom-renam
                                                 array-renam))
                    (type-var-set-rename-type-vars
                     (type-list-free-type-vars type-list)
                     atom-renam
                     array-renam)))
    :flag type-list-rename-type-vars)
  :hints
  (("Goal" :in-theory (enable type-rename-type-vars
                              type-list-rename-type-vars
                              type-free-type-vars
                              type-list-free-type-vars
                              type-rename-type-vars-no-capture-p
                              type-list-rename-type-vars-no-capture-p
                              type-var-set-rename-type-vars-of-difference
                              type-var-set-rename-type-vars-of-delete
                              type-var-set-rename-type-vars
                              rename-type-var
                              rename-var-string))))

; The free ispace variables of a type are untouched by a type renaming.

(defthm-types-rename-type-vars-flag
  (defthm free-ispace-vars-of-type-rename-type-vars
    (equal (type-free-ispace-vars
            (type-rename-type-vars type atom-renam array-renam))
           (type-free-ispace-vars type))
    :flag type-rename-type-vars)
  (defthm free-ispace-vars-of-type-list-rename-type-vars
    (equal (type-list-free-ispace-vars
            (type-list-rename-type-vars type-list atom-renam array-renam))
           (type-list-free-ispace-vars type-list))
    :flag type-list-rename-type-vars)
  :hints
  (("Goal" :in-theory (enable type-rename-type-vars
                              type-list-rename-type-vars
                              type-free-ispace-vars
                              type-list-free-ispace-vars))))

; Restriction of the ispace environment is unchanged when the two
; environments have equal ispace-variable maps.

(defruled ispace-denv-restrict-when-denv-ispace-vars-equal-p
  (implies (and (denv-ispace-vars-equal-p new-idenv idenv)
                (ispace-var-setp vars))
           (equal (ispace-denv-restrict vars new-idenv)
                  (ispace-denv-restrict vars idenv)))
  :induct (set::cardinality vars)
  :enable (set::cardinality
           ispace-denv-restrict
           omap-restrict-to-head-tail))

; Restriction of the type-variable map of the new environment to the
; renamed type variables.

(defruled restrict-of-types-when-denv-type-vars-renamed-p
  (implies (and (denv-type-vars-renamed-p new-denv denv
                                          atom-renam array-renam)
                (type-var-setp vars))
           (equal (omap::restrict
                   (type-var-set-rename-type-vars vars
                                                  atom-renam
                                                  array-renam)
                   (type-denv->types new-denv))
                  (type-var-type-value-map-rename-type-vars
                   (omap::restrict vars (type-denv->types denv))
                   atom-renam
                   array-renam)))
  :induct (type-var-set-rename-type-vars vars atom-renam array-renam)
  :enable (type-var-set-rename-type-vars
           type-var-type-value-map-rename-type-vars
           omap-restrict-to-head-tail
           <<-of-head-of-restrict-of-tail))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Evaluation of types with renamed type variables, in the same two phases
; as for renamed ispace variables.

(local (acl2::defopeners type-rename-type-vars))

; The type-variable analogue of the commutation of renaming with the
; currying of product types: since product types bind no type variables,
; the renaming maps are not reduced, and the commutation is direct.

(defrule type-rename-type-vars-of-pi-curried-body
  (implies (and (ispace-var-listp params)
                (consp params))
           (equal (type-rename-type-vars (pi-curried-body params body)
                                         atom-renam array-renam)
                  (pi-curried-body params
                                   (type-rename-type-vars body
                                                          atom-renam
                                                          array-renam))))
  :enable pi-curried-body)

(defrule type-rename-type-vars-of-sigma-curried-body
  (implies (and (ispace-var-listp params)
                (consp params))
           (equal (type-rename-type-vars (sigma-curried-body params body)
                                         atom-renam array-renam)
                  (sigma-curried-body params
                                      (type-rename-type-vars body
                                                             atom-renam
                                                             array-renam))))
  :enable sigma-curried-body)

; The type-variable commutation for the currying of universal types
; mirrors the ispace-variable one for the currying of product types:
; the crux is again that removing the first parameter and then the
; remaining ones from the renaming maps equals removing all the
; parameters at once.

(local
 (defruled atom/array-rename-remove-bound-of-insert-then-rest
   (implies (and (type-varp var)
                 (type-var-listp rest))
            (b* (((mv & & atom1 array1)
                  (atom/array-rename-remove-bound (set::insert var nil)
                                                  atom-renam array-renam))
                 ((mv & & atom2 array2)
                  (atom/array-rename-remove-bound (set::mergesort rest)
                                                  atom1 array1))
                 ((mv & & atomc arrayc)
                  (atom/array-rename-remove-bound (set::mergesort
                                                   (cons var rest))
                                                  atom-renam array-renam)))
              (and (equal atom2 atomc)
                   (equal array2 arrayc))))
   :enable (atom/array-rename-remove-bound
            delete*-of-delete*-fuse
            mergesort-of-cons)))

(defrule type-rename-type-vars-of-forall-curried-body
  (implies (and (type-var-listp params)
                (consp params))
           (b* (((mv & & atom1 array1)
                 (atom/array-rename-remove-bound (set::insert (car params)
                                                              nil)
                                                 atom-renam array-renam))
                ((mv & & atom-all array-all)
                 (atom/array-rename-remove-bound (set::mergesort params)
                                                 atom-renam array-renam)))
             (equal (type-rename-type-vars (forall-curried-body params body)
                                           atom1 array1)
                    (forall-curried-body params
                                         (type-rename-type-vars body
                                                                atom-all
                                                                array-all)))))
  :enable (forall-curried-body
           mergesort-when-singleton)
  :use ((:instance atom/array-rename-remove-bound-of-insert-then-rest
                   (var (car params))
                   (rest (cdr params)))))

; The type-variable analogue for the currying of term lambda abstractions
; (see lambda-curried-body), laid down ahead of that currying:
; lambda abstractions bind no type variables,
; but their parameter type annotations may contain type variables,
; so all components are renamed and the commutation is direct.

(local (acl2::defopeners expr-rename-type-vars))
(local (acl2::defopeners atom-rename-type-vars))

(defrule expr-rename-type-vars-of-lambda-curried-body
  (implies (and (var+type?-listp params)
                (consp params))
           (equal (expr-rename-type-vars
                   (lambda-curried-body params body type?)
                   atom-renam array-renam)
                  (lambda-curried-body
                   (var+type?-list-rename-type-vars params
                                                    atom-renam
                                                    array-renam)
                   (expr-rename-type-vars body atom-renam array-renam)
                   (type-option-rename-type-vars type?
                                                 atom-renam
                                                 array-renam))))
  :enable (lambda-curried-body
           var+type?-list-rename-type-vars))

; The expression-variable analogue for the currying of
; term lambda abstractions, which bind expression variables:
; renaming the curried body under the map reduced by the first parameter
; equals currying the body renamed under the map reduced by
; all the parameters.

(local (acl2::defopeners expr-rename-expr-vars))
(local (acl2::defopeners atom-rename-expr-vars))

(defrule expr-rename-expr-vars-of-lambda-curried-body
  (implies (and (var+type?-listp params)
                (consp params))
           (equal (expr-rename-expr-vars
                   (lambda-curried-body params body type?)
                   (omap::delete* (set::insert (var+type?->var (car params))
                                               nil)
                                  (string-string-map-fix renam)))
                  (lambda-curried-body
                   params
                   (expr-rename-expr-vars
                    body
                    (omap::delete*
                     (set::mergesort (var+type?-list->var params))
                     (string-string-map-fix renam)))
                   type?)))
  :enable (lambda-curried-body
           delete*-of-delete*-fuse
           mergesort-of-cons
           mergesort-when-singleton))

(defthm-eval-types-flag
  (defthm reserrp-of-eval-type-of-type-rename-type-vars
    (implies (and (denv-ispace-vars-equal-p (type-denv->ienv new-denv)
                                            (type-denv->ienv denv))
                  (denv-type-vars-renamed-p new-denv denv
                                            atom-renam array-renam))
             (iff (reserrp (eval-type (type-rename-type-vars type
                                                             atom-renam
                                                             array-renam)
                                      new-denv))
                  (reserrp (eval-type type denv))))
    :flag eval-type)
  (defthm reserrp-of-eval-type-list-of-type-list-rename-type-vars
    (implies (and (denv-ispace-vars-equal-p (type-denv->ienv new-denv)
                                            (type-denv->ienv denv))
                  (denv-type-vars-renamed-p new-denv denv
                                            atom-renam array-renam))
             (iff (reserrp (eval-type-list
                            (type-list-rename-type-vars types
                                                        atom-renam
                                                        array-renam)
                            new-denv))
                  (reserrp (eval-type-list types denv))))
    :flag eval-type-list)
  :hints
  (("Goal"
    :in-theory (enable eval-type
                       eval-type-list
                       type-rename-type-vars
                       type-list-rename-type-vars
                       rename-var-string
                       rename-type-var
                       not-reserrp-when-type-valuep
                       not-reserrp-when-type-value-listp
                       type-valuep-when-result-not-error
                       type-value-listp-when-result-not-error
                       type-denv-lookup-type))
   (and acl2::stable-under-simplificationp
        '(:use ((:instance denv-type-vars-renamed-p-necc
                           (var (type-var->var type))))))))

(defthm-eval-types-flag
  (defthm eval-type-of-type-rename-type-vars
    (implies (and (denv-ispace-vars-equal-p (type-denv->ienv new-denv)
                                            (type-denv->ienv denv))
                  (denv-type-vars-renamed-p new-denv denv
                                            atom-renam array-renam)
                  (type-rename-type-vars-no-capture-p type
                                                      atom-renam
                                                      array-renam)
                  (not (reserrp (eval-type type denv))))
             (equal (eval-type (type-rename-type-vars type
                                                      atom-renam
                                                      array-renam)
                               new-denv)
                    (type-value-rename-type-vars (eval-type type denv)
                                                 atom-renam
                                                 array-renam)))
    :flag eval-type)
  (defthm eval-type-list-of-type-list-rename-type-vars
    (implies (and (denv-ispace-vars-equal-p (type-denv->ienv new-denv)
                                            (type-denv->ienv denv))
                  (denv-type-vars-renamed-p new-denv denv
                                            atom-renam array-renam)
                  (type-list-rename-type-vars-no-capture-p types
                                                           atom-renam
                                                           array-renam)
                  (not (reserrp (eval-type-list types denv))))
             (equal (eval-type-list (type-list-rename-type-vars types
                                                                atom-renam
                                                                array-renam)
                                    new-denv)
                    (type-value-list-rename-type-vars
                     (eval-type-list types denv)
                     atom-renam
                     array-renam)))
    :flag eval-type-list)
  :hints
  (("Goal"
    :in-theory (enable eval-type
                       eval-type-list
                       type-rename-type-vars
                       type-list-rename-type-vars
                       type-value-rename-type-vars
                       type-value-list-rename-type-vars
                       type-rename-type-vars-no-capture-p
                       type-list-rename-type-vars-no-capture-p
                       type-denv-rename-type-vars
                       type-denv-restrict
                       type-free-ispace-vars
                       type-free-type-vars
                       type-var-set-rename-type-vars-of-difference
                       type-var-set-rename-type-vars-of-delete
                       ispace-denv-restrict-when-denv-ispace-vars-equal-p
                       restrict-of-types-when-denv-type-vars-renamed-p
                       rename-var-string
                       rename-type-var
                       not-reserrp-when-type-valuep
                       not-reserrp-when-type-value-listp
                       type-valuep-when-result-not-error
                       type-value-listp-when-result-not-error
                       type-denv-lookup-type))
   (and acl2::stable-under-simplificationp
        '(:use ((:instance denv-type-vars-renamed-p-necc
                           (var (type-var->var type))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Renamings of expression variables: the value side.
;
; Expression values embed abstract syntax in lambda values (of all three
; kinds) and in boxes, together with the dynamic environments captured for
; the free variables of the lambda bodies, so renaming expression variables
; extends from expressions to expression values, mirroring what
; AST-RENAME-EXPR-VARS does to the corresponding expressions (in particular,
; reducing the renaming by the parameters of a term lambda), and renames the
; captured environments: the keys of their expression-variable maps and,
; recursively, the expression values in them (under the full, unreduced
; renaming, since the captured environment binds the variables that are free
; in the whole abstraction).  The array structure of a value is untouched by
; renaming, so the dimension operations on values --- on which the
; rank-polymorphic application machinery of the evaluator is built ---
; commute with it; this is the support layer for the eventual induction
; over expression evaluation.

; Since the dimension checks descend into the captured environments (see
; CHECK-DIMS-OF-EXPR-DENV), commuting them with the value renamings needs
; two facts about the dimension check on maps of expression values, proved
; here by a locally-generated flag induction over the check's clique: the
; check is two-valued --- :UNIT (or, at the value level, a list of
; dimensions) or (RESERR NIL), since all the primitive failures in the
; clique produce (RESERR NIL) --- and, consequently, insensitive to the
; order in which the map entries are checked: updating a map at a fresh key
; checks the new value and the old map, in whatever order.

(local
 (flag::make-flag flag-check-dims-of-expr-value
                  check-dims-of-expr-value))

(local
 (defthm-flag-check-dims-of-expr-value
   (defthm check-dims-of-expr-value-when-reserrp
     (implies (reserrp (check-dims-of-expr-value val))
              (equal (check-dims-of-expr-value val)
                     (reserr nil)))
     :flag check-dims-of-expr-value)
   (defthm check-dims-of-expr-value-list-when-reserrp
     (implies (reserrp (check-dims-of-expr-value-list vals))
              (equal (check-dims-of-expr-value-list vals)
                     (reserr nil)))
     :flag check-dims-of-expr-value-list)
   (defthm check-dims-of-primop-value-when-reserrp
     (implies (reserrp (check-dims-of-primop-value val))
              (equal (check-dims-of-primop-value val)
                     (reserr nil)))
     :flag check-dims-of-primop-value)
   (defthm check-dims-of-string-expr-value-map-two-valued
     (and (implies (reserrp (check-dims-of-string-expr-value-map map))
                   (equal (check-dims-of-string-expr-value-map map)
                          (reserr nil)))
          (implies (not (reserrp (check-dims-of-string-expr-value-map map)))
                   (equal (check-dims-of-string-expr-value-map map)
                          :unit)))
     :flag check-dims-of-string-expr-value-map)
   (defthm check-dims-of-expr-denv-two-valued
     (and (implies (reserrp (check-dims-of-expr-denv denv))
                   (equal (check-dims-of-expr-denv denv)
                          (reserr nil)))
          (implies (not (reserrp (check-dims-of-expr-denv denv)))
                   (equal (check-dims-of-expr-denv denv)
                          :unit)))
     :flag check-dims-of-expr-denv)
   :hints (("Goal" :in-theory (enable check-dims-of-expr-value
                                      check-dims-of-expr-value-list
                                      check-dims-of-primop-value
                                      check-dims-of-string-expr-value-map
                                      check-dims-of-expr-denv
                                      acl2::nat-listp-when-result-not-error
                                      acl2::nat-list-listp-when-result-not-error
                                      acl2::not-reserrp-when-nat-listp
                                      acl2::not-reserrp-when-nat-list-listp
                                      acl2::nat-listp-of-car-when-nat-list-listp)))))

(defruled check-dims-of-string-expr-value-map-of-update
  (implies (and (stringp key)
                (expr-valuep val)
                (string-expr-value-mapp map)
                (not (set::in key (omap::keys map))))
           (equal (check-dims-of-string-expr-value-map
                   (omap::update key val map))
                  (if (reserrp (check-dims-of-expr-value val))
                      (reserr nil)
                    (check-dims-of-string-expr-value-map map))))
  :induct (omap::size map)
  :expand ((check-dims-of-string-expr-value-map (omap::update key val map)))
  :enable (omap::size
           check-dims-of-string-expr-value-map
           omap::head-val
           omap::keys
           unitp
           unitp-when-result-not-error))

; The injectivity relation for renaming maps, used below for the renaming
; of the keys of the captured environments (and, further below, for the
; preservation of the environment relations under environment extension).
; Injectivity is phrased as a relation (like the environment relations),
; keeping the theorems independent of how the renaming maps are built by
; the uniquification traversal, which will eventually discharge it from
; the freshness of the names it generates.

(acl2::defun-sk rename-var-string-injective-p (renam)
  (forall (name1 name2)
          (implies (and (stringp name1)
                        (stringp name2)
                        (not (equal name1 name2)))
                   (not (equal (rename-var-string name1 renam)
                               (rename-var-string name2 renam)))))
  :rewrite :direct)

(in-theory (disable rename-var-string-injective-p))

(defines expr-value-rename-expr-vars
  ;; The flag function is used by theorems in other books
  ;; (see unique-names-validation.lisp).
  :flag-local nil

  (define expr-value-rename-expr-vars ((val expr-valuep)
                                       (renam string-string-mapp))
    :returns (new-val expr-valuep)
    :parents (renaming-evaluation expr-value-rename-expr-vars)
    :short "Rename expression variables in an expression value."
    :measure (expr-value-count val)
    (expr-value-case
     val
     :base (expr-value-fix val)
     :primop (expr-value-fix val)
     :lambda (b* ((bound (set::insert (var+typevalue->var val.param) nil))
                  (body-renam (omap::delete* bound
                                             (string-string-map-fix renam))))
               (make-expr-value-lambda
                :param val.param
                :body (expr-rename-expr-vars val.body body-renam)
                :type? val.type?
                :denv (expr-denv-rename-expr-vars val.denv renam)))
     :tlambda (make-expr-value-tlambda
               :param val.param
               :body (expr-rename-expr-vars val.body renam)
               :denv (expr-denv-rename-expr-vars val.denv renam))
     :ilambda (make-expr-value-ilambda
               :param val.param
               :body (expr-rename-expr-vars val.body renam)
               :denv (expr-denv-rename-expr-vars val.denv renam))
     :box (make-expr-value-box
           :ispace val.ispace
           :array (expr-value-rename-expr-vars val.array renam)
           :type val.type)
     :vector (expr-value-vector
              (expr-value-list-rename-expr-vars val.elems renam))
     :vector-empty (expr-value-fix val)))

  (define expr-value-list-rename-expr-vars ((vals expr-value-listp)
                                            (renam string-string-mapp))
    :returns (new-vals expr-value-listp)
    :parents (renaming-evaluation expr-value-rename-expr-vars)
    :short "Rename expression variables in a list of expression values."
    :measure (expr-value-list-count vals)
    (if (endp vals)
        nil
      (cons (expr-value-rename-expr-vars (car vals) renam)
            (expr-value-list-rename-expr-vars (cdr vals) renam))))

  (define string-expr-value-map-rename-expr-vars
    ((map string-expr-value-mapp)
     (renam string-string-mapp))
    :returns (new-map string-expr-value-mapp)
    :parents (renaming-evaluation expr-value-rename-expr-vars)
    :short "Rename expression variables in
            a map from expression variables to expression values."
    :long
    (xdoc::topstring
     (xdoc::p
      "Both the expression variable keys and
       the expression values are renamed."))
    :measure (string-expr-value-map-count map)
    (b* ((map (string-expr-value-map-fix map))
         ((when (omap::emptyp map)) nil)
         ((mv var val) (omap::head map)))
      (omap::update (rename-var-string var renam)
                    (expr-value-rename-expr-vars val renam)
                    (string-expr-value-map-rename-expr-vars
                     (omap::tail map) renam))))

  (define expr-denv-rename-expr-vars ((denv expr-denvp)
                                      (renam string-string-mapp))
    :returns (new-denv expr-denvp)
    :parents (renaming-evaluation expr-value-rename-expr-vars)
    :short "Rename expression variables in
            an expression dynamic environment."
    :long
    (xdoc::topstring
     (xdoc::p
      "The type dynamic environment is untouched by
       an expression variable renaming."))
    :measure (expr-denv-count denv)
    (change-expr-denv
     denv
     :exprs (string-expr-value-map-rename-expr-vars
             (expr-denv->exprs denv) renam)))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual expr-value-rename-expr-vars)

  (defret not-reserrp-of-expr-value-rename-expr-vars
    (not (reserrp new-val))
    :fn expr-value-rename-expr-vars
    :hints (("Goal" :in-theory (enable not-reserrp-when-expr-valuep))))

  (defret not-reserrp-of-expr-value-list-rename-expr-vars
    (not (reserrp new-vals))
    :fn expr-value-list-rename-expr-vars
    :hints (("Goal" :in-theory (enable not-reserrp-when-expr-value-listp))))

  (defret expr-value-kind-of-expr-value-rename-expr-vars
    (equal (expr-value-kind new-val)
           (expr-value-kind val))
    :fn expr-value-rename-expr-vars
    :hints (("Goal" :expand ((expr-value-rename-expr-vars val renam)))))

  (defret len-of-expr-value-list-rename-expr-vars
    (equal (len new-vals)
           (len vals))
    :fn expr-value-list-rename-expr-vars
    :hints (("Goal"
             :induct (len vals)
             :in-theory (enable len expr-value-list-rename-expr-vars))))

  ;; Renaming does not change the array structure of a value, so the
  ;; dimension checks and dimensions are unchanged.  The dimension checks
  ;; descend into the captured environments of lambda values, whose keys
  ;; this renaming renames, so the commutation requires the renaming to be
  ;; injective: otherwise two entries of a captured environment could
  ;; collapse into one, hiding a dimension error.

  (defruled not-in-keys-of-string-expr-value-map-rename-expr-vars
    (implies (and (rename-var-string-injective-p renam)
                  (stringp var)
                  (string-expr-value-mapp map)
                  (not (set::in var (omap::keys map))))
             (not (set::in (rename-var-string var renam)
                           (omap::keys
                            (string-expr-value-map-rename-expr-vars
                             map renam)))))
    :induct (omap::size map)
    :expand ((string-expr-value-map-rename-expr-vars map renam))
    :enable (omap::size
             string-expr-value-map-rename-expr-vars
             omap::keys))

  (defthm-expr-value-rename-expr-vars-flag
    (defthm check-dims-of-expr-value-of-expr-value-rename-expr-vars
      (implies (rename-var-string-injective-p renam)
               (equal (check-dims-of-expr-value
                       (expr-value-rename-expr-vars val renam))
                      (check-dims-of-expr-value val)))
      :flag expr-value-rename-expr-vars)
    (defthm check-dims-of-expr-value-list-of-expr-value-list-rename-expr-vars
      (implies (rename-var-string-injective-p renam)
               (equal (check-dims-of-expr-value-list
                       (expr-value-list-rename-expr-vars vals renam))
                      (check-dims-of-expr-value-list vals)))
      :flag expr-value-list-rename-expr-vars)
    (defthm check-dims-of-map-of-string-expr-value-map-rename-expr-vars
      (implies (rename-var-string-injective-p renam)
               (equal (check-dims-of-string-expr-value-map
                       (string-expr-value-map-rename-expr-vars map renam))
                      (check-dims-of-string-expr-value-map map)))
      :flag string-expr-value-map-rename-expr-vars)
    (defthm check-dims-of-expr-denv-of-expr-denv-rename-expr-vars
      (implies (rename-var-string-injective-p renam)
               (equal (check-dims-of-expr-denv
                       (expr-denv-rename-expr-vars denv renam))
                      (check-dims-of-expr-denv denv)))
      :flag expr-denv-rename-expr-vars)
    :hints
    (("Goal"
      :in-theory
      (enable check-dims-of-expr-value
              check-dims-of-expr-value-list
              check-dims-of-string-expr-value-map
              check-dims-of-expr-denv
              check-dims-of-string-expr-value-map-of-update
              not-in-keys-of-string-expr-value-map-rename-expr-vars)))))

(defrule expr-value-wfp-of-expr-value-rename-expr-vars
  (implies (rename-var-string-injective-p renam)
           (equal (expr-value-wfp (expr-value-rename-expr-vars val renam))
                  (expr-value-wfp val)))
  :enable expr-value-wfp)

(defrule expr-value-list-wfp-of-expr-value-list-rename-expr-vars
  (implies (rename-var-string-injective-p renam)
           (equal (expr-value-list-wfp
                   (expr-value-list-rename-expr-vars vals renam))
                  (expr-value-list-wfp vals)))
  :enable expr-value-list-wfp-alt-def)

(defrule dims-of-expr-value-of-expr-value-rename-expr-vars
  (implies (rename-var-string-injective-p renam)
           (equal (dims-of-expr-value (expr-value-rename-expr-vars val renam))
                  (dims-of-expr-value val)))
  :enable (dims-of-expr-value expr-value-wfp))

(defrule dims-of-expr-value-list-of-expr-value-list-rename-expr-vars
  (implies (rename-var-string-injective-p renam)
           (equal (dims-of-expr-value-list
                   (expr-value-list-rename-expr-vars vals renam))
                  (dims-of-expr-value-list vals)))
  :induct (len vals)
  :enable (len
           expr-value-list-rename-expr-vars
           dims-of-expr-value-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Renaming distributes over append (used for the cells operation below).

(defrule expr-value-list-rename-expr-vars-of-append
  (equal (expr-value-list-rename-expr-vars (append vals1 vals2) renam)
         (append (expr-value-list-rename-expr-vars vals1 renam)
                 (expr-value-list-rename-expr-vars vals2 renam)))
  :induct (len vals1)
  :enable (len expr-value-list-rename-expr-vars))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The cells of a renamed value are the renamed cells, in the same two
; phases as the evaluation theorems.

(defthm-cells-at-depth-in-expr-values-flag
  (defthm reserrp-of-cells-at-depth-in-expr-value-of-rename-expr-vars
    (iff (reserrp (cells-at-depth-in-expr-value
                   (expr-value-rename-expr-vars val renam) depth))
         (reserrp (cells-at-depth-in-expr-value val depth)))
    :flag cells-at-depth-in-expr-value)
  (defthm reserrp-of-cells-at-depth-in-expr-value-list-of-rename-expr-vars
    (iff (reserrp (cells-at-depth-in-expr-value-list
                   (expr-value-list-rename-expr-vars vals renam) depth))
         (reserrp (cells-at-depth-in-expr-value-list vals depth)))
    :flag cells-at-depth-in-expr-value-list)
  :hints
  (("Goal"
    :in-theory (enable cells-at-depth-in-expr-value
                       cells-at-depth-in-expr-value-list
                       expr-value-rename-expr-vars
                       expr-value-list-rename-expr-vars
                       not-reserrp-when-expr-value-listp
                       expr-value-listp-when-result-not-error))))

(defthm-cells-at-depth-in-expr-values-flag
  (defthm cells-at-depth-in-expr-value-of-rename-expr-vars
    (implies (not (reserrp (cells-at-depth-in-expr-value val depth)))
             (equal (cells-at-depth-in-expr-value
                     (expr-value-rename-expr-vars val renam) depth)
                    (expr-value-list-rename-expr-vars
                     (cells-at-depth-in-expr-value val depth) renam)))
    :flag cells-at-depth-in-expr-value)
  (defthm cells-at-depth-in-expr-value-list-of-rename-expr-vars
    (implies (not (reserrp (cells-at-depth-in-expr-value-list vals depth)))
             (equal (cells-at-depth-in-expr-value-list
                     (expr-value-list-rename-expr-vars vals renam) depth)
                    (expr-value-list-rename-expr-vars
                     (cells-at-depth-in-expr-value-list vals depth) renam)))
    :flag cells-at-depth-in-expr-value-list)
  :hints
  (("Goal"
    :in-theory (enable cells-at-depth-in-expr-value
                       cells-at-depth-in-expr-value-list
                       expr-value-rename-expr-vars
                       expr-value-list-rename-expr-vars
                       not-reserrp-when-expr-value-listp
                       expr-value-listp-when-result-not-error))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Commutation of renaming with the remaining value-building machinery of the
; evaluator: the arithmetic-flavored list operations (REPEAT, TAKE, NTHCDR,
; LIST-SPLIT, REPEAT-EACH), the array builders (EXPR-VALUE-WITH-EMPTY-DIM,
; EXPR-VALUES-WITH-NONEMPTY-DIMS), and the frame lifting
; (LIFT-EXPR-VALUE-TO-FRAME).

(local (include-book "arithmetic-3/top" :dir :system))

(define expr-value-list-list-rename-expr-vars ((valss expr-value-list-listp)
                                               (renam string-string-mapp))
  :returns (new-valss expr-value-list-listp)
  :short "Rename expression variables in a list of lists of expression values."
  (if (endp valss)
      nil
    (cons (expr-value-list-rename-expr-vars (car valss) renam)
          (expr-value-list-list-rename-expr-vars (cdr valss) renam)))

  ///

  (defret len-of-expr-value-list-list-rename-expr-vars
    (equal (len new-valss)
           (len valss))
    :hints (("Goal" :induct t :in-theory (enable len)))))

(defrule expr-value-list-rename-expr-vars-of-repeat
  (equal (expr-value-list-rename-expr-vars (repeat n val) renam)
         (repeat n (expr-value-rename-expr-vars val renam)))
  :induct (repeat n val)
  :enable (repeat expr-value-list-rename-expr-vars))

(defrule expr-value-list-rename-expr-vars-of-take
  (implies (<= (nfix n) (len vals))
           (equal (expr-value-list-rename-expr-vars (take n vals) renam)
                  (take n (expr-value-list-rename-expr-vars vals renam))))
  :induct (take n vals)
  :enable (take expr-value-list-rename-expr-vars))

(defrule expr-value-list-rename-expr-vars-of-nthcdr
  (equal (expr-value-list-rename-expr-vars (nthcdr n vals) renam)
         (nthcdr n (expr-value-list-rename-expr-vars vals renam)))
  :induct (nthcdr n vals)
  :enable (nthcdr expr-value-list-rename-expr-vars))

; This belongs with REPEAT-EACH itself (see lists.lisp), but is stated here
; to avoid recertifying everything that depends on that book.
(defrule repeat-each-when-zp
  (implies (zp n)
           (equal (repeat-each n list) nil))
  :induct (repeat-each n list)
  :enable (repeat-each repeat))

(defrule expr-value-list-rename-expr-vars-of-repeat-each
  (equal (expr-value-list-rename-expr-vars (repeat-each n cells) renam)
         (repeat-each n (expr-value-list-rename-expr-vars cells renam)))
  :induct (repeat-each n cells)
  :enable (repeat-each expr-value-list-rename-expr-vars)
  :expand ((repeat-each n (expr-value-list-rename-expr-vars cells renam))
           (expr-value-list-rename-expr-vars cells renam))
  :disable (acl2::equal-of-append-repeat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Renamings of ispace variables: the value side.
;
; Expression values embed abstract syntax (lambda bodies) as well as type
; values (lambda parameter and body types, box types, empty-vector element
; types), both of which contain ispace variables, so renaming ispace
; variables extends from types and type values to expression values,
; mirroring what AST-RENAME-ISPACE-VARS does to the corresponding
; expressions (in particular, reducing the renaming at the ispace binders
; of ilambda values).  As with expression-variable renamings, the array
; structure of a value is untouched, so the same commutation properties
; with the evaluator's rank-polymorphic application machinery hold; they
; are stated here and (for the lemmas needing the list arithmetic loaded
; below) after the LIST-SPLIT section.

(define type-value-option-rename-ispace-vars ((tval? type-value-optionp)
                                              (dim-renam string-string-mapp)
                                              (shape-renam string-string-mapp))
  :returns (new-tval? type-value-optionp)
  :short "Rename ispace variables in an optional type value."
  (type-value-option-case
   tval?
   :some (type-value-rename-ispace-vars tval?.val dim-renam shape-renam)
   :none nil)
  ///
  (fty::deffixequiv type-value-option-rename-ispace-vars))

(define var+typevalue-rename-ispace-vars ((param var+typevalue-p)
                                          (dim-renam string-string-mapp)
                                          (shape-renam string-string-mapp))
  :returns (new-param var+typevalue-p)
  :short "Rename ispace variables in the type value of a parameter."
  (b* (((var+typevalue p) param))
    (make-var+typevalue
     :var p.var
     :type (type-value-rename-ispace-vars p.type dim-renam shape-renam)))
  ///
  (fty::deffixequiv var+typevalue-rename-ispace-vars)
  (defret var+typevalue->var-of-var+typevalue-rename-ispace-vars
    (equal (var+typevalue->var new-param)
           (var+typevalue->var param))))

(defines expr-value-rename-ispace-vars
  ;; The flag function is used by theorems in other books
  ;; (see unique-names-validation.lisp).
  :flag-local nil

  (define expr-value-rename-ispace-vars ((val expr-valuep)
                                         (dim-renam string-string-mapp)
                                         (shape-renam string-string-mapp))
    :returns (new-val expr-valuep)
    :parents (renaming-evaluation expr-value-rename-ispace-vars)
    :short "Rename ispace variables in an expression value."
    :measure (expr-value-count val)
    (expr-value-case
     val
     :base (expr-value-fix val)
     :primop (expr-value-fix val)
     :lambda (make-expr-value-lambda
              :param (var+typevalue-rename-ispace-vars val.param
                                                       dim-renam
                                                       shape-renam)
              :body (expr-rename-ispace-vars val.body dim-renam shape-renam)
              :type? (type-value-option-rename-ispace-vars val.type?
                                                           dim-renam
                                                           shape-renam)
              :denv (expr-denv-rename-ispace-vars val.denv
                                                  dim-renam
                                                  shape-renam))
     :tlambda (make-expr-value-tlambda
               :param val.param
               :body (expr-rename-ispace-vars val.body dim-renam shape-renam)
               :denv (expr-denv-rename-ispace-vars val.denv
                                                   dim-renam
                                                   shape-renam))
     :ilambda (b* (((mv & & body-dim-renam body-shape-renam)
                    (dim/shape-rename-remove-bound (set::insert val.param nil)
                                                   dim-renam
                                                   shape-renam)))
                (make-expr-value-ilambda
                 :param val.param
                 :body (expr-rename-ispace-vars val.body
                                                body-dim-renam
                                                body-shape-renam)
                 :denv (expr-denv-rename-ispace-vars val.denv
                                                     dim-renam
                                                     shape-renam)))
     :box (make-expr-value-box
           :ispace val.ispace
           :array (expr-value-rename-ispace-vars val.array
                                                 dim-renam
                                                 shape-renam)
           :type (type-value-rename-ispace-vars val.type
                                                dim-renam
                                                shape-renam))
     :vector (expr-value-vector
              (expr-value-list-rename-ispace-vars val.elems
                                                  dim-renam
                                                  shape-renam))
     :vector-empty (make-expr-value-vector-empty
                    :dims val.dims
                    :elem (type-value-rename-ispace-vars val.elem
                                                         dim-renam
                                                         shape-renam))))

  (define expr-value-list-rename-ispace-vars ((vals expr-value-listp)
                                              (dim-renam string-string-mapp)
                                              (shape-renam string-string-mapp))
    :returns (new-vals expr-value-listp)
    :parents (renaming-evaluation expr-value-rename-ispace-vars)
    :short "Rename ispace variables in a list of expression values."
    :measure (expr-value-list-count vals)
    (if (endp vals)
        nil
      (cons (expr-value-rename-ispace-vars (car vals) dim-renam shape-renam)
            (expr-value-list-rename-ispace-vars (cdr vals)
                                                dim-renam
                                                shape-renam))))

  (define string-expr-value-map-rename-ispace-vars
    ((map string-expr-value-mapp)
     (dim-renam string-string-mapp)
     (shape-renam string-string-mapp))
    :returns (new-map string-expr-value-mapp)
    :parents (renaming-evaluation expr-value-rename-ispace-vars)
    :short "Rename ispace variables in the expression values of
            a map from expression variables to expression values."
    :long
    (xdoc::topstring
     (xdoc::p
      "The keys are expression variables, untouched by an ispace renaming,
       so only the values are renamed."))
    :measure (string-expr-value-map-count map)
    (b* ((map (string-expr-value-map-fix map))
         ((when (omap::emptyp map)) nil)
         ((mv var val) (omap::head map)))
      (omap::update var
                    (expr-value-rename-ispace-vars val dim-renam shape-renam)
                    (string-expr-value-map-rename-ispace-vars
                     (omap::tail map) dim-renam shape-renam))))

  (define expr-denv-rename-ispace-vars ((denv expr-denvp)
                                        (dim-renam string-string-mapp)
                                        (shape-renam string-string-mapp))
    :returns (new-denv expr-denvp)
    :parents (renaming-evaluation expr-value-rename-ispace-vars)
    :short "Rename ispace variables in an expression dynamic environment."
    :measure (expr-denv-count denv)
    (make-expr-denv
     :tenv (type-denv-rename-ispace-vars (expr-denv->tenv denv)
                                         dim-renam
                                         shape-renam)
     :exprs (string-expr-value-map-rename-ispace-vars
             (expr-denv->exprs denv) dim-renam shape-renam)))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual expr-value-rename-ispace-vars)

  (defret not-reserrp-of-expr-value-rename-ispace-vars
    (not (reserrp new-val))
    :fn expr-value-rename-ispace-vars
    :hints (("Goal" :in-theory (enable not-reserrp-when-expr-valuep))))

  (defret not-reserrp-of-expr-value-list-rename-ispace-vars
    (not (reserrp new-vals))
    :fn expr-value-list-rename-ispace-vars
    :hints (("Goal" :in-theory (enable not-reserrp-when-expr-value-listp))))

  (defret expr-value-kind-of-expr-value-rename-ispace-vars
    (equal (expr-value-kind new-val)
           (expr-value-kind val))
    :fn expr-value-rename-ispace-vars
    :hints (("Goal"
             :expand ((expr-value-rename-ispace-vars val
                                                     dim-renam
                                                     shape-renam)))))

  (defret len-of-expr-value-list-rename-ispace-vars
    (equal (len new-vals)
           (len vals))
    :fn expr-value-list-rename-ispace-vars
    :hints (("Goal"
             :induct (len vals)
             :in-theory (enable len expr-value-list-rename-ispace-vars))))

  (defruled keys-of-string-expr-value-map-rename-ispace-vars
    (implies (string-expr-value-mapp map)
             (equal (omap::keys (string-expr-value-map-rename-ispace-vars
                                 map dim-renam shape-renam))
                    (omap::keys map)))
    :induct (omap::size map)
    :expand ((string-expr-value-map-rename-ispace-vars map
                                                       dim-renam
                                                       shape-renam))
    :enable (omap::size
             string-expr-value-map-rename-ispace-vars
             omap::keys))

  (defret-mutual check-dims-of-expr-value-rename-ispace-vars
    (defret check-dims-of-expr-value-of-expr-value-rename-ispace-vars
      (equal (check-dims-of-expr-value new-val)
             (check-dims-of-expr-value val))
      :fn expr-value-rename-ispace-vars)
    (defret check-dims-of-expr-value-list-of-expr-value-list-rename-ispace-vars
      (equal (check-dims-of-expr-value-list new-vals)
             (check-dims-of-expr-value-list vals))
      :fn expr-value-list-rename-ispace-vars)
    (defret check-dims-of-map-of-string-expr-value-map-rename-ispace-vars
      (equal (check-dims-of-string-expr-value-map new-map)
             (check-dims-of-string-expr-value-map map))
      :fn string-expr-value-map-rename-ispace-vars)
    (defret check-dims-of-expr-denv-of-expr-denv-rename-ispace-vars
      (equal (check-dims-of-expr-denv new-denv)
             (check-dims-of-expr-denv denv))
      :fn expr-denv-rename-ispace-vars)
    :hints
    (("Goal"
      :in-theory
      (enable check-dims-of-expr-value
              check-dims-of-expr-value-list
              check-dims-of-string-expr-value-map
              check-dims-of-expr-denv
              check-dims-of-string-expr-value-map-of-update
              keys-of-string-expr-value-map-rename-ispace-vars)))))

(defrule expr-value-wfp-of-expr-value-rename-ispace-vars
  (equal (expr-value-wfp (expr-value-rename-ispace-vars val
                                                        dim-renam
                                                        shape-renam))
         (expr-value-wfp val))
  :enable expr-value-wfp)

(defrule expr-value-list-wfp-of-expr-value-list-rename-ispace-vars
  (equal (expr-value-list-wfp (expr-value-list-rename-ispace-vars vals
                                                                  dim-renam
                                                                  shape-renam))
         (expr-value-list-wfp vals))
  :enable expr-value-list-wfp-alt-def)

(defrule dims-of-expr-value-of-expr-value-rename-ispace-vars
  (equal (dims-of-expr-value (expr-value-rename-ispace-vars val
                                                            dim-renam
                                                            shape-renam))
         (dims-of-expr-value val))
  :enable (dims-of-expr-value expr-value-wfp))

(defrule dims-of-expr-value-list-of-expr-value-list-rename-ispace-vars
  (equal (dims-of-expr-value-list
          (expr-value-list-rename-ispace-vars vals dim-renam shape-renam))
         (dims-of-expr-value-list vals))
  :induct (len vals)
  :enable (len
           expr-value-list-rename-ispace-vars
           dims-of-expr-value-list))

(defrule consp-of-expr-value-list-rename-ispace-vars
  (equal (consp (expr-value-list-rename-ispace-vars vals
                                                    dim-renam
                                                    shape-renam))
         (consp vals))
  :expand ((expr-value-list-rename-ispace-vars vals dim-renam shape-renam)))

(defrule expr-value-list-rename-ispace-vars-of-append
  (equal (expr-value-list-rename-ispace-vars (append vals1 vals2)
                                             dim-renam shape-renam)
         (append (expr-value-list-rename-ispace-vars vals1
                                                     dim-renam shape-renam)
                 (expr-value-list-rename-ispace-vars vals2
                                                     dim-renam shape-renam)))
  :induct (len vals1)
  :enable (len expr-value-list-rename-ispace-vars))

(defthm-cells-at-depth-in-expr-values-flag
  (defthm reserrp-of-cells-at-depth-in-expr-value-of-rename-ispace-vars
    (iff (reserrp (cells-at-depth-in-expr-value
                   (expr-value-rename-ispace-vars val dim-renam shape-renam)
                   depth))
         (reserrp (cells-at-depth-in-expr-value val depth)))
    :flag cells-at-depth-in-expr-value)
  (defthm reserrp-of-cells-at-depth-in-expr-value-list-of-rename-ispace-vars
    (iff (reserrp (cells-at-depth-in-expr-value-list
                   (expr-value-list-rename-ispace-vars vals
                                                       dim-renam shape-renam)
                   depth))
         (reserrp (cells-at-depth-in-expr-value-list vals depth)))
    :flag cells-at-depth-in-expr-value-list)
  :hints
  (("Goal"
    :in-theory (enable cells-at-depth-in-expr-value
                       cells-at-depth-in-expr-value-list
                       expr-value-rename-ispace-vars
                       expr-value-list-rename-ispace-vars
                       not-reserrp-when-expr-value-listp
                       expr-value-listp-when-result-not-error))))

(defthm-cells-at-depth-in-expr-values-flag
  (defthm cells-at-depth-in-expr-value-of-rename-ispace-vars
    (implies (not (reserrp (cells-at-depth-in-expr-value val depth)))
             (equal (cells-at-depth-in-expr-value
                     (expr-value-rename-ispace-vars val dim-renam shape-renam)
                     depth)
                    (expr-value-list-rename-ispace-vars
                     (cells-at-depth-in-expr-value val depth)
                     dim-renam
                     shape-renam)))
    :flag cells-at-depth-in-expr-value)
  (defthm cells-at-depth-in-expr-value-list-of-rename-ispace-vars
    (implies (not (reserrp (cells-at-depth-in-expr-value-list vals depth)))
             (equal (cells-at-depth-in-expr-value-list
                     (expr-value-list-rename-ispace-vars vals
                                                         dim-renam shape-renam)
                     depth)
                    (expr-value-list-rename-ispace-vars
                     (cells-at-depth-in-expr-value-list vals depth)
                     dim-renam
                     shape-renam)))
    :flag cells-at-depth-in-expr-value-list)
  :hints
  (("Goal"
    :in-theory (enable cells-at-depth-in-expr-value
                       cells-at-depth-in-expr-value-list
                       expr-value-rename-ispace-vars
                       expr-value-list-rename-ispace-vars
                       not-reserrp-when-expr-value-listp
                       expr-value-listp-when-result-not-error))))

(define expr-value-list-list-rename-ispace-vars ((valss expr-value-list-listp)
                                                 (dim-renam string-string-mapp)
                                                 (shape-renam string-string-mapp))
  :returns (new-valss expr-value-list-listp)
  :short "Rename ispace variables in a list of lists of expression values."
  (if (endp valss)
      nil
    (cons (expr-value-list-rename-ispace-vars (car valss)
                                              dim-renam shape-renam)
          (expr-value-list-list-rename-ispace-vars (cdr valss)
                                                   dim-renam shape-renam))
  )
  ///
  (defret len-of-expr-value-list-list-rename-ispace-vars
    (equal (len new-valss)
           (len valss))
    :hints (("Goal" :induct t :in-theory (enable len)))))

(defrule expr-value-list-rename-ispace-vars-of-repeat
  (equal (expr-value-list-rename-ispace-vars (repeat n val)
                                             dim-renam shape-renam)
         (repeat n (expr-value-rename-ispace-vars val dim-renam shape-renam)))
  :induct (repeat n val)
  :enable (repeat expr-value-list-rename-ispace-vars))

(defrule expr-value-list-rename-ispace-vars-of-take
  (implies (<= (nfix n) (len vals))
           (equal (expr-value-list-rename-ispace-vars (take n vals)
                                                      dim-renam shape-renam)
                  (take n (expr-value-list-rename-ispace-vars
                           vals dim-renam shape-renam))))
  :induct (take n vals)
  :enable (take expr-value-list-rename-ispace-vars))

(defrule expr-value-list-rename-ispace-vars-of-nthcdr
  (equal (expr-value-list-rename-ispace-vars (nthcdr n vals)
                                             dim-renam shape-renam)
         (nthcdr n (expr-value-list-rename-ispace-vars vals
                                                       dim-renam shape-renam)))
  :induct (nthcdr n vals)
  :enable (nthcdr expr-value-list-rename-ispace-vars))

(defrule expr-value-list-rename-ispace-vars-of-repeat-each
  (equal (expr-value-list-rename-ispace-vars (repeat-each n cells)
                                             dim-renam shape-renam)
         (repeat-each n (expr-value-list-rename-ispace-vars
                         cells dim-renam shape-renam)))
  :induct (repeat-each n cells)
  :enable (repeat-each expr-value-list-rename-ispace-vars)
  :expand ((repeat-each n (expr-value-list-rename-ispace-vars
                           cells dim-renam shape-renam))
           (expr-value-list-rename-ispace-vars cells dim-renam shape-renam))
  :disable (acl2::equal-of-append-repeat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Renamings of type variables: the value side.
;
; Expression values embed abstract syntax (lambda bodies) as well as type
; values (lambda parameter and body types, box types, empty-vector element
; types), both of which contain type variables, so renaming type
; variables extends from types and type values to expression values,
; mirroring what AST-RENAME-TYPE-VARS does to the corresponding
; expressions (in particular, reducing the renaming at the type binders
; of tlambda values).  As with expression-variable renamings, the array
; structure of a value is untouched, so the same commutation properties
; with the evaluator's rank-polymorphic application machinery hold; they
; are stated here and (for the lemmas needing the list arithmetic loaded
; below) after the LIST-SPLIT section.

(define type-value-option-rename-type-vars ((tval? type-value-optionp)
                                              (atom-renam string-string-mapp)
                                              (array-renam string-string-mapp))
  :returns (new-tval? type-value-optionp)
  :short "Rename type variables in an optional type value."
  (type-value-option-case
   tval?
   :some (type-value-rename-type-vars tval?.val atom-renam array-renam)
   :none nil)
  ///
  (fty::deffixequiv type-value-option-rename-type-vars))

(define var+typevalue-rename-type-vars ((param var+typevalue-p)
                                        (atom-renam string-string-mapp)
                                        (array-renam string-string-mapp))
  :returns (new-param var+typevalue-p)
  :short "Rename type variables in the type value of a parameter."
  (b* (((var+typevalue p) param))
    (make-var+typevalue
     :var p.var
     :type (type-value-rename-type-vars p.type atom-renam array-renam)))
  ///
  (fty::deffixequiv var+typevalue-rename-type-vars)
  (defret var+typevalue->var-of-var+typevalue-rename-type-vars
    (equal (var+typevalue->var new-param)
           (var+typevalue->var param))))

(defines expr-value-rename-type-vars
  ;; The flag function is used by theorems in other books
  ;; (see unique-names-validation.lisp).
  :flag-local nil

  (define expr-value-rename-type-vars ((val expr-valuep)
                                       (atom-renam string-string-mapp)
                                       (array-renam string-string-mapp))
    :returns (new-val expr-valuep)
    :parents (renaming-evaluation expr-value-rename-type-vars)
    :short "Rename type variables in an expression value."
    :measure (expr-value-count val)
    (expr-value-case
     val
     :base (expr-value-fix val)
     :primop (expr-value-fix val)
     :lambda (make-expr-value-lambda
              :param (var+typevalue-rename-type-vars val.param
                                                     atom-renam
                                                     array-renam)
              :body (expr-rename-type-vars val.body atom-renam array-renam)
              :type? (type-value-option-rename-type-vars val.type?
                                                         atom-renam
                                                         array-renam)
              :denv (expr-denv-rename-type-vars val.denv
                                                atom-renam
                                                array-renam))
     :tlambda (b* (((mv & & body-atom-renam body-array-renam)
                    (atom/array-rename-remove-bound (set::insert val.param nil)
                                                    atom-renam
                                                    array-renam)))
                (make-expr-value-tlambda
                 :param val.param
                 :body (expr-rename-type-vars val.body
                                              body-atom-renam
                                              body-array-renam)
                 :denv (expr-denv-rename-type-vars val.denv
                                                   atom-renam
                                                   array-renam)))
     :ilambda (make-expr-value-ilambda
               :param val.param
               :body (expr-rename-type-vars val.body atom-renam array-renam)
               :denv (expr-denv-rename-type-vars val.denv
                                                 atom-renam
                                                 array-renam))
     :box (make-expr-value-box
           :ispace val.ispace
           :array (expr-value-rename-type-vars val.array
                                               atom-renam
                                               array-renam)
           :type (type-value-rename-type-vars val.type
                                              atom-renam
                                              array-renam))
     :vector (expr-value-vector
              (expr-value-list-rename-type-vars val.elems
                                                atom-renam
                                                array-renam))
     :vector-empty (make-expr-value-vector-empty
                    :dims val.dims
                    :elem (type-value-rename-type-vars val.elem
                                                       atom-renam
                                                       array-renam))))

  (define expr-value-list-rename-type-vars ((vals expr-value-listp)
                                            (atom-renam string-string-mapp)
                                            (array-renam string-string-mapp))
    :returns (new-vals expr-value-listp)
    :parents (renaming-evaluation expr-value-rename-type-vars)
    :short "Rename type variables in a list of expression values."
    :measure (expr-value-list-count vals)
    (if (endp vals)
        nil
      (cons (expr-value-rename-type-vars (car vals) atom-renam array-renam)
            (expr-value-list-rename-type-vars (cdr vals)
                                              atom-renam
                                              array-renam))))

  (define string-expr-value-map-rename-type-vars
    ((map string-expr-value-mapp)
     (atom-renam string-string-mapp)
     (array-renam string-string-mapp))
    :returns (new-map string-expr-value-mapp)
    :parents (renaming-evaluation expr-value-rename-type-vars)
    :short "Rename type variables in the expression values of
            a map from expression variables to expression values."
    :long
    (xdoc::topstring
     (xdoc::p
      "The keys are expression variables, untouched by a type renaming,
       so only the values are renamed."))
    :measure (string-expr-value-map-count map)
    (b* ((map (string-expr-value-map-fix map))
         ((when (omap::emptyp map)) nil)
         ((mv var val) (omap::head map)))
      (omap::update var
                    (expr-value-rename-type-vars val atom-renam array-renam)
                    (string-expr-value-map-rename-type-vars
                     (omap::tail map) atom-renam array-renam))))

  (define expr-denv-rename-type-vars ((denv expr-denvp)
                                      (atom-renam string-string-mapp)
                                      (array-renam string-string-mapp))
    :returns (new-denv expr-denvp)
    :parents (renaming-evaluation expr-value-rename-type-vars)
    :short "Rename type variables in an expression dynamic environment."
    :measure (expr-denv-count denv)
    (make-expr-denv
     :tenv (type-denv-rename-type-vars (expr-denv->tenv denv)
                                       atom-renam
                                       array-renam)
     :exprs (string-expr-value-map-rename-type-vars
             (expr-denv->exprs denv) atom-renam array-renam)))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual expr-value-rename-type-vars)

  (defret not-reserrp-of-expr-value-rename-type-vars
    (not (reserrp new-val))
    :fn expr-value-rename-type-vars
    :hints (("Goal" :in-theory (enable not-reserrp-when-expr-valuep))))

  (defret not-reserrp-of-expr-value-list-rename-type-vars
    (not (reserrp new-vals))
    :fn expr-value-list-rename-type-vars
    :hints (("Goal" :in-theory (enable not-reserrp-when-expr-value-listp))))

  (defret expr-value-kind-of-expr-value-rename-type-vars
    (equal (expr-value-kind new-val)
           (expr-value-kind val))
    :fn expr-value-rename-type-vars
    :hints (("Goal"
             :expand ((expr-value-rename-type-vars val
                                                   atom-renam
                                                   array-renam)))))

  (defret len-of-expr-value-list-rename-type-vars
    (equal (len new-vals)
           (len vals))
    :fn expr-value-list-rename-type-vars
    :hints (("Goal"
             :induct (len vals)
             :in-theory (enable len expr-value-list-rename-type-vars))))

  (defruled keys-of-string-expr-value-map-rename-type-vars
    (implies (string-expr-value-mapp map)
             (equal (omap::keys (string-expr-value-map-rename-type-vars
                                 map atom-renam array-renam))
                    (omap::keys map)))
    :induct (omap::size map)
    :expand ((string-expr-value-map-rename-type-vars map
                                                     atom-renam
                                                     array-renam))
    :enable (omap::size
             string-expr-value-map-rename-type-vars
             omap::keys))

  (defret-mutual check-dims-of-expr-value-rename-type-vars
    (defret check-dims-of-expr-value-of-expr-value-rename-type-vars
      (equal (check-dims-of-expr-value new-val)
             (check-dims-of-expr-value val))
      :fn expr-value-rename-type-vars)
    (defret check-dims-of-expr-value-list-of-expr-value-list-rename-type-vars
      (equal (check-dims-of-expr-value-list new-vals)
             (check-dims-of-expr-value-list vals))
      :fn expr-value-list-rename-type-vars)
    (defret check-dims-of-map-of-string-expr-value-map-rename-type-vars
      (equal (check-dims-of-string-expr-value-map new-map)
             (check-dims-of-string-expr-value-map map))
      :fn string-expr-value-map-rename-type-vars)
    (defret check-dims-of-expr-denv-of-expr-denv-rename-type-vars
      (equal (check-dims-of-expr-denv new-denv)
             (check-dims-of-expr-denv denv))
      :fn expr-denv-rename-type-vars)
    :hints
    (("Goal"
      :in-theory
      (enable check-dims-of-expr-value
              check-dims-of-expr-value-list
              check-dims-of-string-expr-value-map
              check-dims-of-expr-denv
              check-dims-of-string-expr-value-map-of-update
              keys-of-string-expr-value-map-rename-type-vars)))))

(defrule expr-value-wfp-of-expr-value-rename-type-vars
  (equal (expr-value-wfp (expr-value-rename-type-vars val
                                                        atom-renam
                                                        array-renam))
         (expr-value-wfp val))
  :enable expr-value-wfp)

(defrule expr-value-list-wfp-of-expr-value-list-rename-type-vars
  (equal (expr-value-list-wfp (expr-value-list-rename-type-vars vals
                                                                  atom-renam
                                                                  array-renam))
         (expr-value-list-wfp vals))
  :enable expr-value-list-wfp-alt-def)

(defrule dims-of-expr-value-of-expr-value-rename-type-vars
  (equal (dims-of-expr-value (expr-value-rename-type-vars val
                                                            atom-renam
                                                            array-renam))
         (dims-of-expr-value val))
  :enable (dims-of-expr-value expr-value-wfp))

(defrule dims-of-expr-value-list-of-expr-value-list-rename-type-vars
  (equal (dims-of-expr-value-list
          (expr-value-list-rename-type-vars vals atom-renam array-renam))
         (dims-of-expr-value-list vals))
  :induct (len vals)
  :enable (len
           expr-value-list-rename-type-vars
           dims-of-expr-value-list))

(defrule consp-of-expr-value-list-rename-type-vars
  (equal (consp (expr-value-list-rename-type-vars vals
                                                    atom-renam
                                                    array-renam))
         (consp vals))
  :expand ((expr-value-list-rename-type-vars vals atom-renam array-renam)))

(defrule expr-value-list-rename-type-vars-of-append
  (equal (expr-value-list-rename-type-vars (append vals1 vals2)
                                             atom-renam array-renam)
         (append (expr-value-list-rename-type-vars vals1
                                                     atom-renam array-renam)
                 (expr-value-list-rename-type-vars vals2
                                                     atom-renam array-renam)))
  :induct (len vals1)
  :enable (len expr-value-list-rename-type-vars))

(defthm-cells-at-depth-in-expr-values-flag
  (defthm reserrp-of-cells-at-depth-in-expr-value-of-rename-type-vars
    (iff (reserrp (cells-at-depth-in-expr-value
                   (expr-value-rename-type-vars val atom-renam array-renam)
                   depth))
         (reserrp (cells-at-depth-in-expr-value val depth)))
    :flag cells-at-depth-in-expr-value)
  (defthm reserrp-of-cells-at-depth-in-expr-value-list-of-rename-type-vars
    (iff (reserrp (cells-at-depth-in-expr-value-list
                   (expr-value-list-rename-type-vars vals
                                                       atom-renam array-renam)
                   depth))
         (reserrp (cells-at-depth-in-expr-value-list vals depth)))
    :flag cells-at-depth-in-expr-value-list)
  :hints
  (("Goal"
    :in-theory (enable cells-at-depth-in-expr-value
                       cells-at-depth-in-expr-value-list
                       expr-value-rename-type-vars
                       expr-value-list-rename-type-vars
                       not-reserrp-when-expr-value-listp
                       expr-value-listp-when-result-not-error))))

(defthm-cells-at-depth-in-expr-values-flag
  (defthm cells-at-depth-in-expr-value-of-rename-type-vars
    (implies (not (reserrp (cells-at-depth-in-expr-value val depth)))
             (equal (cells-at-depth-in-expr-value
                     (expr-value-rename-type-vars val atom-renam array-renam)
                     depth)
                    (expr-value-list-rename-type-vars
                     (cells-at-depth-in-expr-value val depth)
                     atom-renam
                     array-renam)))
    :flag cells-at-depth-in-expr-value)
  (defthm cells-at-depth-in-expr-value-list-of-rename-type-vars
    (implies (not (reserrp (cells-at-depth-in-expr-value-list vals depth)))
             (equal (cells-at-depth-in-expr-value-list
                     (expr-value-list-rename-type-vars vals
                                                         atom-renam array-renam)
                     depth)
                    (expr-value-list-rename-type-vars
                     (cells-at-depth-in-expr-value-list vals depth)
                     atom-renam
                     array-renam)))
    :flag cells-at-depth-in-expr-value-list)
  :hints
  (("Goal"
    :in-theory (enable cells-at-depth-in-expr-value
                       cells-at-depth-in-expr-value-list
                       expr-value-rename-type-vars
                       expr-value-list-rename-type-vars
                       not-reserrp-when-expr-value-listp
                       expr-value-listp-when-result-not-error))))

(define expr-value-list-list-rename-type-vars ((valss expr-value-list-listp)
                                                 (atom-renam string-string-mapp)
                                                 (array-renam string-string-mapp))
  :returns (new-valss expr-value-list-listp)
  :short "Rename type variables in a list of lists of expression values."
  (if (endp valss)
      nil
    (cons (expr-value-list-rename-type-vars (car valss)
                                              atom-renam array-renam)
          (expr-value-list-list-rename-type-vars (cdr valss)
                                                   atom-renam array-renam))
  )
  ///
  (defret len-of-expr-value-list-list-rename-type-vars
    (equal (len new-valss)
           (len valss))
    :hints (("Goal" :induct t :in-theory (enable len)))))

(defrule expr-value-list-rename-type-vars-of-repeat
  (equal (expr-value-list-rename-type-vars (repeat n val)
                                             atom-renam array-renam)
         (repeat n (expr-value-rename-type-vars val atom-renam array-renam)))
  :induct (repeat n val)
  :enable (repeat expr-value-list-rename-type-vars))

(defrule expr-value-list-rename-type-vars-of-take
  (implies (<= (nfix n) (len vals))
           (equal (expr-value-list-rename-type-vars (take n vals)
                                                      atom-renam array-renam)
                  (take n (expr-value-list-rename-type-vars
                           vals atom-renam array-renam))))
  :induct (take n vals)
  :enable (take expr-value-list-rename-type-vars))

(defrule expr-value-list-rename-type-vars-of-nthcdr
  (equal (expr-value-list-rename-type-vars (nthcdr n vals)
                                             atom-renam array-renam)
         (nthcdr n (expr-value-list-rename-type-vars vals
                                                       atom-renam array-renam)))
  :induct (nthcdr n vals)
  :enable (nthcdr expr-value-list-rename-type-vars))

(defrule expr-value-list-rename-type-vars-of-repeat-each
  (equal (expr-value-list-rename-type-vars (repeat-each n cells)
                                             atom-renam array-renam)
         (repeat-each n (expr-value-list-rename-type-vars
                         cells atom-renam array-renam)))
  :induct (repeat-each n cells)
  :enable (repeat-each expr-value-list-rename-type-vars)
  :expand ((repeat-each n (expr-value-list-rename-type-vars
                           cells atom-renam array-renam))
           (expr-value-list-rename-type-vars cells atom-renam array-renam))
  :disable (acl2::equal-of-append-repeat))

(local (include-book "arithmetic"))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

(defrule consp-of-expr-value-list-rename-expr-vars
  (equal (consp (expr-value-list-rename-expr-vars vals renam))
         (consp vals))
  :expand ((expr-value-list-rename-expr-vars vals renam)))

(defrule list-split-of-expr-value-list-rename-expr-vars
  (implies (integerp (/ (len vals) (pos-fix chunk)))
           (equal (list-split (expr-value-list-rename-expr-vars vals renam)
                              chunk)
                  (expr-value-list-list-rename-expr-vars
                   (list-split vals chunk) renam)))
  :induct (list-split vals chunk)
  :enable (list-split
           expr-value-list-list-rename-expr-vars
           fix nfix
           lt-to-zero-when-divided-by-pos)
  :hints ('(:use (:instance integerp-of-div-of-diff
                            (x (len vals))
                            (c (pos-fix chunk))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The empty-dimension builder produces values with no embedded abstract
; syntax, so renaming leaves them unchanged.

(defrule expr-value-rename-expr-vars-of-expr-value-with-empty-dim
  (equal (expr-value-rename-expr-vars (expr-value-with-empty-dim dims elem)
                                      renam)
         (expr-value-with-empty-dim dims elem))
  :induct (expr-value-with-empty-dim dims elem)
  :enable (expr-value-with-empty-dim
           expr-value-rename-expr-vars
           expr-value-list-rename-expr-vars))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The nonempty-dimension builders assemble values whose elements are the
; given values, so building from renamed elements yields the renamed result.
; The hypotheses mirror the guards that relate the number of values to the
; product of the dimensions, which ensure that the LIST-SPLIT chunking
; performed by the builders is exact.

; The following two lemmas are as in the
; CHECK-DIMS-OF-EXPR-VALUES-WITH-NONEMPTY-DIMS proof (see evaluation.lisp).

(defruledl lemma1
  (implies (and (nat-listp dims)
                (not (member-equal 0 dims))
                (consp dims)
                (equal (len vals) (nat-list-product dims)))
           (posp (* (/ (car dims)) (len vals))))
  :enable posp
  :use nat-list-product-divided-by-car)

(defruledl lemma2
  (implies (and (expr-value-listp vals)
                (nat-listp dims)
                (not (member-equal 0 dims))
                (consp dims)
                (equal (len vals) (nat-list-product dims)))
           (expr-value-list-listp
            (list-split vals (* (/ (car dims)) (len vals)))))
  :enable posp
  :disable expr-value-list-listp-of-list-split
  :use (nat-list-product-divided-by-car
        (:instance expr-value-list-listp-of-list-split
                   (n (/ (len vals) (car dims))))))

(defthm-expr-values-with-nonempty-dims-flag
  (defthm expr-value-rename-expr-vars-of-expr-value-with-nonempty-dims
    (implies (and (nat-listp dims)
                  (expr-value-listp vals)
                  (not (member-equal 0 dims))
                  (equal (len vals) (nat-list-product dims)))
             (equal (expr-value-rename-expr-vars
                     (expr-value-with-nonempty-dims dims vals) renam)
                    (expr-value-with-nonempty-dims
                     dims
                     (expr-value-list-rename-expr-vars vals renam))))
    :flag expr-value-with-nonempty-dims)
  (defthm expr-value-list-rename-expr-vars-of-expr-value-list-with-nonempty-dims
    (implies (and (nat-listp dims)
                  (expr-value-list-listp valss)
                  (not (member-equal 0 dims))
                  (all-of-len-p valss (nat-list-product dims)))
             (equal (expr-value-list-rename-expr-vars
                     (expr-value-list-with-nonempty-dims dims valss) renam)
                    (expr-value-list-with-nonempty-dims
                     dims
                     (expr-value-list-list-rename-expr-vars valss renam))))
    :flag expr-value-list-with-nonempty-dims)
  :hints (("Goal"
           :in-theory (enable expr-value-with-nonempty-dims
                              expr-value-list-with-nonempty-dims
                              expr-value-rename-expr-vars
                              expr-value-list-rename-expr-vars
                              expr-value-list-list-rename-expr-vars
                              nat-list-product-of-cdr-to-ratio
                              all-of-len-p
                              pos-fix
                              lemma1
                              lemma2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Frame lifting consists of taking cells and replicating them, both of which
; have been shown above to commute with renaming, in the same two phases as
; the evaluation theorems.

(defrule reserrp-of-lift-expr-value-to-frame-of-rename-expr-vars
  (iff (reserrp (lift-expr-value-to-frame
                 (expr-value-rename-expr-vars val renam) frame pframe))
       (reserrp (lift-expr-value-to-frame val frame pframe)))
  :enable (lift-expr-value-to-frame
           not-reserrp-when-expr-value-listp
           expr-value-listp-when-result-not-error))

(defrule lift-expr-value-to-frame-of-expr-value-rename-expr-vars
  (implies (not (reserrp (lift-expr-value-to-frame val frame pframe)))
           (equal (lift-expr-value-to-frame
                   (expr-value-rename-expr-vars val renam) frame pframe)
                  (expr-value-list-rename-expr-vars
                   (lift-expr-value-to-frame val frame pframe) renam)))
  :enable (lift-expr-value-to-frame
           not-reserrp-when-expr-value-listp
           expr-value-listp-when-result-not-error))

(defrule reserrp-of-lift-expr-value-list-to-frame-of-rename-expr-vars
  (iff (reserrp (lift-expr-value-list-to-frame
                 (expr-value-list-rename-expr-vars vals renam) frames pframe))
       (reserrp (lift-expr-value-list-to-frame vals frames pframe)))
  :induct (lift-expr-value-list-to-frame vals frames pframe)
  :enable (lift-expr-value-list-to-frame
           expr-value-list-rename-expr-vars
           expr-value-list-listp-of-cons
           not-reserrp-when-expr-value-list-listp
           expr-value-list-listp-when-result-not-error
           expr-value-listp-when-result-not-error))

(defrule lift-expr-value-list-to-frame-of-expr-value-list-rename-expr-vars
  (implies (not (reserrp (lift-expr-value-list-to-frame vals frames pframe)))
           (equal (lift-expr-value-list-to-frame
                   (expr-value-list-rename-expr-vars vals renam) frames pframe)
                  (expr-value-list-list-rename-expr-vars
                   (lift-expr-value-list-to-frame vals frames pframe) renam)))
  :induct (lift-expr-value-list-to-frame vals frames pframe)
  :enable (lift-expr-value-list-to-frame
           expr-value-list-rename-expr-vars
           expr-value-list-list-rename-expr-vars
           not-reserrp-when-expr-value-list-listp
           expr-value-list-listp-when-result-not-error))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Commutation of the ispace-variable renaming of values with the remaining
; application machinery, in the same way as for expression-variable
; renamings above; the empty-dimension builder embeds a type value, whose
; renaming it commutes with.

(defrule list-split-of-expr-value-list-rename-ispace-vars
  (implies (integerp (/ (len vals) (pos-fix chunk)))
           (equal (list-split (expr-value-list-rename-ispace-vars
                               vals dim-renam shape-renam)
                              chunk)
                  (expr-value-list-list-rename-ispace-vars
                   (list-split vals chunk) dim-renam shape-renam)))
  :induct (list-split vals chunk)
  :enable (list-split
           expr-value-list-list-rename-ispace-vars
           fix nfix
           lt-to-zero-when-divided-by-pos)
  :hints ('(:use (:instance integerp-of-div-of-diff
                            (x (len vals))
                            (c (pos-fix chunk))))))

(defrule expr-value-rename-ispace-vars-of-expr-value-with-empty-dim
  (equal (expr-value-rename-ispace-vars (expr-value-with-empty-dim dims elem)
                                        dim-renam shape-renam)
         (expr-value-with-empty-dim
          dims
          (type-value-rename-ispace-vars elem dim-renam shape-renam)))
  :induct (expr-value-with-empty-dim dims elem)
  :enable (expr-value-with-empty-dim
           expr-value-rename-ispace-vars
           expr-value-list-rename-ispace-vars))

(defthm-expr-values-with-nonempty-dims-flag
  (defthm expr-value-rename-ispace-vars-of-expr-value-with-nonempty-dims
    (implies (and (nat-listp dims)
                  (expr-value-listp vals)
                  (not (member-equal 0 dims))
                  (equal (len vals) (nat-list-product dims)))
             (equal (expr-value-rename-ispace-vars
                     (expr-value-with-nonempty-dims dims vals)
                     dim-renam shape-renam)
                    (expr-value-with-nonempty-dims
                     dims
                     (expr-value-list-rename-ispace-vars vals
                                                         dim-renam
                                                         shape-renam))))
    :flag expr-value-with-nonempty-dims)
  (defthm expr-value-list-rename-ispace-vars-of-expr-value-list-with-nonempty-dims
    (implies (and (nat-listp dims)
                  (expr-value-list-listp valss)
                  (not (member-equal 0 dims))
                  (all-of-len-p valss (nat-list-product dims)))
             (equal (expr-value-list-rename-ispace-vars
                     (expr-value-list-with-nonempty-dims dims valss)
                     dim-renam shape-renam)
                    (expr-value-list-with-nonempty-dims
                     dims
                     (expr-value-list-list-rename-ispace-vars valss
                                                              dim-renam
                                                              shape-renam))))
    :flag expr-value-list-with-nonempty-dims)
  :hints (("Goal"
           :in-theory (enable expr-value-with-nonempty-dims
                              expr-value-list-with-nonempty-dims
                              expr-value-rename-ispace-vars
                              expr-value-list-rename-ispace-vars
                              expr-value-list-list-rename-ispace-vars
                              nat-list-product-of-cdr-to-ratio
                              all-of-len-p
                              pos-fix
                              lemma1
                              lemma2))))

(defrule reserrp-of-lift-expr-value-to-frame-of-rename-ispace-vars
  (iff (reserrp (lift-expr-value-to-frame
                 (expr-value-rename-ispace-vars val dim-renam shape-renam)
                 frame pframe))
       (reserrp (lift-expr-value-to-frame val frame pframe)))
  :enable (lift-expr-value-to-frame
           not-reserrp-when-expr-value-listp
           expr-value-listp-when-result-not-error))

(defrule lift-expr-value-to-frame-of-expr-value-rename-ispace-vars
  (implies (not (reserrp (lift-expr-value-to-frame val frame pframe)))
           (equal (lift-expr-value-to-frame
                   (expr-value-rename-ispace-vars val dim-renam shape-renam)
                   frame pframe)
                  (expr-value-list-rename-ispace-vars
                   (lift-expr-value-to-frame val frame pframe)
                   dim-renam shape-renam)))
  :enable (lift-expr-value-to-frame
           not-reserrp-when-expr-value-listp
           expr-value-listp-when-result-not-error))

(defrule reserrp-of-lift-expr-value-list-to-frame-of-rename-ispace-vars
  (iff (reserrp (lift-expr-value-list-to-frame
                 (expr-value-list-rename-ispace-vars vals
                                                     dim-renam shape-renam)
                 frames pframe))
       (reserrp (lift-expr-value-list-to-frame vals frames pframe)))
  :induct (lift-expr-value-list-to-frame vals frames pframe)
  :enable (lift-expr-value-list-to-frame
           expr-value-list-rename-ispace-vars
           expr-value-list-listp-of-cons
           not-reserrp-when-expr-value-list-listp
           expr-value-list-listp-when-result-not-error
           expr-value-listp-when-result-not-error))

(defrule lift-expr-value-list-to-frame-of-expr-value-list-rename-ispace-vars
  (implies (not (reserrp (lift-expr-value-list-to-frame vals frames pframe)))
           (equal (lift-expr-value-list-to-frame
                   (expr-value-list-rename-ispace-vars vals
                                                       dim-renam shape-renam)
                   frames pframe)
                  (expr-value-list-list-rename-ispace-vars
                   (lift-expr-value-list-to-frame vals frames pframe)
                   dim-renam shape-renam)))
  :induct (lift-expr-value-list-to-frame vals frames pframe)
  :enable (lift-expr-value-list-to-frame
           expr-value-list-rename-ispace-vars
           expr-value-list-list-rename-ispace-vars
           not-reserrp-when-expr-value-list-listp
           expr-value-list-listp-when-result-not-error))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Commutation of the type-variable renaming of values with the remaining
; application machinery, in the same way as for expression-variable
; renamings above; the empty-dimension builder embeds a type value, whose
; renaming it commutes with.

(defrule list-split-of-expr-value-list-rename-type-vars
  (implies (integerp (/ (len vals) (pos-fix chunk)))
           (equal (list-split (expr-value-list-rename-type-vars
                               vals atom-renam array-renam)
                              chunk)
                  (expr-value-list-list-rename-type-vars
                   (list-split vals chunk) atom-renam array-renam)))
  :induct (list-split vals chunk)
  :enable (list-split
           expr-value-list-list-rename-type-vars
           fix nfix
           lt-to-zero-when-divided-by-pos)
  :hints ('(:use (:instance integerp-of-div-of-diff
                            (x (len vals))
                            (c (pos-fix chunk))))))

(defrule expr-value-rename-type-vars-of-expr-value-with-empty-dim
  (equal (expr-value-rename-type-vars (expr-value-with-empty-dim dims elem)
                                        atom-renam array-renam)
         (expr-value-with-empty-dim
          dims
          (type-value-rename-type-vars elem atom-renam array-renam)))
  :induct (expr-value-with-empty-dim dims elem)
  :enable (expr-value-with-empty-dim
           expr-value-rename-type-vars
           expr-value-list-rename-type-vars))

(defthm-expr-values-with-nonempty-dims-flag
  (defthm expr-value-rename-type-vars-of-expr-value-with-nonempty-dims
    (implies (and (nat-listp dims)
                  (expr-value-listp vals)
                  (not (member-equal 0 dims))
                  (equal (len vals) (nat-list-product dims)))
             (equal (expr-value-rename-type-vars
                     (expr-value-with-nonempty-dims dims vals)
                     atom-renam array-renam)
                    (expr-value-with-nonempty-dims
                     dims
                     (expr-value-list-rename-type-vars vals
                                                         atom-renam
                                                         array-renam))))
    :flag expr-value-with-nonempty-dims)
  (defthm expr-value-list-rename-type-vars-of-expr-value-list-with-nonempty-dims
    (implies (and (nat-listp dims)
                  (expr-value-list-listp valss)
                  (not (member-equal 0 dims))
                  (all-of-len-p valss (nat-list-product dims)))
             (equal (expr-value-list-rename-type-vars
                     (expr-value-list-with-nonempty-dims dims valss)
                     atom-renam array-renam)
                    (expr-value-list-with-nonempty-dims
                     dims
                     (expr-value-list-list-rename-type-vars valss
                                                              atom-renam
                                                              array-renam))))
    :flag expr-value-list-with-nonempty-dims)
  :hints (("Goal"
           :in-theory (enable expr-value-with-nonempty-dims
                              expr-value-list-with-nonempty-dims
                              expr-value-rename-type-vars
                              expr-value-list-rename-type-vars
                              expr-value-list-list-rename-type-vars
                              nat-list-product-of-cdr-to-ratio
                              all-of-len-p
                              pos-fix
                              lemma1
                              lemma2))))

(defrule reserrp-of-lift-expr-value-to-frame-of-rename-type-vars
  (iff (reserrp (lift-expr-value-to-frame
                 (expr-value-rename-type-vars val atom-renam array-renam)
                 frame pframe))
       (reserrp (lift-expr-value-to-frame val frame pframe)))
  :enable (lift-expr-value-to-frame
           not-reserrp-when-expr-value-listp
           expr-value-listp-when-result-not-error))

(defrule lift-expr-value-to-frame-of-expr-value-rename-type-vars
  (implies (not (reserrp (lift-expr-value-to-frame val frame pframe)))
           (equal (lift-expr-value-to-frame
                   (expr-value-rename-type-vars val atom-renam array-renam)
                   frame pframe)
                  (expr-value-list-rename-type-vars
                   (lift-expr-value-to-frame val frame pframe)
                   atom-renam array-renam)))
  :enable (lift-expr-value-to-frame
           not-reserrp-when-expr-value-listp
           expr-value-listp-when-result-not-error))

(defrule reserrp-of-lift-expr-value-list-to-frame-of-rename-type-vars
  (iff (reserrp (lift-expr-value-list-to-frame
                 (expr-value-list-rename-type-vars vals
                                                     atom-renam array-renam)
                 frames pframe))
       (reserrp (lift-expr-value-list-to-frame vals frames pframe)))
  :induct (lift-expr-value-list-to-frame vals frames pframe)
  :enable (lift-expr-value-list-to-frame
           expr-value-list-rename-type-vars
           expr-value-list-listp-of-cons
           not-reserrp-when-expr-value-list-listp
           expr-value-list-listp-when-result-not-error
           expr-value-listp-when-result-not-error))

(defrule lift-expr-value-list-to-frame-of-expr-value-list-rename-type-vars
  (implies (not (reserrp (lift-expr-value-list-to-frame vals frames pframe)))
           (equal (lift-expr-value-list-to-frame
                   (expr-value-list-rename-type-vars vals
                                                       atom-renam array-renam)
                   frames pframe)
                  (expr-value-list-list-rename-type-vars
                   (lift-expr-value-list-to-frame vals frames pframe)
                   atom-renam array-renam)))
  :induct (lift-expr-value-list-to-frame vals frames pframe)
  :enable (lift-expr-value-list-to-frame
           expr-value-list-rename-type-vars
           expr-value-list-list-rename-type-vars
           not-reserrp-when-expr-value-list-listp
           expr-value-list-listp-when-result-not-error))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Preservation of the environment relations under the extensions of the
; dynamic environment performed by the evaluator.
;
; An extension in a namespace other than the one a relation constrains
; preserves the relation unconditionally (the constrained map is untouched).
; An extension in the constrained namespace itself arises from evaluating a
; bind, whose (renamed) variable is added to the new environment while the
; original variable is added to the old one; for the relations whose keys
; are renamed, preservation additionally requires the renaming to be
; injective (see RENAME-VAR-STRING-INJECTIVE-P, defined with the value
; renamings above), so that the renamed key collides with no other renamed
; key.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The expression-variable map of the new environment associates, to the
; renaming of each expression variable, the renaming of the expression value
; associated to the variable in the old environment.  This completes the
; family of environment relations with the one for expression variables.

(acl2::defun-sk denv-expr-vars-renamed-p (new-denv denv renam)
  (forall (var)
          (implies
           (stringp var)
           (equal (omap::assoc (rename-var-string var renam)
                               (expr-denv->exprs new-denv))
                  (b* ((pair (omap::assoc var (expr-denv->exprs denv))))
                    (and pair
                         (cons (rename-var-string var renam)
                               (expr-value-rename-expr-vars (cdr pair)
                                                            renam)))))))
  :rewrite :direct)

(in-theory (disable denv-expr-vars-renamed-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Injectivity of the renaming maps lifts to injectivity of the renaming of
; ispace and type variables (renamed variables are equal exactly when the
; original variables are).  The local lemmas recover the equality of two
; variables of the same kind from the equality of their names, by
; reconstructing each variable from its fields.

(defrulel ispace-var-equal-by-dim-name
  (implies (and (ispace-varp var1)
                (ispace-varp var2)
                (equal (ispace-var-kind var1) :dim)
                (equal (ispace-var-kind var2) :dim)
                (equal (ispace-var-dim->name var1)
                       (ispace-var-dim->name var2)))
           (equal var1 var2))
  :rule-classes nil
  :enable (ispace-var-fix ispace-var-dim->name)
  :disable ispace-var-fix-when-ispace-varp
  :use ((:instance ispace-var-fix-when-ispace-varp (x var1))
        (:instance ispace-var-fix-when-ispace-varp (x var2))))

(defrulel ispace-var-equal-by-shape-name
  (implies (and (ispace-varp var1)
                (ispace-varp var2)
                (equal (ispace-var-kind var1) :shape)
                (equal (ispace-var-kind var2) :shape)
                (equal (ispace-var-shape->name var1)
                       (ispace-var-shape->name var2)))
           (equal var1 var2))
  :rule-classes nil
  :enable (ispace-var-fix ispace-var-shape->name)
  :disable ispace-var-fix-when-ispace-varp
  :use ((:instance ispace-var-fix-when-ispace-varp (x var1))
        (:instance ispace-var-fix-when-ispace-varp (x var2))))

(defrulel type-var-equal-by-atom-name
  (implies (and (type-varp var1)
                (type-varp var2)
                (equal (type-var-kind var1) :atom)
                (equal (type-var-kind var2) :atom)
                (equal (type-var-atom->name var1)
                       (type-var-atom->name var2)))
           (equal var1 var2))
  :rule-classes nil
  :enable (type-var-fix type-var-atom->name)
  :disable type-var-fix-when-type-varp
  :use ((:instance type-var-fix-when-type-varp (x var1))
        (:instance type-var-fix-when-type-varp (x var2))))

(defrulel type-var-equal-by-array-name
  (implies (and (type-varp var1)
                (type-varp var2)
                (equal (type-var-kind var1) :array)
                (equal (type-var-kind var2) :array)
                (equal (type-var-array->name var1)
                       (type-var-array->name var2)))
           (equal var1 var2))
  :rule-classes nil
  :enable (type-var-fix type-var-array->name)
  :disable type-var-fix-when-type-varp
  :use ((:instance type-var-fix-when-type-varp (x var1))
        (:instance type-var-fix-when-type-varp (x var2))))

(defruled equal-of-rename-ispace-vars
  (implies (and (rename-var-string-injective-p dim-renam)
                (rename-var-string-injective-p shape-renam)
                (ispace-varp var1)
                (ispace-varp var2))
           (equal (equal (rename-ispace-var var1 dim-renam shape-renam)
                         (rename-ispace-var var2 dim-renam shape-renam))
                  (equal var1 var2)))
  :enable rename-ispace-var
  :use (ispace-var-equal-by-dim-name
        ispace-var-equal-by-shape-name
        (:instance rename-var-string-injective-p-necc
                   (renam dim-renam)
                   (name1 (ispace-var-dim->name var1))
                   (name2 (ispace-var-dim->name var2)))
        (:instance rename-var-string-injective-p-necc
                   (renam shape-renam)
                   (name1 (ispace-var-shape->name var1))
                   (name2 (ispace-var-shape->name var2)))
        (:instance ispace-var-kind-possibilities (x var1))
        (:instance ispace-var-kind-possibilities (x var2))))

(defruled equal-of-rename-type-vars
  (implies (and (rename-var-string-injective-p atom-renam)
                (rename-var-string-injective-p array-renam)
                (type-varp var1)
                (type-varp var2))
           (equal (equal (rename-type-var var1 atom-renam array-renam)
                         (rename-type-var var2 atom-renam array-renam))
                  (equal var1 var2)))
  :enable rename-type-var
  :use (type-var-equal-by-atom-name
        type-var-equal-by-array-name
        (:instance rename-var-string-injective-p-necc
                   (renam atom-renam)
                   (name1 (type-var-atom->name var1))
                   (name2 (type-var-atom->name var2)))
        (:instance rename-var-string-injective-p-necc
                   (renam array-renam)
                   (name1 (type-var-array->name var1))
                   (name2 (type-var-array->name var2)))
        (:instance type-var-kind-possibilities (x var1))
        (:instance type-var-kind-possibilities (x var2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Preservation of the environment relations under the extensions of the
; dynamic environments performed by evaluation.  With the layered
; environments (an ISPACE-DENV inside a TYPE-DENV inside an EXPR-DENV),
; each relation constrains the map of a single layer, so an extension in
; another namespace either leaves that layer's map untouched or delegates
; to the corresponding extension of an inner layer: this is captured once
; and for all by the accessor commutation lemmas below.  An extension in
; the relation's own namespace requires, for the renaming relations, the
; renaming to be injective (see RENAME-VAR-STRING-INJECTIVE-P), a property
; that the uniquification traversal will eventually discharge from the
; freshness of the names it generates.

; Accessor commutation for the layered environment extensions.

(defrule type-denv->ienv-of-type-denv-add-ispace
  (equal (type-denv->ienv (type-denv-add-ispace var ival denv))
         (ispace-denv-add-ispace var ival (type-denv->ienv denv)))
  :enable type-denv-add-ispace)

(defrule type-denv->ienv-of-type-denv-add-ispaces
  (equal (type-denv->ienv (type-denv-add-ispaces vars ivals denv))
         (ispace-denv-add-ispaces vars ivals (type-denv->ienv denv)))
  :enable type-denv-add-ispaces)

(defrule type-denv->ienv-of-type-denv-add-type
  (equal (type-denv->ienv (type-denv-add-type var tval denv))
         (type-denv->ienv denv))
  :enable type-denv-add-type)

(defrule type-denv->ienv-of-type-denv-add-types
  (equal (type-denv->ienv (type-denv-add-types vars tvals denv))
         (type-denv->ienv denv))
  :induct t
  :enable type-denv-add-types)

(defrule type-denv->types-of-type-denv-add-ispace
  (equal (type-denv->types (type-denv-add-ispace var ival denv))
         (type-denv->types denv))
  :enable type-denv-add-ispace)

(defrule type-denv->types-of-type-denv-add-ispaces
  (equal (type-denv->types (type-denv-add-ispaces vars ivals denv))
         (type-denv->types denv))
  :enable type-denv-add-ispaces)

(defrule expr-denv->tenv-of-expr-denv-add-ispace
  (equal (expr-denv->tenv (expr-denv-add-ispace var ival denv))
         (type-denv-add-ispace var ival (expr-denv->tenv denv)))
  :enable expr-denv-add-ispace)

(defrule expr-denv->tenv-of-expr-denv-add-ispaces
  (equal (expr-denv->tenv (expr-denv-add-ispaces vars ivals denv))
         (type-denv-add-ispaces vars ivals (expr-denv->tenv denv)))
  :enable expr-denv-add-ispaces)

(defrule expr-denv->tenv-of-expr-denv-add-type
  (equal (expr-denv->tenv (expr-denv-add-type var tval denv))
         (type-denv-add-type var tval (expr-denv->tenv denv)))
  :enable expr-denv-add-type)

(defrule expr-denv->tenv-of-expr-denv-add-types
  (equal (expr-denv->tenv (expr-denv-add-types vars tvals denv))
         (type-denv-add-types vars tvals (expr-denv->tenv denv)))
  :enable expr-denv-add-types)

(defrule expr-denv->tenv-of-expr-denv-add-expr
  (equal (expr-denv->tenv (expr-denv-add-expr var val denv))
         (expr-denv->tenv denv))
  :enable expr-denv-add-expr)

(defrule expr-denv->tenv-of-expr-denv-add-exprs
  (equal (expr-denv->tenv (expr-denv-add-exprs vars vals denv))
         (expr-denv->tenv denv))
  :induct t
  :enable expr-denv-add-exprs)

(defrule expr-denv->exprs-of-expr-denv-add-ispace
  (equal (expr-denv->exprs (expr-denv-add-ispace var ival denv))
         (expr-denv->exprs denv))
  :enable expr-denv-add-ispace)

(defrule expr-denv->exprs-of-expr-denv-add-ispaces
  (equal (expr-denv->exprs (expr-denv-add-ispaces vars ivals denv))
         (expr-denv->exprs denv))
  :enable expr-denv-add-ispaces)

(defrule expr-denv->exprs-of-expr-denv-add-type
  (equal (expr-denv->exprs (expr-denv-add-type var tval denv))
         (expr-denv->exprs denv))
  :enable expr-denv-add-type)

(defrule expr-denv->exprs-of-expr-denv-add-types
  (equal (expr-denv->exprs (expr-denv-add-types vars tvals denv))
         (expr-denv->exprs denv))
  :enable expr-denv-add-types)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Preservation of DENV-ISPACE-VARS-RENAMED-P
; (a relation between ispace dynamic environments)
; under an extension in its own namespace.

(defrule denv-ispace-vars-renamed-p-of-ispace-denv-add-ispace
  (implies (and (denv-ispace-vars-renamed-p new-denv denv dim-renam shape-renam)
                (rename-var-string-injective-p dim-renam)
                (rename-var-string-injective-p shape-renam)
                (ispace-varp var))
           (denv-ispace-vars-renamed-p
            (ispace-denv-add-ispace (rename-ispace-var var dim-renam shape-renam)
                                    ival new-denv)
            (ispace-denv-add-ispace var ival denv)
            dim-renam shape-renam))
  :expand ((denv-ispace-vars-renamed-p
            (ispace-denv-add-ispace (rename-ispace-var var dim-renam shape-renam)
                                    ival new-denv)
            (ispace-denv-add-ispace var ival denv)
            dim-renam shape-renam))
  :hints ((and acl2::stable-under-simplificationp
               '(:in-theory (enable ispace-denv-add-ispace
                                    equal-of-rename-ispace-vars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Preservation of DENV-ISPACE-VARS-EQUAL-P
; (a relation between ispace dynamic environments)
; under an extension in its own namespace.

(defrule denv-ispace-vars-equal-p-of-ispace-denv-add-ispace
  (implies (denv-ispace-vars-equal-p new-denv denv)
           (denv-ispace-vars-equal-p
            (ispace-denv-add-ispace var ival new-denv)
            (ispace-denv-add-ispace var ival denv)))
  :expand ((denv-ispace-vars-equal-p
            (ispace-denv-add-ispace var ival new-denv)
            (ispace-denv-add-ispace var ival denv)))
  :hints ((and acl2::stable-under-simplificationp
               '(:in-theory (enable ispace-denv-add-ispace)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Preservation of DENV-TYPE-VARS-ISPACE-RENAMED-P
; (a relation between type dynamic environments):
; an ispace extension leaves the type-variable map untouched;
; a type extension associates, to the same type variable,
; the renaming of the type value.

(defrule denv-type-vars-ispace-renamed-p-of-type-denv-add-ispace
  (implies (denv-type-vars-ispace-renamed-p new-denv denv dim-renam shape-renam)
           (denv-type-vars-ispace-renamed-p
            (type-denv-add-ispace var1 ival1 new-denv)
            (type-denv-add-ispace var2 ival2 denv)
            dim-renam shape-renam))
  :expand ((denv-type-vars-ispace-renamed-p
            (type-denv-add-ispace var1 ival1 new-denv)
            (type-denv-add-ispace var2 ival2 denv)
            dim-renam shape-renam)))

(defrule denv-type-vars-ispace-renamed-p-of-type-denv-add-ispaces
  (implies (denv-type-vars-ispace-renamed-p new-denv denv dim-renam shape-renam)
           (denv-type-vars-ispace-renamed-p
            (type-denv-add-ispaces vars1 ivals1 new-denv)
            (type-denv-add-ispaces vars2 ivals2 denv)
            dim-renam shape-renam))
  :expand ((denv-type-vars-ispace-renamed-p
            (type-denv-add-ispaces vars1 ivals1 new-denv)
            (type-denv-add-ispaces vars2 ivals2 denv)
            dim-renam shape-renam)))

(defrule denv-type-vars-ispace-renamed-p-of-type-denv-add-type
  (implies (and (denv-type-vars-ispace-renamed-p new-denv denv
                                                 dim-renam shape-renam)
                (type-varp var)
                (type-valuep tval))
           (denv-type-vars-ispace-renamed-p
            (type-denv-add-type var
                                (type-value-rename-ispace-vars tval
                                                               dim-renam
                                                               shape-renam)
                                new-denv)
            (type-denv-add-type var tval denv)
            dim-renam shape-renam))
  :expand ((denv-type-vars-ispace-renamed-p
            (type-denv-add-type var
                                (type-value-rename-ispace-vars tval
                                                               dim-renam
                                                               shape-renam)
                                new-denv)
            (type-denv-add-type var tval denv)
            dim-renam shape-renam))
  :hints ((and acl2::stable-under-simplificationp
               '(:in-theory (enable type-denv-add-type)
                 :use ((:instance
                        denv-type-vars-ispace-renamed-p-necc
                        (var (denv-type-vars-ispace-renamed-p-witness
                              (type-denv-add-type
                               var
                               (type-value-rename-ispace-vars tval
                                                              dim-renam
                                                              shape-renam)
                               new-denv)
                              (type-denv-add-type var tval denv)
                              dim-renam shape-renam))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Preservation of DENV-TYPE-VARS-RENAMED-P
; (a relation between type dynamic environments), analogously.

(defrule denv-type-vars-renamed-p-of-type-denv-add-ispace
  (implies (denv-type-vars-renamed-p new-denv denv atom-renam array-renam)
           (denv-type-vars-renamed-p
            (type-denv-add-ispace var1 ival1 new-denv)
            (type-denv-add-ispace var2 ival2 denv)
            atom-renam array-renam))
  :expand ((denv-type-vars-renamed-p
            (type-denv-add-ispace var1 ival1 new-denv)
            (type-denv-add-ispace var2 ival2 denv)
            atom-renam array-renam)))

(defrule denv-type-vars-renamed-p-of-type-denv-add-ispaces
  (implies (denv-type-vars-renamed-p new-denv denv atom-renam array-renam)
           (denv-type-vars-renamed-p
            (type-denv-add-ispaces vars1 ivals1 new-denv)
            (type-denv-add-ispaces vars2 ivals2 denv)
            atom-renam array-renam))
  :expand ((denv-type-vars-renamed-p
            (type-denv-add-ispaces vars1 ivals1 new-denv)
            (type-denv-add-ispaces vars2 ivals2 denv)
            atom-renam array-renam)))

(defrule denv-type-vars-renamed-p-of-type-denv-add-type
  (implies (and (denv-type-vars-renamed-p new-denv denv atom-renam array-renam)
                (rename-var-string-injective-p atom-renam)
                (rename-var-string-injective-p array-renam)
                (type-varp var)
                (type-valuep tval))
           (denv-type-vars-renamed-p
            (type-denv-add-type (rename-type-var var atom-renam array-renam)
                                (type-value-rename-type-vars tval
                                                             atom-renam
                                                             array-renam)
                                new-denv)
            (type-denv-add-type var tval denv)
            atom-renam array-renam))
  :expand ((denv-type-vars-renamed-p
            (type-denv-add-type (rename-type-var var atom-renam array-renam)
                                (type-value-rename-type-vars tval
                                                             atom-renam
                                                             array-renam)
                                new-denv)
            (type-denv-add-type var tval denv)
            atom-renam array-renam))
  :hints ((and acl2::stable-under-simplificationp
               '(:in-theory (enable type-denv-add-type
                                    equal-of-rename-type-vars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Preservation of DENV-EXPR-VARS-RENAMED-P
; (a relation between expression dynamic environments):
; ispace and type extensions leave the expression-variable map untouched;
; an expression extension associates, to the renaming of the variable,
; the renaming of the expression value.

(defrule denv-expr-vars-renamed-p-of-expr-denv-add-ispace
  (implies (denv-expr-vars-renamed-p new-denv denv renam)
           (denv-expr-vars-renamed-p
            (expr-denv-add-ispace var1 ival1 new-denv)
            (expr-denv-add-ispace var2 ival2 denv)
            renam))
  :expand ((denv-expr-vars-renamed-p
            (expr-denv-add-ispace var1 ival1 new-denv)
            (expr-denv-add-ispace var2 ival2 denv)
            renam)))

(defrule denv-expr-vars-renamed-p-of-expr-denv-add-ispaces
  (implies (denv-expr-vars-renamed-p new-denv denv renam)
           (denv-expr-vars-renamed-p
            (expr-denv-add-ispaces vars1 ivals1 new-denv)
            (expr-denv-add-ispaces vars2 ivals2 denv)
            renam))
  :expand ((denv-expr-vars-renamed-p
            (expr-denv-add-ispaces vars1 ivals1 new-denv)
            (expr-denv-add-ispaces vars2 ivals2 denv)
            renam)))

(defrule denv-expr-vars-renamed-p-of-expr-denv-add-type
  (implies (denv-expr-vars-renamed-p new-denv denv renam)
           (denv-expr-vars-renamed-p
            (expr-denv-add-type var1 tval1 new-denv)
            (expr-denv-add-type var2 tval2 denv)
            renam))
  :expand ((denv-expr-vars-renamed-p
            (expr-denv-add-type var1 tval1 new-denv)
            (expr-denv-add-type var2 tval2 denv)
            renam)))

(defrule denv-expr-vars-renamed-p-of-expr-denv-add-types
  (implies (denv-expr-vars-renamed-p new-denv denv renam)
           (denv-expr-vars-renamed-p
            (expr-denv-add-types vars1 tvals1 new-denv)
            (expr-denv-add-types vars2 tvals2 denv)
            renam))
  :expand ((denv-expr-vars-renamed-p
            (expr-denv-add-types vars1 tvals1 new-denv)
            (expr-denv-add-types vars2 tvals2 denv)
            renam)))

(defrule denv-expr-vars-renamed-p-of-expr-denv-add-expr
  (implies (and (denv-expr-vars-renamed-p new-denv denv renam)
                (rename-var-string-injective-p renam)
                (stringp var))
           (denv-expr-vars-renamed-p
            (expr-denv-add-expr (rename-var-string var renam)
                                (expr-value-rename-expr-vars val renam)
                                new-denv)
            (expr-denv-add-expr var val denv)
            renam))
  :expand ((denv-expr-vars-renamed-p
            (expr-denv-add-expr (rename-var-string var renam)
                                (expr-value-rename-expr-vars val renam)
                                new-denv)
            (expr-denv-add-expr var val denv)
            renam))
  :hints ((and acl2::stable-under-simplificationp
               '(:in-theory (enable expr-denv-add-expr)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Environment relations under binder-reduced renamings.
;
; When evaluation enters the scope of a binder, the renamings in force are
; REDUCED by the bound variables: the body of an applied lambda value was
; renamed under the maps with the parameters removed (see the lambda cases
; of the value renamings above), and likewise for the bodies of the binding
; constructs in a renamed AST.  The two evaluations extend their
; environments with the SAME variables (binders are untouched by the
; map-based renamings), bound to related values, and the evaluation of the
; two bodies requires the environment relations UNDER THE REDUCED MAPS.
; This section provides two kinds of lemmas towards those relations.
;
; (1) Establishment: the renaming of an environment is related, by the
;     corresponding relation, to the environment itself.  This seeds the
;     relations at an application site, where the renamed closure carries
;     exactly the renaming of the original closure's captured environment.
;     Where the relation renames its keys, this requires the renaming to
;     be injective.
;
; (2) Transition: a relation under the full maps carries over to the
;     relation under the maps reduced by a set of bound variables when
;     those variables are added to both environments, provided the reduced
;     renaming captures none of the bound names (so that the surviving
;     entries' renamed keys stay clear of the added ones).  For the ispace
;     relation, whose values are ground, this is proved below.  For the
;     relations whose entries carry RENAMED VALUES (type and expression
;     values), the same transition additionally requires the renaming of
;     the surviving entries' values to be unchanged by the reduction; that
;     stability property will be discharged, in the eventual main
;     induction, from the freshness of the uniquified names (bound names
;     do not occur in the values of the enclosing environments), and those
;     transitions are deferred to that development.
;
; Once a relation is established at the reduced maps, the extension lemmas
; above apply at those maps; in particular, for a variable bound at the
; binder (hence removed from the maps) the renaming is the identity, so
; the same-namespace extension lemmas add it to both environments under
; the same name.

; Injectivity of a renaming map lifts to the renaming of variable names.

(defruled equal-of-rename-var-string
  (implies (and (rename-var-string-injective-p renam)
                (stringp name1)
                (stringp name2))
           (equal (equal (rename-var-string name1 renam)
                         (rename-var-string name2 renam))
                  (equal name1 name2)))
  :use ((:instance rename-var-string-injective-p-necc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Establishment of DENV-ISPACE-VARS-RENAMED-P:
; looking up a renamed ispace variable in the renaming of a map yields
; the renaming of the variable's association in the map.

(defruled assoc-of-ispace-var-ispace-value-map-rename-ispace-vars
  (implies (and (rename-var-string-injective-p dim-renam)
                (rename-var-string-injective-p shape-renam)
                (ispace-var-ispace-value-mapp map)
                (ispace-varp var))
           (equal (omap::assoc
                   (rename-ispace-var var dim-renam shape-renam)
                   (ispace-var-ispace-value-map-rename-ispace-vars
                    map dim-renam shape-renam))
                  (b* ((pair (omap::assoc var map)))
                    (and pair
                         (cons (rename-ispace-var var dim-renam shape-renam)
                               (cdr pair))))))
  :induct (omap::size map)
  :expand ((ispace-var-ispace-value-map-rename-ispace-vars map
                                                           dim-renam
                                                           shape-renam))
  :enable (omap::size
           ispace-var-ispace-value-map-rename-ispace-vars
           omap::assoc
           equal-of-rename-ispace-vars))

(defruled not-assoc-of-ispace-var-ispace-value-map-rename-ispace-vars
  (implies (and (rename-var-string-injective-p dim-renam)
                (rename-var-string-injective-p shape-renam)
                (ispace-var-ispace-value-mapp map)
                (ispace-varp var)
                (not (omap::assoc var map)))
           (not (omap::assoc
                 (rename-ispace-var var dim-renam shape-renam)
                 (ispace-var-ispace-value-map-rename-ispace-vars
                  map dim-renam shape-renam))))
  :induct (omap::size map)
  :expand ((ispace-var-ispace-value-map-rename-ispace-vars map
                                                           dim-renam
                                                           shape-renam))
  :enable (omap::size
           ispace-var-ispace-value-map-rename-ispace-vars
           omap::assoc
           equal-of-rename-ispace-vars))

(defrule denv-ispace-vars-renamed-p-of-ispace-denv-rename-ispace-vars
  (implies (and (rename-var-string-injective-p dim-renam)
                (rename-var-string-injective-p shape-renam))
           (denv-ispace-vars-renamed-p
            (ispace-denv-rename-ispace-vars idenv dim-renam shape-renam)
            idenv dim-renam shape-renam))
  :expand ((denv-ispace-vars-renamed-p
            (ispace-denv-rename-ispace-vars idenv dim-renam shape-renam)
            idenv dim-renam shape-renam))
  :hints ((and acl2::stable-under-simplificationp
               '(:in-theory
                 (enable
                  ispace-denv-rename-ispace-vars
                  assoc-of-ispace-var-ispace-value-map-rename-ispace-vars
                  not-assoc-of-ispace-var-ispace-value-map-rename-ispace-vars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Establishment of DENV-TYPE-VARS-ISPACE-RENAMED-P (keys untouched by an
; ispace renaming, values renamed), and the ispace layer of the same
; renamed environment.

(defruled assoc-of-type-var-type-value-map-rename-ispace-vars
  (implies (and (type-var-type-value-mapp map)
                (type-varp var))
           (equal (omap::assoc
                   var
                   (type-var-type-value-map-rename-ispace-vars
                    map dim-renam shape-renam))
                  (b* ((pair (omap::assoc var map)))
                    (and pair
                         (cons var
                               (type-value-rename-ispace-vars
                                (cdr pair) dim-renam shape-renam))))))
  :induct (omap::size map)
  :expand ((type-var-type-value-map-rename-ispace-vars map
                                                       dim-renam
                                                       shape-renam))
  :enable (omap::size
           type-var-type-value-map-rename-ispace-vars
           omap::assoc))

(defruled not-assoc-of-type-var-type-value-map-rename-ispace-vars
  (implies (and (type-var-type-value-mapp map)
                (not (omap::assoc var map)))
           (not (omap::assoc
                 var
                 (type-var-type-value-map-rename-ispace-vars map
                                                             dim-renam
                                                             shape-renam))))
  :induct (omap::size map)
  :expand ((type-var-type-value-map-rename-ispace-vars map
                                                       dim-renam
                                                       shape-renam))
  :enable (omap::size
           type-var-type-value-map-rename-ispace-vars
           omap::assoc))

(defrule denv-type-vars-ispace-renamed-p-of-type-denv-rename-ispace-vars
  (denv-type-vars-ispace-renamed-p
   (type-denv-rename-ispace-vars denv dim-renam shape-renam)
   denv dim-renam shape-renam)
  :expand ((denv-type-vars-ispace-renamed-p
            (type-denv-rename-ispace-vars denv dim-renam shape-renam)
            denv dim-renam shape-renam))
  :hints ((and acl2::stable-under-simplificationp
               '(:in-theory
                 (enable
                  type-denv-rename-ispace-vars
                  assoc-of-type-var-type-value-map-rename-ispace-vars
                  not-assoc-of-type-var-type-value-map-rename-ispace-vars)))))

(defrule denv-ispace-vars-renamed-p-of-ienv-of-type-denv-rename-ispace-vars
  (implies (and (rename-var-string-injective-p dim-renam)
                (rename-var-string-injective-p shape-renam))
           (denv-ispace-vars-renamed-p
            (type-denv->ienv (type-denv-rename-ispace-vars denv
                                                           dim-renam
                                                           shape-renam))
            (type-denv->ienv denv)
            dim-renam shape-renam))
  :expand ((type-denv-rename-ispace-vars denv dim-renam shape-renam)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Establishment of DENV-TYPE-VARS-RENAMED-P (keys renamed), and the
; untouched ispace layer of the same renamed environment.

(defruled assoc-of-type-var-type-value-map-rename-type-vars
  (implies (and (rename-var-string-injective-p atom-renam)
                (rename-var-string-injective-p array-renam)
                (type-var-type-value-mapp map)
                (type-varp var))
           (equal (omap::assoc
                   (rename-type-var var atom-renam array-renam)
                   (type-var-type-value-map-rename-type-vars
                    map atom-renam array-renam))
                  (b* ((pair (omap::assoc var map)))
                    (and pair
                         (cons (rename-type-var var atom-renam array-renam)
                               (type-value-rename-type-vars
                                (cdr pair) atom-renam array-renam))))))
  :induct (omap::size map)
  :expand ((type-var-type-value-map-rename-type-vars map
                                                     atom-renam
                                                     array-renam))
  :enable (omap::size
           type-var-type-value-map-rename-type-vars
           omap::assoc
           equal-of-rename-type-vars))

(defruled not-assoc-of-type-var-type-value-map-rename-type-vars
  (implies (and (rename-var-string-injective-p atom-renam)
                (rename-var-string-injective-p array-renam)
                (type-var-type-value-mapp map)
                (type-varp var)
                (not (omap::assoc var map)))
           (not (omap::assoc
                 (rename-type-var var atom-renam array-renam)
                 (type-var-type-value-map-rename-type-vars map
                                                           atom-renam
                                                           array-renam))))
  :induct (omap::size map)
  :expand ((type-var-type-value-map-rename-type-vars map
                                                     atom-renam
                                                     array-renam))
  :enable (omap::size
           type-var-type-value-map-rename-type-vars
           omap::assoc
           equal-of-rename-type-vars))

(defrule denv-type-vars-renamed-p-of-type-denv-rename-type-vars
  (implies (and (rename-var-string-injective-p atom-renam)
                (rename-var-string-injective-p array-renam))
           (denv-type-vars-renamed-p
            (type-denv-rename-type-vars denv atom-renam array-renam)
            denv atom-renam array-renam))
  :expand ((denv-type-vars-renamed-p
            (type-denv-rename-type-vars denv atom-renam array-renam)
            denv atom-renam array-renam))
  :hints ((and acl2::stable-under-simplificationp
               '(:in-theory
                 (enable
                  type-denv-rename-type-vars
                  assoc-of-type-var-type-value-map-rename-type-vars
                  not-assoc-of-type-var-type-value-map-rename-type-vars)))))

(defrule denv-ispace-vars-equal-p-reflexive
  (denv-ispace-vars-equal-p idenv idenv)
  :expand ((denv-ispace-vars-equal-p idenv idenv)))

(defrule denv-ispace-vars-equal-p-of-ienv-of-type-denv-rename-type-vars
  (denv-ispace-vars-equal-p
   (type-denv->ienv (type-denv-rename-type-vars denv atom-renam array-renam))
   (type-denv->ienv denv))
  :expand ((type-denv-rename-type-vars denv atom-renam array-renam)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Establishment of DENV-EXPR-VARS-RENAMED-P (keys renamed), and the layer
; accessors of the renamed expression environments, which reduce the
; establishment of the inner-layer relations for a renamed expression
; environment to the lemmas above.

(defruled assoc-of-string-expr-value-map-rename-expr-vars
  (implies (and (rename-var-string-injective-p renam)
                (string-expr-value-mapp map)
                (stringp var))
           (equal (omap::assoc
                   (rename-var-string var renam)
                   (string-expr-value-map-rename-expr-vars map renam))
                  (b* ((pair (omap::assoc var map)))
                    (and pair
                         (cons (rename-var-string var renam)
                               (expr-value-rename-expr-vars (cdr pair)
                                                            renam))))))
  :induct (omap::size map)
  :expand ((string-expr-value-map-rename-expr-vars map renam))
  :enable (omap::size
           string-expr-value-map-rename-expr-vars
           omap::assoc
           equal-of-rename-var-string))

(defruled not-assoc-of-string-expr-value-map-rename-expr-vars
  (implies (and (rename-var-string-injective-p renam)
                (string-expr-value-mapp map)
                (stringp var)
                (not (omap::assoc var map)))
           (not (omap::assoc
                 (rename-var-string var renam)
                 (string-expr-value-map-rename-expr-vars map renam))))
  :induct (omap::size map)
  :expand ((string-expr-value-map-rename-expr-vars map renam))
  :enable (omap::size
           string-expr-value-map-rename-expr-vars
           omap::assoc
           equal-of-rename-var-string))

(defrule denv-expr-vars-renamed-p-of-expr-denv-rename-expr-vars
  (implies (rename-var-string-injective-p renam)
           (denv-expr-vars-renamed-p
            (expr-denv-rename-expr-vars denv renam)
            denv renam))
  :expand ((denv-expr-vars-renamed-p
            (expr-denv-rename-expr-vars denv renam)
            denv renam))
  :hints ((and acl2::stable-under-simplificationp
               '(:in-theory
                 (enable
                  expr-denv-rename-expr-vars
                  assoc-of-string-expr-value-map-rename-expr-vars
                  not-assoc-of-string-expr-value-map-rename-expr-vars)))))

(defrule expr-denv->tenv-of-expr-denv-rename-expr-vars
  (equal (expr-denv->tenv (expr-denv-rename-expr-vars denv renam))
         (expr-denv->tenv denv))
  :expand ((expr-denv-rename-expr-vars denv renam)))

(defrule expr-denv->tenv-of-expr-denv-rename-ispace-vars
  (equal (expr-denv->tenv (expr-denv-rename-ispace-vars denv
                                                        dim-renam
                                                        shape-renam))
         (type-denv-rename-ispace-vars (expr-denv->tenv denv)
                                       dim-renam
                                       shape-renam))
  :expand ((expr-denv-rename-ispace-vars denv dim-renam shape-renam)))

(defrule expr-denv->tenv-of-expr-denv-rename-type-vars
  (equal (expr-denv->tenv (expr-denv-rename-type-vars denv
                                                      atom-renam
                                                      array-renam))
         (type-denv-rename-type-vars (expr-denv->tenv denv)
                                     atom-renam
                                     array-renam))
  :expand ((expr-denv-rename-type-vars denv atom-renam array-renam)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Transition of DENV-ISPACE-VARS-RENAMED-P to the binder-reduced maps:
; if two ispace environments are related under the full maps, then after
; adding the SAME bound variables (with the same, ground, ispace values)
; to both, they are related under the maps with those variables removed,
; provided the reduced renaming captures none of the bound names.
;
; The lookup of a variable in the extended environments is characterized
; through the additions: a variable among the added ones looks up the
; same in both extensions (and is found); any other key looks up as in
; the base environment.  The witness of the relation then splits: a bound
; variable is renamed to itself by the reduced maps and is found, with
; the same value, in both extensions; any other variable is renamed as by
; the full maps, its renaming avoids the added variables (no capture),
; and the relation under the full maps applies.

(local
 (defun add-ispaces2-induct (vars ivals denv1 denv2)
   (if (endp vars)
       (list denv1 denv2)
     (add-ispaces2-induct (cdr vars)
                          (cdr ivals)
                          (ispace-denv-add-ispace (car vars)
                                                  (car ivals)
                                                  denv1)
                          (ispace-denv-add-ispace (car vars)
                                                  (car ivals)
                                                  denv2)))))

(defruled assoc-of-ispaces-of-ispace-denv-add-ispaces-when-not-member
  (implies (and (ispace-var-listp vars)
                (not (member-equal var vars)))
           (equal (omap::assoc
                   var
                   (ispace-denv->ispaces (ispace-denv-add-ispaces vars
                                                                  ivals
                                                                  denv)))
                  (omap::assoc var (ispace-denv->ispaces denv))))
  :induct (ispace-denv-add-ispaces vars ivals denv)
  :enable (ispace-denv-add-ispaces
           ispace-denv-add-ispace))

(defruled assoc-of-ispaces-of-ispace-denv-add-ispaces-when-member
  (implies (and (ispace-varp var)
                (ispace-var-listp vars)
                (equal (len vars) (len ivals))
                (member-equal var vars))
           (equal (omap::assoc
                   var
                   (ispace-denv->ispaces (ispace-denv-add-ispaces vars
                                                                  ivals
                                                                  denv1)))
                  (b* ((pair (omap::assoc
                              var
                              (ispace-denv->ispaces
                               (ispace-denv-add-ispaces vars ivals denv2)))))
                    (and pair
                         (cons var (cdr pair))))))
  :induct (add-ispaces2-induct vars ivals denv1 denv2)
  :expand ((ispace-denv-add-ispaces vars ivals denv1)
           (ispace-denv-add-ispaces vars ivals denv2))
  :enable (ispace-denv-add-ispaces
           ispace-denv-add-ispace
           assoc-of-ispaces-of-ispace-denv-add-ispaces-when-not-member))

(defruled assoc-of-ispaces-of-ispace-denv-add-ispaces-consp-when-member
  (implies (and (ispace-varp var)
                (ispace-var-listp vars)
                (equal (len vars) (len ivals))
                (member-equal var vars))
           (omap::assoc
            var
            (ispace-denv->ispaces (ispace-denv-add-ispaces vars
                                                           ivals
                                                           denv))))
  :induct (ispace-denv-add-ispaces vars ivals denv)
  :enable (ispace-denv-add-ispaces
           ispace-denv-add-ispace
           assoc-of-ispaces-of-ispace-denv-add-ispaces-when-not-member))

; The renaming of a variable under the reduced maps: the identity on the
; bound variables, the full renaming off them.

(defruledl rename-ispace-var-of-remove-bound-when-in
  (b* (((mv & & dim-renam1 shape-renam1)
        (dim/shape-rename-remove-bound bound dim-renam shape-renam)))
    (implies (and (ispace-var-setp bound)
                  (ispace-varp var)
                  (set::in var bound))
             (equal (rename-ispace-var var dim-renam1 shape-renam1)
                    var)))
  :enable (dim/shape-rename-remove-bound
           rename-ispace-var
           rename-var-string
           equal-of-ispace-var-dim
           equal-of-ispace-var-shape))

(defruledl rename-ispace-var-of-remove-bound-when-not-in
  (b* (((mv & & dim-renam1 shape-renam1)
        (dim/shape-rename-remove-bound bound dim-renam shape-renam)))
    (implies (and (ispace-var-setp bound)
                  (ispace-varp var)
                  (not (set::in var bound)))
             (equal (rename-ispace-var var dim-renam1 shape-renam1)
                    (rename-ispace-var var dim-renam shape-renam))))
  :enable (dim/shape-rename-remove-bound
           rename-ispace-var
           rename-var-string
           equal-of-ispace-var-dim
           equal-of-ispace-var-shape))

(defruledl not-in-bound-of-rename-ispace-var-of-remove-bound
  (b* (((mv bound-dim-vars bound-shape-vars dim-renam1 shape-renam1)
        (dim/shape-rename-remove-bound bound dim-renam shape-renam)))
    (implies (and (ispace-var-setp bound)
                  (ispace-varp var)
                  (not (set::in var bound))
                  (renaming-no-capture-p bound-dim-vars dim-renam1)
                  (renaming-no-capture-p bound-shape-vars shape-renam1))
             (not (set::in (rename-ispace-var var dim-renam shape-renam)
                           bound))))
  :enable (dim/shape-rename-remove-bound
           renaming-no-capture-p
           rename-ispace-var
           rename-var-string
           not-in-bound-of-renamed-dim-name
           not-in-bound-of-renamed-shape-name))

(defruledl not-member-of-rename-ispace-var-of-remove-bound
  (b* (((mv bound-dim-vars bound-shape-vars dim-renam1 shape-renam1)
        (dim/shape-rename-remove-bound (set::mergesort vars)
                                       dim-renam
                                       shape-renam)))
    (implies (and (ispace-var-listp vars)
                  (ispace-varp var)
                  (not (member-equal var vars))
                  (renaming-no-capture-p bound-dim-vars dim-renam1)
                  (renaming-no-capture-p bound-shape-vars shape-renam1))
             (not (member-equal
                   (rename-ispace-var var dim-renam shape-renam)
                   vars))))
  :use ((:instance not-in-bound-of-rename-ispace-var-of-remove-bound
                   (bound (set::mergesort vars))))
  :disable not-in-bound-of-rename-ispace-var-of-remove-bound)

(defrule denv-ispace-vars-renamed-p-of-add-ispaces-remove-bound
  (b* (((mv bound-dim-vars bound-shape-vars dim-renam1 shape-renam1)
        (dim/shape-rename-remove-bound (set::mergesort vars)
                                       dim-renam
                                       shape-renam)))
    (implies (and (denv-ispace-vars-renamed-p new-idenv idenv
                                              dim-renam shape-renam)
                  (renaming-no-capture-p bound-dim-vars dim-renam1)
                  (renaming-no-capture-p bound-shape-vars shape-renam1)
                  (ispace-var-listp vars)
                  (equal (len vars) (len ivals)))
             (denv-ispace-vars-renamed-p
              (ispace-denv-add-ispaces vars ivals new-idenv)
              (ispace-denv-add-ispaces vars ivals idenv)
              dim-renam1 shape-renam1)))
  :do-not-induct t
  :expand ((:free (dim-renam1 shape-renam1)
            (denv-ispace-vars-renamed-p
             (ispace-denv-add-ispaces vars ivals new-idenv)
             (ispace-denv-add-ispaces vars ivals idenv)
             dim-renam1 shape-renam1)))
  :enable (rename-ispace-var-of-remove-bound-when-in
           rename-ispace-var-of-remove-bound-when-not-in
           assoc-of-ispaces-of-ispace-denv-add-ispaces-consp-when-member
           assoc-of-ispaces-of-ispace-denv-add-ispaces-when-not-member
           not-in-bound-of-rename-ispace-var-of-remove-bound
           not-member-of-rename-ispace-var-of-remove-bound
           car-of-assoc)
  :hints ((and acl2::stable-under-simplificationp
               '(:cases ((set::in (denv-ispace-vars-renamed-p-witness
                              (ispace-denv-add-ispaces vars ivals new-idenv)
                              (ispace-denv-add-ispaces vars ivals idenv)
                              (mv-nth 2 (dim/shape-rename-remove-bound
                                         (set::mergesort vars)
                                         dim-renam shape-renam))
                              (mv-nth 3 (dim/shape-rename-remove-bound
                                         (set::mergesort vars)
                                         dim-renam shape-renam)))
                          (set::mergesort vars)))
                 :use ((:instance
                        denv-ispace-vars-renamed-p-necc
                        (var (denv-ispace-vars-renamed-p-witness
                              (ispace-denv-add-ispaces vars ivals new-idenv)
                              (ispace-denv-add-ispaces vars ivals idenv)
                              (mv-nth 2 (dim/shape-rename-remove-bound
                                         (set::mergesort vars)
                                         dim-renam shape-renam))
                              (mv-nth 3 (dim/shape-rename-remove-bound
                                         (set::mergesort vars)
                                         dim-renam shape-renam))))
                        (new-denv new-idenv)
                        (denv idenv))
                       (:instance
                        assoc-of-ispaces-of-ispace-denv-add-ispaces-when-member
                        (var (denv-ispace-vars-renamed-p-witness
                              (ispace-denv-add-ispaces vars ivals new-idenv)
                              (ispace-denv-add-ispaces vars ivals idenv)
                              (mv-nth 2 (dim/shape-rename-remove-bound
                                         (set::mergesort vars)
                                         dim-renam shape-renam))
                              (mv-nth 3 (dim/shape-rename-remove-bound
                                         (set::mergesort vars)
                                         dim-renam shape-renam))))
                        (denv1 new-idenv)
                        (denv2 idenv))))))
  :otf-flg t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Stability of the renamings under binder reduction.
;
; The transitions of the value-carrying relations to binder-reduced maps
; (see the section above) require the renaming of the enclosing
; environments' values to be UNCHANGED by the reduction.  This section
; proves the underpinning: a renaming depends only on its associations at
; the free variables of the thing renamed, so removing from the map a set
; of (bound) names that is disjoint from those free variables does not
; change the result.  The free expression variables of an expression are
; given by EXPR-FREE-EXPR-VARS; for expression VALUES, which embed
; expressions and captured environments, the corresponding notion is
; defined below (EXPR-VALUE-FREE-EXPR-VARS and companions): the free
; variables of the lambda bodies outside their parameters, together with
; the keys and (recursively) the free variables of the captured
; environments.  The freshness of the uniquified names will discharge the
; disjointness: a binder's names, being fresh, do not occur free in the
; values of the enclosing environments.

; Removing names that are either not the variable's name or not keys of
; the map does not change the variable's renaming.

(defruled rename-var-string-of-delete*-when-not-relevant
  (implies (and (string-setp bound)
                (stringp name)
                (not (set::in name
                              (set::intersect
                               bound
                               (omap::keys
                                (string-string-map-fix renam))))))
           (equal (rename-var-string
                   name
                   (omap::delete* bound (string-string-map-fix renam)))
                  (rename-var-string name renam)))
  :enable (rename-var-string
           set::intersect-in
           omap::in-of-keys-to-assoc))

; Removing a set of names whose relevant part (names that are keys of the
; renaming) is disjoint from the free expression variables of an AST does
; not change the renaming of the AST.  The triple-intersection form makes
; the statement self-strengthening at binders: the parameters leave both
; the free variables and the keys of the reduced map.

(defthm-exprs/atoms/binds-rename-expr-vars-flag
  (defthm expr-rename-expr-vars-of-delete*-when-disjoint
    (implies (and (string-setp bound)
                  (set::emptyp
                   (set::intersect
                    (expr-free-expr-vars expr)
                    (set::intersect
                     bound
                     (omap::keys (string-string-map-fix renam))))))
             (equal (expr-rename-expr-vars
                     expr
                     (omap::delete* bound (string-string-map-fix renam)))
                    (expr-rename-expr-vars expr renam)))
    :flag expr-rename-expr-vars)
  (defthm expr-list-rename-expr-vars-of-delete*-when-disjoint
    (implies (and (string-setp bound)
                  (set::emptyp
                   (set::intersect
                    (expr-list-free-expr-vars expr-list)
                    (set::intersect
                     bound
                     (omap::keys (string-string-map-fix renam))))))
             (equal (expr-list-rename-expr-vars
                     expr-list
                     (omap::delete* bound (string-string-map-fix renam)))
                    (expr-list-rename-expr-vars expr-list renam)))
    :flag expr-list-rename-expr-vars)
  (defthm atom-rename-expr-vars-of-delete*-when-disjoint
    (implies (and (string-setp bound)
                  (set::emptyp
                   (set::intersect
                    (atom-free-expr-vars atom)
                    (set::intersect
                     bound
                     (omap::keys (string-string-map-fix renam))))))
             (equal (atom-rename-expr-vars
                     atom
                     (omap::delete* bound (string-string-map-fix renam)))
                    (atom-rename-expr-vars atom renam)))
    :flag atom-rename-expr-vars)
  (defthm atom-list-rename-expr-vars-of-delete*-when-disjoint
    (implies (and (string-setp bound)
                  (set::emptyp
                   (set::intersect
                    (atom-list-free-expr-vars atom-list)
                    (set::intersect
                     bound
                     (omap::keys (string-string-map-fix renam))))))
             (equal (atom-list-rename-expr-vars
                     atom-list
                     (omap::delete* bound (string-string-map-fix renam)))
                    (atom-list-rename-expr-vars atom-list renam)))
    :flag atom-list-rename-expr-vars)
  (defthm bind-rename-expr-vars-of-delete*-when-disjoint
    (implies (and (string-setp bound)
                  (set::emptyp
                   (set::intersect
                    (bind-free-expr-vars bind)
                    (set::intersect
                     bound
                     (omap::keys (string-string-map-fix renam))))))
             (equal (bind-rename-expr-vars
                     bind
                     (omap::delete* bound (string-string-map-fix renam)))
                    (bind-rename-expr-vars bind renam)))
    :flag bind-rename-expr-vars)
  (defthm bind-list-rename-expr-vars-of-delete*-when-disjoint
    (implies (and (string-setp bound)
                  (set::emptyp
                   (set::intersect
                    (bind-list-free-expr-vars bind-list)
                    (set::intersect
                     bound
                     (omap::keys (string-string-map-fix renam))))))
             (equal (bind-list-rename-expr-vars
                     bind-list
                     (omap::delete* bound (string-string-map-fix renam)))
                    (bind-list-rename-expr-vars bind-list renam)))
    :flag bind-list-rename-expr-vars)
  :hints
  (("Goal"
    :expand ((:free (renam) (expr-rename-expr-vars expr renam))
             (:free (renam) (expr-list-rename-expr-vars expr-list renam))
             (:free (renam) (atom-rename-expr-vars atom renam))
             (:free (renam) (atom-list-rename-expr-vars atom-list renam))
             (:free (renam) (bind-rename-expr-vars bind renam))
             (:free (renam) (bind-list-rename-expr-vars bind-list renam)))
    :in-theory
    (enable expr-rename-expr-vars
            expr-list-rename-expr-vars
            atom-rename-expr-vars
            atom-list-rename-expr-vars
            bind-rename-expr-vars
            bind-list-rename-expr-vars
            expr-free-expr-vars
            expr-list-free-expr-vars
            atom-free-expr-vars
            atom-list-free-expr-vars
            bind-free-expr-vars
            bind-list-free-expr-vars
            rename-var-string-of-delete*-when-not-relevant
            delete*-commute-restricted
            delete-commute-restricted
            emptyp-intersect3-binder-union
            emptyp-intersect3-binder-plain
            emptyp-intersect3-binder-delete
            emptyp-intersect-of-union-left-1
            emptyp-intersect-of-union-left-2
            not-in-when-emptyp-intersect-of-insert
            emptyp-intersect-singleton
            set::intersect-in
            omap::in-of-keys-to-assoc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled expr-rename-expr-vars-of-delete*-when-disjoint-typed
  (implies (and (string-string-mapp renam)
                (string-setp bound)
                (set::emptyp
                 (set::intersect (expr-free-expr-vars expr)
                                 (set::intersect bound
                                                 (omap::keys renam)))))
           (equal (expr-rename-expr-vars expr (omap::delete* bound renam))
                  (expr-rename-expr-vars expr renam)))
  :use ((:instance expr-rename-expr-vars-of-delete*-when-disjoint)))

; Free expression variables of expression values: the free variables of
; the lambda bodies outside their parameters, together with the keys and
; (recursively) the free expression variables of the captured
; environments.  This is the support of the expression-variable renaming
; of a value: names outside it are irrelevant to the renaming (see below).

(defines expr-value-free-expr-vars
  ;; The flag function may be used by theorems in other books.
  :flag-local nil

  (define expr-value-free-expr-vars ((val expr-valuep))
    :returns (names string-setp)
    :parents (renaming-evaluation)
    :short "Free expression variables of an expression value."
    :measure (expr-value-count val)
    (expr-value-case
     val
     :base nil
     :primop nil
     :lambda (set::union
              (expr-denv-free-expr-vars val.denv)
              (set::difference
               (expr-free-expr-vars val.body)
               (set::insert (var+typevalue->var val.param) nil)))
     :tlambda (set::union (expr-denv-free-expr-vars val.denv)
                          (expr-free-expr-vars val.body))
     :ilambda (set::union (expr-denv-free-expr-vars val.denv)
                          (expr-free-expr-vars val.body))
     :box (expr-value-free-expr-vars val.array)
     :vector (expr-value-list-free-expr-vars val.elems)
     :vector-empty nil))

  (define expr-value-list-free-expr-vars ((vals expr-value-listp))
    :returns (names string-setp)
    :parents (renaming-evaluation expr-value-free-expr-vars)
    :short "Free expression variables of a list of expression values."
    :measure (expr-value-list-count vals)
    (if (endp vals)
        nil
      (set::union (expr-value-free-expr-vars (car vals))
                  (expr-value-list-free-expr-vars (cdr vals)))))

  (define string-expr-value-map-free-expr-vars ((map string-expr-value-mapp))
    :returns (names string-setp)
    :parents (renaming-evaluation expr-value-free-expr-vars)
    :short "Free expression variables of
            a map from expression variables to expression values:
            the keys and the free variables of the values."
    :measure (string-expr-value-map-count map)
    (b* ((map (string-expr-value-map-fix map))
         ((when (omap::emptyp map)) nil)
         ((mv var val) (omap::head map)))
      (set::insert var
                   (set::union
                    (expr-value-free-expr-vars val)
                    (string-expr-value-map-free-expr-vars
                     (omap::tail map))))))

  (define expr-denv-free-expr-vars ((denv expr-denvp))
    :returns (names string-setp)
    :parents (renaming-evaluation expr-value-free-expr-vars)
    :short "Free expression variables of
            an expression dynamic environment."
    :measure (expr-denv-count denv)
    (string-expr-value-map-free-expr-vars (expr-denv->exprs denv)))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual expr-value-free-expr-vars))

; Removing a set of names whose relevant part is disjoint from the free
; expression variables of a value does not change the renaming of the
; value.

(defthm-expr-value-rename-expr-vars-flag
  (defthm expr-value-rename-expr-vars-of-delete*-when-disjoint
    (implies (and (string-setp bound)
                  (set::emptyp
                   (set::intersect
                    (expr-value-free-expr-vars val)
                    (set::intersect
                     bound
                     (omap::keys (string-string-map-fix renam))))))
             (equal (expr-value-rename-expr-vars
                     val
                     (omap::delete* bound (string-string-map-fix renam)))
                    (expr-value-rename-expr-vars val renam)))
    :flag expr-value-rename-expr-vars)
  (defthm expr-value-list-rename-expr-vars-of-delete*-when-disjoint
    (implies (and (string-setp bound)
                  (set::emptyp
                   (set::intersect
                    (expr-value-list-free-expr-vars vals)
                    (set::intersect
                     bound
                     (omap::keys (string-string-map-fix renam))))))
             (equal (expr-value-list-rename-expr-vars
                     vals
                     (omap::delete* bound (string-string-map-fix renam)))
                    (expr-value-list-rename-expr-vars vals renam)))
    :flag expr-value-list-rename-expr-vars)
  (defthm string-expr-value-map-rename-expr-vars-of-delete*-when-disjoint
    (implies (and (string-setp bound)
                  (set::emptyp
                   (set::intersect
                    (string-expr-value-map-free-expr-vars map)
                    (set::intersect
                     bound
                     (omap::keys (string-string-map-fix renam))))))
             (equal (string-expr-value-map-rename-expr-vars
                     map
                     (omap::delete* bound (string-string-map-fix renam)))
                    (string-expr-value-map-rename-expr-vars map renam)))
    :flag string-expr-value-map-rename-expr-vars)
  (defthm expr-denv-rename-expr-vars-of-delete*-when-disjoint
    (implies (and (string-setp bound)
                  (set::emptyp
                   (set::intersect
                    (expr-denv-free-expr-vars denv)
                    (set::intersect
                     bound
                     (omap::keys (string-string-map-fix renam))))))
             (equal (expr-denv-rename-expr-vars
                     denv
                     (omap::delete* bound (string-string-map-fix renam)))
                    (expr-denv-rename-expr-vars denv renam)))
    :flag expr-denv-rename-expr-vars)
  :hints
  (("Goal"
    :expand ((:free (renam) (expr-value-rename-expr-vars val renam))
             (:free (renam) (expr-value-list-rename-expr-vars vals renam))
             (:free (renam)
              (string-expr-value-map-rename-expr-vars map renam))
             (:free (renam) (expr-denv-rename-expr-vars denv renam))
             (expr-value-free-expr-vars val)
             (expr-value-list-free-expr-vars vals)
             (string-expr-value-map-free-expr-vars map)
             (expr-denv-free-expr-vars denv))
    :in-theory
    (enable rename-var-string-of-delete*-when-not-relevant
            expr-rename-expr-vars-of-delete*-when-disjoint-typed
            delete*-commute-restricted
            delete-commute-restricted
            emptyp-intersect3-binder-union
            emptyp-intersect3-binder-plain
            emptyp-intersect3-binder-delete
            emptyp-intersect-of-union-left-1
            emptyp-intersect-of-union-left-2
            not-in-when-emptyp-intersect-of-insert
            emptyp-intersect-of-insert-union-1
            emptyp-intersect-of-insert-union-2
            emptyp-intersect-singleton
            set::intersect-in
            omap::in-of-keys-to-assoc))))

; The stability corollary in the form needed by the transition below: if
; the bound names do not occur among the free expression variables of a
; value --- as the freshness of the uniquified names will guarantee for
; the values of the enclosing environments --- then the renaming of the
; value under the reduced map is its renaming under the full map.

(defruled expr-value-rename-expr-vars-stable-under-remove-bound
  (implies (and (string-setp bound)
                (set::emptyp
                 (set::intersect (expr-value-free-expr-vars val) bound)))
           (equal (expr-value-rename-expr-vars
                   val
                   (omap::delete* bound (string-string-map-fix renam)))
                  (expr-value-rename-expr-vars val renam)))
  :use ((:instance expr-value-rename-expr-vars-of-delete*-when-disjoint))
  :enable emptyp-intersect-mono-right)

; The free expression variables of a value in a map are among the free
; expression variables of the map.

(defruled emptyp-intersect-of-free-expr-vars-of-assoc
  (implies (and (string-expr-value-mapp map)
                (set::emptyp
                 (set::intersect (string-expr-value-map-free-expr-vars map)
                                 bound))
                (omap::assoc var map))
           (set::emptyp
            (set::intersect
             (expr-value-free-expr-vars (cdr (omap::assoc var map)))
             bound)))
  :induct (omap::size map)
  :expand ((string-expr-value-map-free-expr-vars map))
  :enable (omap::size
           omap::assoc
           string-expr-value-map-free-expr-vars
           emptyp-intersect-of-insert-union-1
           emptyp-intersect-of-insert-union-2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Transition of DENV-EXPR-VARS-RENAMED-P to the binder-reduced map: if two
; expression environments are related under the full map, then after
; adding the SAME bound variables --- with values related by the REDUCED
; map --- to both, they are related under the reduced map, provided the
; reduced renaming captures none of the bound names AND the bound names do
; not occur among the free expression variables of the old environment
; (the stability hypothesis, discharged by freshness).

(local
 (defun add-exprs2-induct (vars vals renam1 denv1 denv2)
   (if (endp vars)
       (list denv1 denv2)
     (add-exprs2-induct (cdr vars)
                        (cdr vals)
                        renam1
                        (expr-denv-add-expr
                         (car vars)
                         (expr-value-rename-expr-vars (car vals) renam1)
                         denv1)
                        (expr-denv-add-expr (car vars) (car vals) denv2)))))

(defruled assoc-of-exprs-of-expr-denv-add-exprs-when-not-member
  (implies (and (string-listp vars)
                (not (member-equal var vars)))
           (equal (omap::assoc
                   var
                   (expr-denv->exprs (expr-denv-add-exprs vars vals denv)))
                  (omap::assoc var (expr-denv->exprs denv))))
  :induct (expr-denv-add-exprs vars vals denv)
  :enable (expr-denv-add-exprs
           expr-denv-add-expr))

(defruled assoc-of-exprs-of-expr-denv-add-exprs-when-member
  (implies (and (stringp var)
                (string-listp vars)
                (equal (len vars) (len vals))
                (member-equal var vars))
           (equal (omap::assoc
                   var
                   (expr-denv->exprs
                    (expr-denv-add-exprs
                     vars
                     (expr-value-list-rename-expr-vars vals renam1)
                     denv1)))
                  (b* ((pair (omap::assoc
                              var
                              (expr-denv->exprs
                               (expr-denv-add-exprs vars vals denv2)))))
                    (and pair
                         (cons var
                               (expr-value-rename-expr-vars (cdr pair)
                                                            renam1))))))
  :induct (add-exprs2-induct vars vals renam1 denv1 denv2)
  :expand ((expr-denv-add-exprs vars vals denv2)
           (:free (vals) (expr-denv-add-exprs vars vals denv1))
           (expr-value-list-rename-expr-vars vals renam1))
  :enable (expr-denv-add-exprs
           expr-denv-add-expr
           expr-value-list-rename-expr-vars
           assoc-of-exprs-of-expr-denv-add-exprs-when-not-member))

; The renaming of a variable under the reduced map: the identity on the
; bound variables, the full renaming off them; and, by no capture, the
; renaming of an unbound variable is not among the bound ones.

(defruledl rename-var-string-of-remove-bound-when-member
  (implies (and (string-listp vars)
                (stringp var)
                (member-equal var vars))
           (equal (rename-var-string
                   var
                   (omap::delete* (set::mergesort vars)
                                  (string-string-map-fix renam)))
                  var))
  :enable rename-var-string)

(defruledl rename-var-string-of-remove-bound-when-not-member
  (implies (and (string-listp vars)
                (stringp var)
                (not (member-equal var vars)))
           (equal (rename-var-string
                   var
                   (omap::delete* (set::mergesort vars)
                                  (string-string-map-fix renam)))
                  (rename-var-string var renam)))
  :enable rename-var-string)

(defruledl not-member-of-rename-var-string-of-remove-bound
  (implies (and (string-listp vars)
                (stringp var)
                (not (member-equal var vars))
                (renaming-no-capture-p
                 (set::mergesort vars)
                 (omap::delete* (set::mergesort vars)
                                (string-string-map-fix renam))))
           (not (member-equal (rename-var-string var renam) vars)))
  :enable (renaming-no-capture-p
           rename-var-string)
  :use ((:instance omap::cdr-assoc-in-values
                   (omap::key var)
                   (omap::map (omap::delete*
                               (set::mergesort vars)
                               (string-string-map-fix renam))))
        (:instance set::never-in-empty
                   (set::a (cdr (omap::assoc var (string-string-map-fix renam))))
                   (set::x (set::intersect (set::mergesort vars)
                                           (omap::values
                       (omap::delete* (set::mergesort vars)
                                      (string-string-map-fix renam))))))))

(defrule denv-expr-vars-renamed-p-of-add-exprs-remove-bound
  (b* ((bound (set::mergesort vars))
       (renam1 (omap::delete* bound (string-string-map-fix renam))))
    (implies (and (denv-expr-vars-renamed-p new-denv denv renam)
                  (renaming-no-capture-p bound renam1)
                  (string-listp vars)
                  (equal (len vars) (len vals))
                  (set::emptyp
                   (set::intersect
                    (string-expr-value-map-free-expr-vars
                     (expr-denv->exprs denv))
                    bound)))
             (denv-expr-vars-renamed-p
              (expr-denv-add-exprs vars
                                   (expr-value-list-rename-expr-vars vals
                                                                     renam1)
                                   new-denv)
              (expr-denv-add-exprs vars vals denv)
              renam1)))
  :do-not-induct t
  :expand ((:free (renam1)
            (denv-expr-vars-renamed-p
             (expr-denv-add-exprs vars
                                  (expr-value-list-rename-expr-vars vals
                                                                    renam1)
                                  new-denv)
             (expr-denv-add-exprs vars vals denv)
             renam1)))
  :enable (rename-var-string-of-remove-bound-when-member
           rename-var-string-of-remove-bound-when-not-member
           not-member-of-rename-var-string-of-remove-bound
           assoc-of-exprs-of-expr-denv-add-exprs-when-not-member
           expr-value-rename-expr-vars-stable-under-remove-bound
           emptyp-intersect-of-free-expr-vars-of-assoc
           car-of-assoc)
  :hints ((and acl2::stable-under-simplificationp
               '(:cases ((member-equal
                          (denv-expr-vars-renamed-p-witness
                           (expr-denv-add-exprs
                            vars
                            (expr-value-list-rename-expr-vars
                             vals
                             (omap::delete* (set::mergesort vars)
                                            (string-string-map-fix renam)))
                            new-denv)
                           (expr-denv-add-exprs vars vals denv)
                           (omap::delete* (set::mergesort vars)
                                          (string-string-map-fix renam)))
                          vars))
                 :use ((:instance
                        denv-expr-vars-renamed-p-necc
                        (var (denv-expr-vars-renamed-p-witness
                              (expr-denv-add-exprs
                               vars
                               (expr-value-list-rename-expr-vars
                                vals
                                (omap::delete* (set::mergesort vars)
                                               (string-string-map-fix renam)))
                               new-denv)
                              (expr-denv-add-exprs vars vals denv)
                              (omap::delete* (set::mergesort vars)
                                             (string-string-map-fix renam))))
                        (new-denv new-denv)
                        (denv denv))
                       (:instance
                        assoc-of-exprs-of-expr-denv-add-exprs-when-member
                        (var (denv-expr-vars-renamed-p-witness
                              (expr-denv-add-exprs
                               vars
                               (expr-value-list-rename-expr-vars
                                vals
                                (omap::delete* (set::mergesort vars)
                                               (string-string-map-fix renam)))
                               new-denv)
                              (expr-denv-add-exprs vars vals denv)
                              (omap::delete* (set::mergesort vars)
                                             (string-string-map-fix renam))))
                        (renam1 (omap::delete* (set::mergesort vars)
                                               (string-string-map-fix renam)))
                        (denv1 new-denv)
                        (denv2 denv))))))
  :otf-flg t)
