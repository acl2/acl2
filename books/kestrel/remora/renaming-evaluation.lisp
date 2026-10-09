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
(include-book "variable-name-sets")

(include-book "kestrel/utilities/defopeners" :dir :system)

(include-book "portcullis")

(local (include-book "osets"))
(local (include-book "omaps"))

(local (include-book "kestrel/utilities/lists/len-const-theorems" :dir :system))

; The tau system is needed by only one proof in this book (noted below, where
; it is switched back on); running it on every goal of the rest is pure
; overhead, so it is off by default here.
(local (acl2::in-theory (acl2::disable (:e acl2::tau-system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ renaming-evaluation
  :parents (unique-names-validation)
  :short "Renamings of ispace and type variables: variables, sets of
          variables, and the free variables of renamed types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This book is the base of the proof of
     @(tsee eval-top-expr-of-expr-uniquify-names)
     (see @(see unique-names-validation)).  It provides the facts about the
     renamings of ispace and type variables (see @(see unique-names)) that
     the alpha-relatedness relations of @(see uniquify-alpha-relations) and
     the main induction of @(see uniquify-evaluation) consume: the renaming
     of a single tagged variable (@(tsee rename-ispace-var),
     @(tsee rename-type-var)) and of a set of variables
     (@(tsee ispace-var-set-rename-ispace-vars),
     @(tsee type-var-set-rename-type-vars)), with the preimage witnesses
     that invert membership in such an image; the free-variable laws of
     renamed dimensions, shapes, ispaces, and types --- the free variables
     of a renamed type are the renaming image of the free variables of the
     original when the renaming captures none, and an ispace renaming
     leaves the free type variables alone and vice versa --- extended to
     type annotations and parameter lists; the commutation of the renamings
     with the currying of types that evaluation performs; the success- and
     failure-direction relations between the ispace layers of two dynamic
     environments (@('denv-ispace-vars-covered-p'),
     @('denv-ispace-vars-avoided-p'), @('type-var-map-avoided-p'))
     and their monotonicity; and the commutation of the expression layer's
     accessor with the ispace extension of an expression environment.")
   (xdoc::p
    "The book once also carried the first design of the validation proof:
     the evaluation of renamed dimensions, shapes, ispaces, and types under
     renamings of the ispace and type variables, the value side of the
     renamings (renaming the abstract syntax embedded in type and
     expression values and in their captured environments), and the
     preservation of pointwise environment relations under extension and
     under the renamings reduced at binders.  That design was superseded by
     the witness-indexed relations of @(see uniquify-alpha-relations) (see
     the design notes there), and its material has been removed."))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Support for the type-level theorems: the free variables of renamed
; dimensions, shapes, ispaces, and types.
;
; The free ispace variables of a renamed type are the elementwise renamings
; of the free ispace variables of the original type, provided the renaming
; captures no variables, while the free type variables are untouched by an
; ispace renaming.  These are the image laws that the free-variable
; correspondence of alpha-related ASTs (UNIQUIFY-ALPHA-RELATIONS) rests on.

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

; The free ispace variables of dimensions are all dimension variables.

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
  :enable ((:e acl2::tau-system)   ; tau does the ISPACE-VAR-KIND case analysis
           ispace-var-set-rename-ispace-vars
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Commutation of the ispace-variable renaming of types with the currying of
; types performed by evaluation.
;
; The rewriter's heuristics decline to open TYPE-RENAME-ISPACE-VARS on the Pi
; and Sigma cases (the bound-variable removal changes the renaming arguments
; of the recursive calls), so we generate hypothesis-guarded opener rules for
; it.

(local (acl2::defopeners type-rename-ispace-vars))

; Commutation of ispace-variable renaming with the currying of product
; types performed by evaluation (see pi-curried-body): renaming the curried
; body under the maps reduced by the first parameter equals currying the
; body renamed under the maps reduced by all the parameters.  The crux is
; that removing the first parameter and then the remaining ones from the
; renaming maps equals removing all the parameters at once; that lemma is
; exported, since UNIQUIFY-ALPHA-RELATIONS uses it too.  (It is proved
; here rather than with DIM/SHAPE-RENAME-REMOVE-BOUND because it needs the
; name-set lemmas of VARIABLE-NAME-SETS.)

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
           mergesort-of-cons))

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
           make-type-pi/pin
           mergesort-when-singleton
           acl2::equal-len-const)
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
           make-type-sigma/sigman
           mergesort-when-singleton
           acl2::equal-len-const)
  :use ((:instance dim/shape-rename-remove-bound-of-insert-then-rest
                   (var (car params))
                   (rest (cdr params)))))

; The ispace-variable analogue for the currying of universal types:
; since universal types bind no ispace variables,
; the renaming maps are not reduced, and the commutation is direct.

(defrule type-rename-ispace-vars-of-forall-curried-body
  (implies (type-var-listp params)
           (equal (type-rename-ispace-vars (forall-curried-body params body)
                                           dim-renam shape-renam)
                  (forall-curried-body params
                                       (type-rename-ispace-vars body
                                                                dim-renam
                                                                shape-renam))))
  :enable (forall-curried-body
           make-type-forall/foralln))

; The analogue for the currying of term lambda abstractions
; (see lambda-curried-body), laid down ahead of that currying:
; lambda abstractions bind no ispace variables,
; but their parameter type annotations may contain ispace variables,
; so all components are renamed and the commutation is direct.

(local (acl2::defopeners expr-rename-ispace-vars))
(local (acl2::defopeners atom-rename-ispace-vars))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Renamings of type variables: the variable and set-image level, and the
; free-variable laws, mirroring the ispace-variable development above.

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

; Support for the type-level theorems, mirroring the development for ispace
; renamings: the free type variables of a type with renamed type variables
; are the elementwise renamings of the free type variables of the type (when
; the renaming captures no variables), and the free ispace variables are
; untouched.

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Commutation of the type-variable renaming of types with the currying of
; types performed by evaluation, mirroring the ispace-variable development.

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
  :enable (pi-curried-body
           make-type-pi/pin))

(defrule type-rename-type-vars-of-sigma-curried-body
  (implies (and (ispace-var-listp params)
                (consp params))
           (equal (type-rename-type-vars (sigma-curried-body params body)
                                         atom-renam array-renam)
                  (sigma-curried-body params
                                      (type-rename-type-vars body
                                                             atom-renam
                                                             array-renam))))
  :enable (sigma-curried-body
           make-type-sigma/sigman))

; The type-variable commutation for the currying of universal types
; mirrors the ispace-variable one for the currying of product types:
; the crux is again that removing the first parameter and then the
; remaining ones from the renaming maps equals removing all the
; parameters at once (also exported, for UNIQUIFY-ALPHA-RELATIONS).

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
           mergesort-of-cons))

(defrule type-rename-type-vars-of-forall-curried-body
  (implies (type-var-listp params)
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
           make-type-forall/foralln
           mergesort-when-singleton
           acl2::equal-len-const)
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

; The expression-variable analogue for the currying of
; term lambda abstractions, which bind expression variables:
; renaming the curried body under the map reduced by the first parameter
; equals currying the body renamed under the map reduced by
; all the parameters.

(local (acl2::defopeners expr-rename-expr-vars))
(local (acl2::defopeners atom-rename-expr-vars))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Accessor commutation for the layered environment extensions.  With the
; layered environments (an ISPACE-DENV inside a TYPE-DENV inside an
; EXPR-DENV), an extension in another namespace either leaves a layer's map
; untouched or delegates to the corresponding extension of an inner layer.
; (The lemmas for the TYPE-DENV layer are in TYPE-VALUES-AND-ENVIRONMENTS.)

(defrule expr-denv->exprs-of-expr-denv-add-ispace
  (equal (expr-denv->exprs (expr-denv-add-ispace var ival denv))
         (expr-denv->exprs denv))
  :enable expr-denv-add-ispace)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The renaming of a variable under the reduced maps: the identity on the
; bound variables, the full renaming off them.  (Exported: the uniquify
; books use it too.)

(defruled rename-ispace-var-of-remove-bound-when-not-in
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Environment relations for the success and failure directions of a
; renaming: the renamed key is
; present with the same value (covered), and a variable absent on the old
; side stays absent under the renaming (avoided).  The avoidance shrinks
; with the AST in the inductions that consume it, whence the monotonicity.

(acl2::defun-sk denv-ispace-vars-covered-p (new-denv denv
                                            dim-renam shape-renam)
  (forall (var)
          (implies (and (ispace-varp var)
                        (omap::assoc var (ispace-denv->ispaces denv)))
                   (equal (omap::assoc (rename-ispace-var var
                                                          dim-renam
                                                          shape-renam)
                                       (ispace-denv->ispaces new-denv))
                          (cons (rename-ispace-var var
                                                   dim-renam
                                                   shape-renam)
                                (cdr (omap::assoc
                                      var
                                      (ispace-denv->ispaces denv)))))))
  :rewrite :direct)

(in-theory (disable denv-ispace-vars-covered-p))

(acl2::defun-sk denv-ispace-vars-avoided-p (new-denv denv
                                            dim-renam shape-renam
                                            vars)
  (forall (var)
          (implies (and (set::in var (ispace-var-set-fix vars))
                        (not (omap::assoc var
                                          (ispace-denv->ispaces denv))))
                   (not (omap::assoc (rename-ispace-var var
                                                        dim-renam
                                                        shape-renam)
                                     (ispace-denv->ispaces new-denv)))))
  :rewrite :direct)

(in-theory (disable denv-ispace-vars-avoided-p))

(acl2::defun-sk type-var-map-avoided-p (new-map map
                                        atom-renam array-renam
                                        vars)
  (forall (var)
          (implies (and (set::in var (type-var-set-fix vars))
                        (not (omap::assoc var
                                          (type-var-type-value-map-fix map))))
                   (not (omap::assoc (rename-type-var var
                                                      atom-renam array-renam)
                                     (type-var-type-value-map-fix new-map)))))
  :rewrite :direct)

(in-theory (disable type-var-map-avoided-p))

(defruled denv-ispace-vars-avoided-p-monotone
  (implies (and (denv-ispace-vars-avoided-p new-denv denv
                                            dim-renam shape-renam vars2)
                (set::subset (ispace-var-set-fix vars1)
                             (ispace-var-set-fix vars2)))
           (denv-ispace-vars-avoided-p new-denv denv
                                       dim-renam shape-renam vars1))
  :expand ((denv-ispace-vars-avoided-p new-denv denv
                                       dim-renam shape-renam vars1))
  :use ((:instance denv-ispace-vars-avoided-p-necc
                   (vars vars2)
                   (var (denv-ispace-vars-avoided-p-witness
                         new-denv denv dim-renam shape-renam vars1)))
        (:instance set::subset-in-2
                   (x (ispace-var-set-fix vars1))
                   (y (ispace-var-set-fix vars2))
                   (a (denv-ispace-vars-avoided-p-witness
                       new-denv denv dim-renam shape-renam vars1)))))

(defruled type-var-map-avoided-p-monotone
  (implies (and (type-var-map-avoided-p new-map map
                                        atom-renam array-renam vars2)
                (set::subset (type-var-set-fix vars1)
                             (type-var-set-fix vars2)))
           (type-var-map-avoided-p new-map map
                                   atom-renam array-renam vars1))
  :expand ((type-var-map-avoided-p new-map map
                                   atom-renam array-renam vars1))
  :use ((:instance type-var-map-avoided-p-necc
                   (vars vars2)
                   (var (type-var-map-avoided-p-witness
                         new-map map atom-renam array-renam vars1)))
        (:instance set::subset-in-2
                   (x (type-var-set-fix vars1))
                   (y (type-var-set-fix vars2))
                   (a (type-var-map-avoided-p-witness
                       new-map map atom-renam array-renam vars1)))))

(defruled denv-ispace-vars-covered-p-of-restrict
  (implies (and (denv-ispace-vars-covered-p new-ienv ienv
                                            dim-renam shape-renam)
                (ispace-var-setp vars)
                (ispace-var-setp new-vars)
                (set::subset (ispace-var-set-rename-ispace-vars
                              vars dim-renam shape-renam)
                             new-vars))
           (denv-ispace-vars-covered-p
            (ispace-denv (omap::restrict
                          new-vars
                          (ispace-denv->ispaces new-ienv)))
            (ispace-denv (omap::restrict
                          vars
                          (ispace-denv->ispaces ienv)))
            dim-renam shape-renam))
  :enable (denv-ispace-vars-covered-p
           omap::assoc-of-restrict)
  :expand ((denv-ispace-vars-covered-p
            (ispace-denv (omap::restrict
                          new-vars
                          (ispace-denv->ispaces new-ienv)))
            (ispace-denv (omap::restrict
                          vars
                          (ispace-denv->ispaces ienv)))
            dim-renam shape-renam))
  :use ((:instance denv-ispace-vars-covered-p-necc
                   (new-denv new-ienv)
                   (denv ienv)
                   (var (denv-ispace-vars-covered-p-witness
                         (ispace-denv (omap::restrict
                                       new-vars
                                       (ispace-denv->ispaces new-ienv)))
                         (ispace-denv (omap::restrict
                                       vars
                                       (ispace-denv->ispaces ienv)))
                         dim-renam shape-renam)))
        (:instance in-of-rename-ispace-var-of-ispace-var-set-rename-ispace-vars
                   (var (denv-ispace-vars-covered-p-witness
                         (ispace-denv (omap::restrict
                                       new-vars
                                       (ispace-denv->ispaces new-ienv)))
                         (ispace-denv (omap::restrict
                                       vars
                                       (ispace-denv->ispaces ienv)))
                         dim-renam shape-renam))
                   (vars vars))
        (:instance set::subset-in-2
                   (x (ispace-var-set-rename-ispace-vars
                       vars dim-renam shape-renam))
                   (y new-vars)
                   (a (rename-ispace-var
                       (denv-ispace-vars-covered-p-witness
                        (ispace-denv (omap::restrict
                                      new-vars
                                      (ispace-denv->ispaces new-ienv)))
                        (ispace-denv (omap::restrict
                                      vars
                                      (ispace-denv->ispaces ienv)))
                        dim-renam shape-renam)
                       dim-renam shape-renam)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Renaming leaves the variables of a parameter list alone: it rewrites only
; the type annotations.

(defruled var+type?-list->var-of-var+type?-list-rename-ispace-vars
  (equal (var+type?-list->var
          (var+type?-list-rename-ispace-vars params dim-renam shape-renam))
         (var+type?-list->var params))
  :induct (len params)
  :enable (var+type?-list-rename-ispace-vars
           var+type?-rename-ispace-vars
           var+type?-list->var
           len))

(defruled var+type?-list->var-of-var+type?-list-rename-type-vars
  (equal (var+type?-list->var
          (var+type?-list-rename-type-vars params atom-renam array-renam))
         (var+type?-list->var params))
  :induct (len params)
  :enable (var+type?-list-rename-type-vars
           var+type?-rename-type-vars
           var+type?-list->var
           len))

(defruled var+type?-list->var-of-var+type?-list-rename-all-vars
  (equal (var+type?-list->var (var+type?-list-rename-all-vars params r))
         (var+type?-list->var params))
  :enable (var+type?-list-rename-all-vars
           var+type?-list->var-of-var+type?-list-rename-ispace-vars
           var+type?-list->var-of-var+type?-list-rename-type-vars))

(defruled var+type?-list->var-of-var+type?-list-set-vars
  (implies (equal (len vars) (len params))
           (equal (var+type?-list->var (var+type?-list-set-vars vars params))
                  (string-list-fix vars)))
  :induct (var+type?-list-set-vars vars params)
  :enable (var+type?-list-set-vars var+type?-list->var len))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The image of a set of variables under a renaming: its type, its value on
; the empty and singleton sets and under the map fixers, and the preimage
; that witnesses membership in it.

(defrule setp-of-type-var-set-rename-type-vars
  (set::setp (type-var-set-rename-type-vars vars atom-renam array-renam)))

(defrule setp-of-ispace-var-set-rename-ispace-vars
  (set::setp (ispace-var-set-rename-ispace-vars vars dim-renam
                                                shape-renam)))

(defrule type-var-set-rename-type-vars-of-nil
  (equal (type-var-set-rename-type-vars nil atom-m array-m) nil)
  :enable type-var-set-rename-type-vars)

(defrule ispace-var-set-rename-ispace-vars-of-nil
  (equal (ispace-var-set-rename-ispace-vars nil dim-m shape-m) nil)
  :enable ispace-var-set-rename-ispace-vars)

(defrule type-var-set-rename-type-vars-of-string-string-map-fix-atom
  (equal (type-var-set-rename-type-vars
          vars (string-string-map-fix atom-renam) array-renam)
         (type-var-set-rename-type-vars vars atom-renam array-renam))
  :induct (type-var-set-rename-type-vars vars atom-renam array-renam)
  :enable type-var-set-rename-type-vars)

(defrule type-var-set-rename-type-vars-of-string-string-map-fix-array
  (equal (type-var-set-rename-type-vars
          vars atom-renam (string-string-map-fix array-renam))
         (type-var-set-rename-type-vars vars atom-renam array-renam))
  :induct (type-var-set-rename-type-vars vars atom-renam array-renam)
  :enable type-var-set-rename-type-vars)

(defrule ispace-var-set-rename-ispace-vars-of-string-string-map-fix-dim
  (equal (ispace-var-set-rename-ispace-vars
          vars (string-string-map-fix dim-renam) shape-renam)
         (ispace-var-set-rename-ispace-vars vars dim-renam shape-renam))
  :induct (ispace-var-set-rename-ispace-vars vars dim-renam shape-renam)
  :enable ispace-var-set-rename-ispace-vars)

(defrule ispace-var-set-rename-ispace-vars-of-string-string-map-fix-shape
  (equal (ispace-var-set-rename-ispace-vars
          vars dim-renam (string-string-map-fix shape-renam))
         (ispace-var-set-rename-ispace-vars vars dim-renam shape-renam))
  :induct (ispace-var-set-rename-ispace-vars vars dim-renam shape-renam)
  :enable ispace-var-set-rename-ispace-vars)

(define type-var-set-rename-type-vars-preimage ((y type-varp)
                                                (vars type-var-setp)
                                                (atom-renam
                                                 string-string-mapp)
                                                (array-renam
                                                 string-string-mapp))
  :returns (x type-varp)
  :short "Preimage witness for @(tsee type-var-set-rename-type-vars)."
  (b* (((when (set::emptyp (type-var-set-fix vars)))
        (type-var-atom "")))
    (if (equal (rename-type-var (set::head vars) atom-renam array-renam)
               (type-var-fix y))
        (type-var-fix (set::head vars))
      (type-var-set-rename-type-vars-preimage y (set::tail vars)
                                              atom-renam array-renam)))
  :prepwork ((local (in-theory (enable emptyp-of-type-var-set-fix))))
  :verify-guards :after-returns)

(defruled type-var-set-rename-type-vars-preimage-witnesses
  (implies (and (type-var-setp vars)
                (set::in y (type-var-set-rename-type-vars
                            vars atom-renam array-renam)))
           (b* ((x (type-var-set-rename-type-vars-preimage
                    y vars atom-renam array-renam)))
             (and (set::in x vars)
                  (equal (rename-type-var x atom-renam array-renam) y))))
  :induct (type-var-set-rename-type-vars-preimage y vars
                                                  atom-renam array-renam)
  :enable (type-var-set-rename-type-vars-preimage
           type-var-set-rename-type-vars))

(define ispace-var-set-rename-ispace-vars-preimage ((y ispace-varp)
                                                    (vars ispace-var-setp)
                                                    (dim-renam
                                                     string-string-mapp)
                                                    (shape-renam
                                                     string-string-mapp))
  :returns (x ispace-varp)
  :short "Preimage witness for
          @(tsee ispace-var-set-rename-ispace-vars)."
  (b* (((when (set::emptyp (ispace-var-set-fix vars)))
        (ispace-var-dim "")))
    (if (equal (rename-ispace-var (set::head vars) dim-renam shape-renam)
               (ispace-var-fix y))
        (ispace-var-fix (set::head vars))
      (ispace-var-set-rename-ispace-vars-preimage y (set::tail vars)
                                                  dim-renam
                                                  shape-renam)))
  :prepwork ((local (in-theory (enable emptyp-of-ispace-var-set-fix))))
  :verify-guards :after-returns)

(defruled ispace-var-set-rename-ispace-vars-preimage-witnesses
  (implies (and (ispace-var-setp vars)
                (set::in y (ispace-var-set-rename-ispace-vars
                            vars dim-renam shape-renam)))
           (b* ((x (ispace-var-set-rename-ispace-vars-preimage
                    y vars dim-renam shape-renam)))
             (and (set::in x vars)
                  (equal (rename-ispace-var x dim-renam shape-renam)
                         y))))
  :induct (ispace-var-set-rename-ispace-vars-preimage y vars
                                                      dim-renam
                                                      shape-renam)
  :enable (ispace-var-set-rename-ispace-vars-preimage
           ispace-var-set-rename-ispace-vars))

(defruled not-in-type-var-image-when-subset
  (implies (and (set::subset a b)
                (type-var-setp a)
                (type-var-setp b)
                (not (set::in elt (type-var-set-rename-type-vars
                                   b atom-m array-m))))
           (not (set::in elt (type-var-set-rename-type-vars
                              a atom-m array-m))))
  :use ((:instance type-var-set-rename-type-vars-preimage-witnesses
                   (y elt) (vars a)
                   (atom-renam atom-m) (array-renam array-m))
        (:instance in-of-rename-type-var-of-type-var-set-rename-type-vars
                   (var (type-var-set-rename-type-vars-preimage
                         elt a atom-m array-m))
                   (vars b)
                   (atom-renam atom-m) (array-renam array-m))
        (:instance set::subset-in
                   (a (type-var-set-rename-type-vars-preimage
                       elt a atom-m array-m))
                   (x a) (y b))))

(defruled not-in-ispace-var-image-when-subset
  (implies (and (set::subset a b)
                (ispace-var-setp a)
                (ispace-var-setp b)
                (not (set::in elt (ispace-var-set-rename-ispace-vars
                                   b dim-m shape-m))))
           (not (set::in elt (ispace-var-set-rename-ispace-vars
                              a dim-m shape-m))))
  :use ((:instance ispace-var-set-rename-ispace-vars-preimage-witnesses
                   (y elt) (vars a)
                   (dim-renam dim-m) (shape-renam shape-m))
        (:instance in-of-rename-ispace-var-of-ispace-var-set-rename-ispace-vars
                   (var (ispace-var-set-rename-ispace-vars-preimage
                         elt a dim-m shape-m))
                   (vars b)
                   (dim-renam dim-m) (shape-renam shape-m))
        (:instance set::subset-in
                   (a (ispace-var-set-rename-ispace-vars-preimage
                       elt a dim-m shape-m))
                   (x a) (y b))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Free variables of renamed types, annotations and parameter lists.  The
; renaming of ispace variables leaves the free type variables alone and
; vice versa; rebinding the variables of a parameter list leaves the free
; variables of its annotations alone.

(defrule free-type-vars-of-type-option-rename-ispace-vars
  (equal (type-option-free-type-vars
          (type-option-rename-ispace-vars ty? dim-renam shape-renam))
         (type-option-free-type-vars ty?))
  :enable (type-option-free-type-vars
           type-option-rename-ispace-vars
           type-option-some->val-when-typep)
  :use ((:instance free-type-vars-of-type-rename-ispace-vars
                   (type (type-option-some->val ty?)))))

(defrule free-type-vars-of-var+type?-rename-ispace-vars
  (equal (var+type?-free-type-vars
          (var+type?-rename-ispace-vars p dim-renam shape-renam))
         (var+type?-free-type-vars p))
  :enable (var+type?-free-type-vars
           var+type?-rename-ispace-vars))

(defrule free-type-vars-of-var+type?-list-rename-ispace-vars
  (equal (var+type?-list-free-type-vars
          (var+type?-list-rename-ispace-vars params dim-renam shape-renam))
         (var+type?-list-free-type-vars params))
  :induct (len params)
  :enable (var+type?-list-free-type-vars
           var+type?-list-rename-ispace-vars))

(defrule free-type-vars-of-var+type?-list-set-vars
  (equal (var+type?-list-free-type-vars
          (var+type?-list-set-vars names params))
         (var+type?-list-free-type-vars params))
  :induct (var+type?-list-set-vars names params)
  :enable (var+type?-list-set-vars
           var+type?-list-free-type-vars
           var+type?-free-type-vars))

(defrule free-type-vars-of-var+type?-list-rename-type-vars
  (implies (var+type?-list-rename-type-vars-no-capture-p
            params atom-m array-m)
           (equal (var+type?-list-free-type-vars
                   (var+type?-list-rename-type-vars params atom-m
                                                    array-m))
                  (type-var-set-rename-type-vars
                   (var+type?-list-free-type-vars params)
                   atom-m array-m)))
  :induct (len params)
  :enable (type-option-some->val-when-typep
           var+type?-list-free-type-vars
           var+type?-list-rename-type-vars
           var+type?-list-rename-type-vars-no-capture-p
           var+type?-free-type-vars
           var+type?-rename-type-vars
           var+type?-rename-type-vars-no-capture-p
           type-option-free-type-vars
           type-option-rename-type-vars
           type-option-rename-type-vars-no-capture-p))

(defruled free-type-vars-of-projected-renamed-annotation
  (implies (and (equal ty?new
                       (type-rename-type-vars
                        (type-option-some->val
                         (type-rename-ispace-vars ty dim-m shape-m))
                        atom-m array-m))
                (typep ty)
                (type-rename-ispace-vars-no-capture-p ty dim-m shape-m)
                (type-rename-type-vars-no-capture-p
                 (type-rename-ispace-vars ty dim-m shape-m)
                 atom-m array-m))
           (equal (type-free-type-vars (type-option-some->val ty?new))
                  (type-var-set-rename-type-vars
                   (type-free-type-vars ty)
                   atom-m array-m)))
  :enable type-option-some->val-when-typep)

(defruled free-type-vars-of-renamed-type-when-equal
  (implies (and (equal tynew
                       (type-rename-type-vars
                        (type-rename-ispace-vars ty dim-m shape-m)
                        atom-m array-m))
                (type-rename-ispace-vars-no-capture-p ty dim-m shape-m)
                (type-rename-type-vars-no-capture-p
                 (type-rename-ispace-vars ty dim-m shape-m)
                 atom-m array-m))
           (equal (type-free-type-vars tynew)
                  (type-var-set-rename-type-vars
                   (type-free-type-vars ty)
                   atom-m array-m))))

(defruled free-type-vars-of-renamed-type-list-when-equal
  (implies (and (equal tysnew
                       (type-list-rename-type-vars
                        (type-list-rename-ispace-vars tys dim-m shape-m)
                        atom-m array-m))
                (type-list-rename-ispace-vars-no-capture-p tys dim-m
                                                           shape-m)
                (type-list-rename-type-vars-no-capture-p
                 (type-list-rename-ispace-vars tys dim-m shape-m)
                 atom-m array-m))
           (equal (type-list-free-type-vars tysnew)
                  (type-var-set-rename-type-vars
                   (type-list-free-type-vars tys)
                   atom-m array-m))))

(defruled free-type-vars-of-set-vars-renamed-params
  (implies (and (equal pnew
                       (var+type?-list-set-vars
                        names
                        (var+type?-list-rename-type-vars
                         (var+type?-list-rename-ispace-vars params dim-m
                                                            shape-m)
                         atom-m array-m)))
                (var+type?-list-rename-type-vars-no-capture-p
                 (var+type?-list-rename-ispace-vars params dim-m shape-m)
                 atom-m array-m))
           (equal (var+type?-list-free-type-vars pnew)
                  (type-var-set-rename-type-vars
                   (var+type?-list-free-type-vars params)
                   atom-m array-m))))

(defrule free-ispace-vars-of-var+type?-list-set-vars
  (equal (var+type?-list-free-ispace-vars
          (var+type?-list-set-vars names params))
         (var+type?-list-free-ispace-vars params))
  :induct (var+type?-list-set-vars names params)
  :enable (var+type?-list-set-vars
           var+type?-list-free-ispace-vars
           var+type?-free-ispace-vars))

(defrule free-ispace-vars-of-type-option-rename-ispace-vars
  (implies (type-option-rename-ispace-vars-no-capture-p ty? dim-m shape-m)
           (equal (type-option-free-ispace-vars
                   (type-option-rename-ispace-vars ty? dim-m shape-m))
                  (ispace-var-set-rename-ispace-vars
                   (type-option-free-ispace-vars ty?)
                   dim-m shape-m)))
  :enable (type-option-free-ispace-vars
           type-option-rename-ispace-vars
           type-option-rename-ispace-vars-no-capture-p
           type-option-some->val-when-typep)
  :use ((:instance free-ispace-vars-of-type-rename-ispace-vars
                   (type (type-option-some->val ty?)))))

(defrule free-ispace-vars-of-type-option-rename-type-vars
  (equal (type-option-free-ispace-vars
          (type-option-rename-type-vars ty? atom-m array-m))
         (type-option-free-ispace-vars ty?))
  :enable (type-option-free-ispace-vars
           type-option-rename-type-vars
           type-option-some->val-when-typep)
  :use ((:instance free-ispace-vars-of-type-rename-type-vars
                   (type (type-option-some->val ty?)))))

(defrule free-ispace-vars-of-var+type?-list-rename-type-vars
  (equal (var+type?-list-free-ispace-vars
          (var+type?-list-rename-type-vars params atom-m array-m))
         (var+type?-list-free-ispace-vars params))
  :induct (len params)
  :enable (var+type?-list-free-ispace-vars
           var+type?-list-rename-type-vars
           var+type?-free-ispace-vars
           var+type?-rename-type-vars))

(defrule free-ispace-vars-of-var+type?-list-rename-ispace-vars
  (implies (var+type?-list-rename-ispace-vars-no-capture-p
            params dim-m shape-m)
           (equal (var+type?-list-free-ispace-vars
                   (var+type?-list-rename-ispace-vars params dim-m
                                                      shape-m))
                  (ispace-var-set-rename-ispace-vars
                   (var+type?-list-free-ispace-vars params)
                   dim-m shape-m)))
  :induct (len params)
  :enable (var+type?-list-free-ispace-vars
           var+type?-list-rename-ispace-vars
           var+type?-free-ispace-vars
           var+type?-rename-ispace-vars
           var+type?-list-rename-ispace-vars-no-capture-p
           var+type?-rename-ispace-vars-no-capture-p))

(defruled free-ispace-vars-of-renamed-type-when-equal
  (implies (and (equal tynew
                       (type-rename-type-vars
                        (type-rename-ispace-vars ty dim-m shape-m)
                        atom-m array-m))
                (type-rename-ispace-vars-no-capture-p ty dim-m shape-m))
           (equal (type-free-ispace-vars tynew)
                  (ispace-var-set-rename-ispace-vars
                   (type-free-ispace-vars ty)
                   dim-m shape-m))))

(defruled free-ispace-vars-of-projected-renamed-annotation
  (implies (and (equal ty?new
                       (type-rename-type-vars
                        (type-option-some->val
                         (type-rename-ispace-vars ty dim-m shape-m))
                        atom-m array-m))
                (typep ty)
                (type-rename-ispace-vars-no-capture-p ty dim-m shape-m))
           (equal (type-free-ispace-vars (type-option-some->val ty?new))
                  (ispace-var-set-rename-ispace-vars
                   (type-free-ispace-vars ty)
                   dim-m shape-m)))
  :enable type-option-some->val-when-typep)

(defruled free-ispace-vars-of-renamed-type-list-when-equal
  (implies (and (equal tysnew
                       (type-list-rename-type-vars
                        (type-list-rename-ispace-vars tys dim-m shape-m)
                        atom-m array-m))
                (type-list-rename-ispace-vars-no-capture-p tys dim-m
                                                           shape-m))
           (equal (type-list-free-ispace-vars tysnew)
                  (ispace-var-set-rename-ispace-vars
                   (type-list-free-ispace-vars tys)
                   dim-m shape-m))))

(defruled free-ispace-vars-of-set-vars-renamed-params
  (implies (and (equal pnew
                       (var+type?-list-set-vars
                        names
                        (var+type?-list-rename-type-vars
                         (var+type?-list-rename-ispace-vars params dim-m
                                                            shape-m)
                         atom-m array-m)))
                (var+type?-list-rename-ispace-vars-no-capture-p
                 params dim-m shape-m))
           (equal (var+type?-list-free-ispace-vars pnew)
                  (ispace-var-set-rename-ispace-vars
                   (var+type?-list-free-ispace-vars params)
                   dim-m shape-m))))

(defruled free-ispace-vars-of-renamed-ispace-when-equal
  (implies (equal ispnew (ispace-rename-ispace-vars isp dim-m shape-m))
           (equal (ispace-free-ispace-vars ispnew)
                  (ispace-var-set-rename-ispace-vars
                   (ispace-free-ispace-vars isp)
                   dim-m shape-m))))

(defruled free-ispace-vars-of-renamed-ispace-list-when-equal
  (implies (equal ispsnew (ispace-list-rename-ispace-vars isps dim-m
                                                          shape-m))
           (equal (ispace-list-free-ispace-vars ispsnew)
                  (ispace-var-set-rename-ispace-vars
                   (ispace-list-free-ispace-vars isps)
                   dim-m shape-m))))
