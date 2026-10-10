; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "renaming-evaluation")
(include-book "value-groundness")

; The groundness fold appears in the leaf cases of the value relations below;
; its functions loop with the rewriter when enabled, so they stay disabled
; here and are expanded on demand.
(in-theory (disable expr-value-groundp
                    expr-value-list-groundp
                    primop-value-groundp
                    string-expr-value-map-groundp
                    expr-denv-groundp
                    type-value-groundp
                    type-value-list-groundp))
(include-book "unique-names")

(include-book "portcullis")

(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "omaps"))
(local (include-book "kestrel/utilities/lists/len-const-theorems" :dir :system))

; The tau system contributes to no proof in this book; running it on every
; goal is pure overhead here, so we turn it off.
(local (acl2::in-theory (acl2::disable (:e acl2::tau-system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ uniquify-alpha-relations
  :parents (unique-names)
  :short "Alpha-relatedness of ASTs and of expression values
          modulo in-scope renamings: the invariant of the main
          uniquification induction."
  :long
  (xdoc::topstring
   (xdoc::p
    "The main induction for @(tsee eval-top-expr-of-expr-uniquify-names),
     carried out in @(see uniquify-evaluation), needs an invariant
     relating the values produced by the two evaluations.  Renaming the
     values in the style of the AST renamings of @(see unique-names) does
     not suffice for lambda values: the uniquification renames a lambda's
     parameters to fresh names (see @(tsee uniq-expr-params)), while a
     value renaming would keep them and merely reduce the renaming for the
     body.  So the invariant must be a relation that, at
     each binder, extends the renamings by the correspondence between the
     original parameters and the (arbitrary) parameters found on the
     uniquified side.  This book defines that relation, in four layers,
     and proves the facts about it that the induction and its bridges to
     the uniquification traversal consume.")
   (xdoc::p
    "The AST layer: @(tsee expr-alpha-related-p) (and companions over the
     @(see exprs/atoms/binds) clique) relates a candidate uniquified AST
     to an original AST under a bundle of in-scope renamings.  It has
     exactly the traversal structure of @(tsee uniq-expr), but is free of
     the fresh-name generation policy --- the new binder names are taken
     from the left-hand AST, whatever they are, and the renamings are
     extended by the pointwise correspondence (via
     @(tsee extend-renaming), so a binder that keeps its name clears any
     stale outer entry, exactly as in the traversal).  Accordingly the
     output of the traversal is alpha-related to its input under the
     traversal's own renamings, hypothesis-free: see
     @('uniq-alpha-bridge') and
     @('expr-alpha-related-p-of-expr-uniquify-names').")
   (xdoc::p
    "The freshness layer: @(tsee expr-alpha-fresh-p) (and companions) is
     the companion fold that asserts, of the new binder names that the
     AST relation leaves arbitrary, the no-capture and support-set
     conditions that the environment-extension steps of the induction
     need (see @(tsee name-fresh-ok)).  Its bridge --- that the
     traversal's output satisfies it --- rests on the crux obligation
     @(tsee name-fresh-ok-of-fresh-bind-name) proved here and is
     completed in @(see uniquify-freshness).  The free-variable
     correspondence proved here for the three namespaces
     (@('expr-free-expr-vars-of-alpha-related'),
     @('expr-free-type-vars-of-alpha-related'), and
     @('expr-free-ispace-vars-of-alpha-related')) --- the free variables
     of the uniquified AST are the renaming image of those of the
     original --- is what the fold's no-capture conjuncts buy.")
   (xdoc::p
    "The environment layer relates the dynamic environments of the two
     evaluations, split by direction, since the uniquified run extends
     its environments at freshened keys: in the success direction a
     lookup that succeeds on the original side succeeds, suitably related,
     at the renamed key (the pointwise relations and the @('-covered-p')
     forms); in the failure direction, restricted to the free variables
     of the AST under evaluation, a lookup that fails on the original
     side fails at the renamed key (see @(tsee expr-denv-alpha-avoided-p)).
     The support invariant @(tsee expr-denv-keys-supported-p) ties the
     keys of the original environment to the fold's support set and the
     renamings' keys, which is what lets the freshness of a binder name
     exclude collisions with the renamings of other keys.  The
     preservation of these relations under the binder extensions, and
     under the restriction performed at closure creation, is proved here
     for the ispace, type, and expression layers.")
   (xdoc::p
    "The value layer: @(tsee expr-value-alpha-related-via-p) and
     @(tsee type-value-alpha-related-via-p) (and companions) relate the
     values of the two evaluations via explicit witnesses
     (@(tsee expr-value-witness), @(tsee type-value-witness)): each
     closure pair is related under its own renaming bundle, the one in
     scope where the value was created, and each entry of a captured
     environment carries its own witness in turn, because no relation
     under a single shared renaming is inductive (the review findings
     recorded in the design notes near the end of this book explain why).
     Ground values relate by equality (the leaf witnesses).  The closure
     cases carry the no-capture, freshness, key-bound, and
     failure-direction facts that the application step of the induction
     needs to evaluate the closure's body in its captured environment.
     Since an existential quantifier cannot appear inside a recursive
     clique, the witnesses are explicit arguments; the existential
     wrappers @('expr-value-alpha-equiv-p'),
     @('type-value-alpha-equiv-p'), and @('expr-denv-alpha-equiv-p')
     restore the quantified form for theorem statements.  This book also
     proves the consequences of the value relations that the induction
     uses (equal kinds and dimensions), the evaluation theorems for the
     structurally recursive levels --- dimensions, shapes, and ispaces
     evaluate identically under the relations (@('eval-dim-alpha'),
     @('eval-shape-alpha'), @('eval-ispace-alpha')), and types evaluate
     to witness-related type values (@('eval-type-alpha'), which
     constructs the witness) --- and the groundness collapse: on ground
     values the relation is equality
     (@('expr-value-alpha-related-via-p-when-groundp')), which turns the
     induction's conclusion into the literal equality of the main theorem
     (see @(see unique-names-validation)).")
   (xdoc::p
    "A first, shared-renaming version of the value relation was superseded
     by the witness-indexed one and has since been removed; the review
     findings that led to the witness design are in the design notes near
     the end of the book."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Extension of the renamings by binder correspondences.  These compute,
; from the two sides' binder names, the renamings in scope for the
; binder's body, mirroring exactly the extensions performed by the
; uniquification traversal (including the clearing of stale entries when
; a name is kept, via EXTEND-RENAMING).

(define extend-renaming-list ((names string-listp)
                              (new-names string-listp)
                              (renam string-string-mapp))
  :guard (equal (len names) (len new-names))
  :returns (new-renam string-string-mapp)
  :short "Extend a renaming map by a pointwise correspondence of names."
  (b* (((when (endp names)) (string-string-map-fix renam))
       (renam (extend-renaming (car names) (car new-names) renam)))
    (extend-renaming-list (cdr names) (cdr new-names) renam)))

(define type-var-list-alpha-extend ((new-vars type-var-listp)
                                    (vars type-var-listp)
                                    (atom-renam string-string-mapp)
                                    (array-renam string-string-mapp))
  :returns (mv (okp booleanp)
               (new-atom-renam string-string-mapp)
               (new-array-renam string-string-mapp))
  :short "Check that two type-variable parameter lists correspond in
          length and kinds, extending the atom-kind and array-kind
          renamings by the name correspondence."
  (b* ((atom-renam (string-string-map-fix atom-renam))
       (array-renam (string-string-map-fix array-renam))
       ((when (endp vars)) (mv (endp new-vars) atom-renam array-renam))
       ((when (endp new-vars)) (mv nil atom-renam array-renam))
       (var (car vars))
       (new-var (car new-vars)))
    (type-var-case
     var
     :atom (b* (((unless (type-var-case new-var :atom))
                 (mv nil atom-renam array-renam)))
             (type-var-list-alpha-extend
              (cdr new-vars) (cdr vars)
              (extend-renaming var.name (type-var-atom->name new-var)
                               atom-renam)
              array-renam))
     :array (b* (((unless (type-var-case new-var :array))
                  (mv nil atom-renam array-renam)))
              (type-var-list-alpha-extend
               (cdr new-vars) (cdr vars)
               atom-renam
               (extend-renaming var.name (type-var-array->name new-var)
                                array-renam))))))

(define ispace-var-list-alpha-extend ((new-vars ispace-var-listp)
                                      (vars ispace-var-listp)
                                      (dim-renam string-string-mapp)
                                      (shape-renam string-string-mapp))
  :returns (mv (okp booleanp)
               (new-dim-renam string-string-mapp)
               (new-shape-renam string-string-mapp))
  :short "Check that two ispace-variable parameter lists correspond in
          length and sorts, extending the dimension and shape renamings
          by the name correspondence."
  (b* ((dim-renam (string-string-map-fix dim-renam))
       (shape-renam (string-string-map-fix shape-renam))
       ((when (endp vars)) (mv (endp new-vars) dim-renam shape-renam))
       ((when (endp new-vars)) (mv nil dim-renam shape-renam))
       (var (car vars))
       (new-var (car new-vars)))
    (ispace-var-case
     var
     :dim (b* (((unless (ispace-var-case new-var :dim))
                (mv nil dim-renam shape-renam)))
            (ispace-var-list-alpha-extend
             (cdr new-vars) (cdr vars)
             (extend-renaming var.name (ispace-var-dim->name new-var)
                              dim-renam)
             shape-renam))
     :shape (b* (((unless (ispace-var-case new-var :shape))
                  (mv nil dim-renam shape-renam)))
              (ispace-var-list-alpha-extend
               (cdr new-vars) (cdr vars)
               dim-renam
               (extend-renaming var.name (ispace-var-shape->name new-var)
                                shape-renam))))))

(define bind-alpha-extended-renamings ((new-bind bindp)
                                       (bind bindp)
                                       (r var-renamings-p))
  :returns (new-r var-renamings-p)
  :short "The renamings in scope after a bind: the incoming ones extended
          by the correspondence between the bind's name on the two sides,
          in the namespace that the bind binds."
  :long
  (xdoc::topstring
   (xdoc::p
    "This mirrors the renaming extensions of @(tsee uniq-bind).  When the
     two binds have different kinds the result is irrelevant, since the
     relation below is then false anyway."))
  (b* (((var-renamings r-) r)
       (name (bind-name bind))
       (new-name (bind-name new-bind)))
    (bind-case
     bind
     :ispace (ispace-var-case
              bind.var
              :dim (change-var-renamings
                    r :dim (extend-renaming name new-name r-.dim))
              :shape (change-var-renamings
                      r :shape (extend-renaming name new-name r-.shape)))
     :type (type-var-case
            bind.var
            :atom (change-var-renamings
                   r :atom (extend-renaming name new-name r-.atom))
            :array (change-var-renamings
                    r :array (extend-renaming name new-name r-.array)))
     :otherwise (change-var-renamings
                 r :expr (extend-renaming name new-name r-.expr)))))

(define bind-list-alpha-extended-renamings ((new-binds bind-listp)
                                            (binds bind-listp)
                                            (r var-renamings-p))
  :returns (new-r var-renamings-p)
  :short "The renamings in scope after a list of binds."
  (b* (((when (endp binds)) (var-renamings-fix r))
       ((when (endp new-binds)) (var-renamings-fix r)))
    (bind-list-alpha-extended-renamings
     (cdr new-binds)
     (cdr binds)
     (bind-alpha-extended-renamings (car new-binds) (car binds) r))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Alpha-relatedness of ASTs modulo in-scope renamings: the left-hand AST
; is a candidate uniquification of the right-hand AST under the renamings.
; Free-variable occurrences and embedded types are the (deterministic)
; renamings of the originals; at each binder, the left-hand side may bind
; ANY names, and the bodies must be related under the renamings extended
; by the pointwise binder correspondence.  The traversal structure is
; exactly that of UNIQ-EXPR, minus the fresh-name policy.

(defines exprs-alpha-related-p
  :parents (uniquify-alpha-relations)
  :short "Alpha-relatedness of expressions, atoms, and bindings
          modulo in-scope renamings."
  :long
  (xdoc::topstring
   (xdoc::p
    "Free-variable occurrences and embedded types are the (deterministic)
     renamings of the originals; at each binder, the left-hand side may bind
     any names, and the bodies must be related under the renamings extended
     by the pointwise binder correspondence.
     The traversal structure is exactly that of @(tsee uniq-expr),
     minus the fresh-name policy."))
  :flag-local nil

  (define expr-alpha-related-p ((new-x exprp) (x exprp) (r var-renamings-p))
    :returns (yes/no booleanp)
    :parents (uniquify-alpha-relations)
    :short "Alpha-relatedness of expressions modulo in-scope renamings."
    :measure (expr-count x)
    (b* (((var-renamings r-) r))
      (expr-case
       x
       :var (and (expr-case new-x :var)
                 (equal (expr-var->name new-x)
                        (rename-var-string x.name r-.expr)))
       :atom (and (expr-case new-x :atom)
                  (atom-alpha-related-p (expr-atom->atom new-x) x.atom r))
       :array (and (expr-case new-x :array)
                   (equal (expr-array->dims new-x) x.dims)
                   (atom-list-alpha-related-p (expr-array->atoms new-x)
                                              x.atoms r))
       :array-empty (and (expr-case new-x :array-empty)
                         (equal (expr-array-empty->dims new-x) x.dims)
                         (equal (expr-array-empty->type new-x)
                                (type-rename-all-vars x.type r)))
       :frame (and (expr-case new-x :frame)
                   (equal (expr-frame->dims new-x) x.dims)
                   (expr-list-alpha-related-p (expr-frame->exprs new-x)
                                              x.exprs r))
       :frame-empty (and (expr-case new-x :frame-empty)
                         (equal (expr-frame-empty->dims new-x) x.dims)
                         (equal (expr-frame-empty->type new-x)
                                (type-rename-all-vars x.type r)))
       :string (and (expr-case new-x :string)
                    (equal (expr-string->chars new-x) x.chars))
       :app (and (expr-case new-x :app)
                 (expr-alpha-related-p (expr-app->fun new-x) x.fun r)
                 (expr-alpha-related-p (expr-app->arg new-x) x.arg r))
       :appn (and (expr-case new-x :appn)
                  (expr-alpha-related-p (expr-appn->fun new-x) x.fun r)
                  (expr-list-alpha-related-p (expr-appn->args new-x)
                                             x.args r))
       :tapp (and (expr-case new-x :tapp)
                  (expr-alpha-related-p (expr-tapp->fun new-x) x.fun r)
                  (equal (expr-tapp->arg new-x)
                         (type-rename-all-vars x.arg r)))
       :tappn (and (expr-case new-x :tappn)
                   (expr-alpha-related-p (expr-tappn->fun new-x) x.fun r)
                   (equal (expr-tappn->args new-x)
                          (type-list-rename-all-vars x.args r)))
       :iapp (and (expr-case new-x :iapp)
                  (expr-alpha-related-p (expr-iapp->fun new-x) x.fun r)
                  (equal (expr-iapp->arg new-x)
                         (ispace-rename-ispace-vars x.arg
                                                    r-.dim r-.shape)))
       :iappn (and (expr-case new-x :iappn)
                   (expr-alpha-related-p (expr-iappn->fun new-x) x.fun r)
                   (equal (expr-iappn->args new-x)
                          (ispace-list-rename-ispace-vars x.args
                                                          r-.dim r-.shape)))
       :capp (and (expr-case new-x :capp)
                  (expr-alpha-related-p (expr-capp->fun new-x) x.fun r)
                  (equal (expr-capp->targs new-x)
                         (type-list-option-rename-all-vars x.targs r))
                  (equal (expr-capp->iargs new-x)
                         (ispace-list-option-rename-ispace-vars
                          x.iargs r-.dim r-.shape))
                  (expr-list-alpha-related-p (expr-capp->args new-x)
                                             x.args r))
       :unbox
       ;; The single ispace variable goes through the same extension
       ;; helper as :unboxn, on a singleton list, mirroring UNIQ-EXPR's
       ;; singleton-list use of UNIQ-ISPACE-VAR-PARAMS.
       (b* (((unless (expr-case new-x :unbox)) nil)
            ((expr-unbox u) new-x)
            ((mv okp dim-renam shape-renam)
             (ispace-var-list-alpha-extend (list u.ispace) (list x.ispace)
                                           r-.dim r-.shape))
            ((unless okp) nil)
            (body-r (change-var-renamings
                     r
                     :dim dim-renam
                     :shape shape-renam
                     :expr (extend-renaming x.var u.var r-.expr))))
         (and (expr-alpha-related-p u.target x.target r)
              (equal u.type? (type-option-rename-all-vars x.type? r))
              (expr-alpha-related-p u.body x.body body-r)))
       :unboxn
       (b* (((unless (expr-case new-x :unboxn)) nil)
            ((expr-unboxn u) new-x)
            ((mv okp dim-renam shape-renam)
             (ispace-var-list-alpha-extend u.ispaces x.ispaces
                                           r-.dim r-.shape))
            ((unless okp) nil)
            (body-r (change-var-renamings
                     r
                     :dim dim-renam
                     :shape shape-renam
                     :expr (extend-renaming x.var u.var r-.expr))))
         (and (expr-alpha-related-p u.target x.target r)
              (equal u.type? (type-option-rename-all-vars x.type? r))
              (expr-alpha-related-p u.body x.body body-r)))
       :bracket (and (expr-case new-x :bracket)
                     (expr-list-alpha-related-p (expr-bracket->exprs new-x)
                                                x.exprs r))
       :let
       (b* (((unless (expr-case new-x :let)) nil)
            ((expr-let u) new-x))
         (and (bind-list-alpha-related-p u.binds x.binds r)
              (expr-alpha-related-p
               u.body x.body
               (bind-list-alpha-extended-renamings u.binds x.binds r)))))))

  (define expr-list-alpha-related-p ((new-x expr-listp)
                                     (x expr-listp)
                                     (r var-renamings-p))
    :returns (yes/no booleanp)
    :parents (uniquify-alpha-relations exprs-alpha-related-p)
    :short "Alpha-relatedness of lists of expressions."
    :measure (expr-list-count x)
    (if (endp x)
        (endp new-x)
      (and (consp new-x)
           (expr-alpha-related-p (car new-x) (car x) r)
           (expr-list-alpha-related-p (cdr new-x) (cdr x) r))))

  (define atom-alpha-related-p ((new-a atomp) (a atomp) (r var-renamings-p))
    :returns (yes/no booleanp)
    :parents (uniquify-alpha-relations exprs-alpha-related-p)
    :short "Alpha-relatedness of atoms."
    :measure (atom-count a)
    (b* (((var-renamings r-) r))
      (atom-case
       a
       :base (and (atom-case new-a :base)
                  (equal (atom-base->lit new-a) a.lit))
       :lambda
       ;; The single parameter's name is arbitrary; its optional type
       ;; and the body annotation are the renamings of the originals,
       ;; mirroring UNIQ-ATOM's :lambda case.
       (b* (((unless (atom-case new-a :lambda)) nil)
            ((atom-lambda u) new-a))
         (and (equal (var+type?->type? u.param)
                     (type-option-rename-all-vars (var+type?->type? a.param)
                                                  r))
              (equal u.type? (type-option-rename-all-vars a.type? r))
              (expr-alpha-related-p
               u.body a.body
               (change-var-renamings
                r :expr (extend-renaming
                         (var+type?->var a.param)
                         (var+type?->var u.param)
                         r-.expr)))))
       :lambdan
       (b* (((unless (atom-case new-a :lambdan)) nil)
            ((atom-lambdan u) new-a))
         (and (equal (len u.params) (len a.params))
              (equal u.params
                     (var+type?-list-set-vars
                      (var+type?-list->var u.params)
                      (var+type?-list-rename-all-vars a.params r)))
              (equal u.type? (type-option-rename-all-vars a.type? r))
              (expr-alpha-related-p
               u.body a.body
               (change-var-renamings
                r :expr (extend-renaming-list
                         (var+type?-list->var a.params)
                         (var+type?-list->var u.params)
                         r-.expr)))))
       :tlambda
       (b* (((unless (atom-case new-a :tlambda)) nil)
            ((atom-tlambda u) new-a)
            ((mv okp atom-renam array-renam)
             (type-var-list-alpha-extend (list u.param) (list a.param)
                                         r-.atom r-.array))
            ((unless okp) nil))
         (expr-alpha-related-p u.body a.body
                               (change-var-renamings r
                                                     :atom atom-renam
                                                     :array array-renam)))
       :tlambdan
       (b* (((unless (atom-case new-a :tlambdan)) nil)
            ((atom-tlambdan u) new-a)
            ((mv okp atom-renam array-renam)
             (type-var-list-alpha-extend u.params a.params
                                         r-.atom r-.array))
            ((unless okp) nil))
         (expr-alpha-related-p u.body a.body
                               (change-var-renamings r
                                                     :atom atom-renam
                                                     :array array-renam)))
       :ilambda
       (b* (((unless (atom-case new-a :ilambda)) nil)
            ((atom-ilambda u) new-a)
            ((mv okp dim-renam shape-renam)
             (ispace-var-list-alpha-extend (list u.param) (list a.param)
                                           r-.dim r-.shape))
            ((unless okp) nil))
         (expr-alpha-related-p u.body a.body
                               (change-var-renamings r
                                                     :dim dim-renam
                                                     :shape shape-renam)))
       :ilambdan
       (b* (((unless (atom-case new-a :ilambdan)) nil)
            ((atom-ilambdan u) new-a)
            ((mv okp dim-renam shape-renam)
             (ispace-var-list-alpha-extend u.params a.params
                                           r-.dim r-.shape))
            ((unless okp) nil))
         (expr-alpha-related-p u.body a.body
                               (change-var-renamings r
                                                     :dim dim-renam
                                                     :shape shape-renam)))
       :box (and (atom-case new-a :box)
                 (equal (atom-box->ispace new-a)
                        (ispace-rename-ispace-vars a.ispace
                                                   r-.dim r-.shape))
                 (expr-alpha-related-p (atom-box->array new-a) a.array r)
                 (equal (atom-box->type? new-a)
                        (type-option-rename-all-vars a.type? r)))
       :boxn (and (atom-case new-a :boxn)
                  (equal (atom-boxn->ispaces new-a)
                         (ispace-list-rename-ispace-vars a.ispaces
                                                         r-.dim r-.shape))
                  (expr-alpha-related-p (atom-boxn->array new-a) a.array r)
                  (equal (atom-boxn->type? new-a)
                         (type-option-rename-all-vars a.type? r))))))

  (define atom-list-alpha-related-p ((new-a atom-listp)
                                     (a atom-listp)
                                     (r var-renamings-p))
    :returns (yes/no booleanp)
    :parents (uniquify-alpha-relations exprs-alpha-related-p)
    :short "Alpha-relatedness of lists of atoms."
    :measure (atom-list-count a)
    (if (endp a)
        (endp new-a)
      (and (consp new-a)
           (atom-alpha-related-p (car new-a) (car a) r)
           (atom-list-alpha-related-p (cdr new-a) (cdr a) r))))

  (define bind-alpha-related-p ((new-b bindp) (b bindp) (r var-renamings-p))
    :returns (yes/no booleanp)
    :parents (uniquify-alpha-relations exprs-alpha-related-p)
    :short "Alpha-relatedness of binds.  The bound name on the left-hand
            side is arbitrary (it feeds the extension of the renamings,
            see @(tsee bind-alpha-extended-renamings)); the components
            are related under the incoming renamings, since a bind's name
            is not in scope in its own definition."
    :measure (bind-count b)
    (b* (((var-renamings r-) r))
      (bind-case
       b
       :ispace (and (bind-case new-b :ispace)
                    (equal (ispace-var-kind (bind-ispace->var new-b))
                           (ispace-var-kind b.var))
                    (equal (bind-ispace->ispace new-b)
                           (ispace-rename-ispace-vars b.ispace
                                                      r-.dim r-.shape)))
       :type (and (bind-case new-b :type)
                  (equal (type-var-kind (bind-type->var new-b))
                         (type-var-kind b.var))
                  (equal (bind-type->type new-b)
                         (type-rename-all-vars b.type r)))
       :val (and (bind-case new-b :val)
                 (equal (bind-val->type? new-b)
                        (type-option-rename-all-vars b.type? r))
                 (expr-alpha-related-p (bind-val->expr new-b) b.expr r))
       :fun
       (b* (((unless (bind-case new-b :fun)) nil)
            ((bind-fun u) new-b))
         (and (equal (len u.params) (len b.params))
              (equal u.params
                     (var+type?-list-set-vars
                      (var+type?-list->var u.params)
                      (var+type?-list-rename-all-vars b.params r)))
              (equal u.type? (type-option-rename-all-vars b.type? r))
              (expr-alpha-related-p
               u.expr b.expr
               (change-var-renamings
                r :expr (extend-renaming-list
                         (var+type?-list->var b.params)
                         (var+type?-list->var u.params)
                         r-.expr)))))
       :tfun
       (b* (((unless (bind-case new-b :tfun)) nil)
            ((bind-tfun u) new-b)
            ((mv okp atom-renam array-renam)
             (type-var-list-alpha-extend u.params b.params
                                         r-.atom r-.array))
            ((unless okp) nil)
            (inner-r (change-var-renamings r
                                           :atom atom-renam
                                           :array array-renam)))
         (and (equal u.type? (type-option-rename-all-vars b.type? inner-r))
              (expr-alpha-related-p u.expr b.expr inner-r)))
       :ifun
       (b* (((unless (bind-case new-b :ifun)) nil)
            ((bind-ifun u) new-b)
            ((mv okp dim-renam shape-renam)
             (ispace-var-list-alpha-extend u.params b.params
                                           r-.dim r-.shape))
            ((unless okp) nil)
            (inner-r (change-var-renamings r
                                           :dim dim-renam
                                           :shape shape-renam)))
         (and (equal u.type? (type-option-rename-all-vars b.type? inner-r))
              (expr-alpha-related-p u.expr b.expr inner-r)))
       :cfun
       (b* (((unless (bind-case new-b :cfun)) nil)
            ((bind-cfun u) new-b)
            (tparams (type-var-list-option-case b.tparams?
                                                :some b.tparams?.val
                                                :none nil))
            (new-tparams (type-var-list-option-case u.tparams?
                                                    :some u.tparams?.val
                                                    :none nil))
            ((unless (equal (type-var-list-option-case u.tparams? :some)
                            (type-var-list-option-case b.tparams? :some)))
             nil)
            (iparams (ispace-var-list-option-case b.iparams?
                                                  :some b.iparams?.val
                                                  :none nil))
            (new-iparams (ispace-var-list-option-case u.iparams?
                                                      :some u.iparams?.val
                                                      :none nil))
            ((unless (equal (ispace-var-list-option-case u.iparams? :some)
                            (ispace-var-list-option-case b.iparams? :some)))
             nil)
            ((mv okp1 atom-renam array-renam)
             (type-var-list-alpha-extend new-tparams tparams
                                         r-.atom r-.array))
            ((unless okp1) nil)
            ((mv okp2 dim-renam shape-renam)
             (ispace-var-list-alpha-extend new-iparams iparams
                                           r-.dim r-.shape))
            ((unless okp2) nil)
            (inner-r (change-var-renamings r
                                           :dim dim-renam
                                           :shape shape-renam
                                           :atom atom-renam
                                           :array array-renam))
            ((var-renamings inner-r-) inner-r))
         (and (equal (len u.params) (len b.params))
              (equal u.params
                     (var+type?-list-set-vars
                      (var+type?-list->var u.params)
                      (var+type?-list-rename-all-vars b.params inner-r)))
              (equal u.type (type-rename-all-vars b.type inner-r))
              (expr-alpha-related-p
               u.expr b.expr
               (change-var-renamings
                inner-r
                :expr (extend-renaming-list
                       (var+type?-list->var b.params)
                       (var+type?-list->var u.params)
                       inner-r-.expr))))))))

  (define bind-list-alpha-related-p ((new-b bind-listp)
                                     (b bind-listp)
                                     (r var-renamings-p))
    :returns (yes/no booleanp)
    :parents (uniquify-alpha-relations exprs-alpha-related-p)
    :short "Alpha-relatedness of lists of binds, threading the extended
            renamings through the sequential scopes."
    :measure (bind-list-count b)
    (if (endp b)
        (endp new-b)
      (and (consp new-b)
           (bind-alpha-related-p (car new-b) (car b) r)
           (bind-list-alpha-related-p
            (cdr new-b) (cdr b)
            (bind-alpha-extended-renamings (car new-b) (car b) r)))))

  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Fixing congruences for the AST-level relations and their helpers.
;
; The AST relation clique and the extension helpers touch no defun-sk
; relation, so their congruences are unproblematic; they are needed by the
; bridge theorem below (the relation is applied there to accessors of
; constructed nodes, whose accessor theorems introduce fixes).  The
; congruences for EXTEND-RENAMING (defined in unique-names.lisp) are added
; here rather than there to avoid recertifying that book's dependents.

(fty::deffixequiv extend-renaming
  :hints (("Goal" :in-theory (enable extend-renaming))))

(fty::deffixequiv extend-renaming-list
  :hints (("Goal"
           :induct t
           :in-theory (enable extend-renaming-list))))

(fty::deffixequiv type-var-list-alpha-extend
  :hints (("Goal"
           :induct t
           :in-theory (enable type-var-list-alpha-extend))))

(fty::deffixequiv ispace-var-list-alpha-extend
  :hints (("Goal"
           :induct t
           :in-theory (enable ispace-var-list-alpha-extend))))

(fty::deffixequiv bind-alpha-extended-renamings
  :hints (("Goal" :in-theory (enable bind-alpha-extended-renamings
                                     bind-name))))

(fty::deffixequiv bind-list-alpha-extended-renamings
  :hints (("Goal"
           :induct t
           :in-theory (enable bind-list-alpha-extended-renamings))))

; The composed renaming wrappers of unique-names.lisp, which the AST
; relation calls on embedded types, likewise get their congruences here.

(fty::deffixequiv-mutual exprs-alpha-related-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Support lemmas for the bridge theorem below: the uniquification
; traversal's parameter helpers line up with the *-ALPHA-EXTEND functions.
;
; The three UNIQ-*-PARAMS functions extend the renamings exactly as the
; corresponding *-ALPHA-EXTEND functions recompute them from the name
; correspondence.  For the expression-variable parameters this is stated
; as two normalization rules that rewrite the NEW-PARAMS and NEW-RENAM
; results of UNIQ-EXPR-PARAMS into UNIQ-NAME-LIST-based forms, in the same
; direction as the UNIQ-EXPR-PARAMS-TO-UNIQ-NAME-LIST bridge of
; unique-names.lisp, so that the two rule sets compose instead of racing.

; Variable-name preservation and length facts.

(defruled len-of-uniq-expr-params-new-params
  (equal (len (mv-nth 1 (uniq-expr-params params used avoid renam)))
         (len params))
  :induct (uniq-expr-params params used avoid renam)
  :enable (uniq-expr-params len))

; Base cases of the parameter helpers, normalized so that the fixes they
; return are absorbed by the constructors of the callers.

(defruled uniq-name-list-when-endp
  (implies (not (consp names))
           (equal (uniq-name-list names used avoid)
                  (mv (string-list-fix used) nil)))
  :enable uniq-name-list)

(defruled uniq-type-var-params-when-endp
  (implies (not (consp params))
           (equal (uniq-type-var-params params used avoid atom-renam array-renam)
                  (mv (string-list-fix used) nil
                      (string-string-map-fix atom-renam)
                      (string-string-map-fix array-renam))))
  :enable uniq-type-var-params)

(defruled uniq-ispace-var-params-when-endp
  (implies (not (consp params))
           (equal (uniq-ispace-var-params params used avoid dim-renam shape-renam)
                  (mv (string-list-fix used) nil
                      (string-string-map-fix dim-renam)
                      (string-string-map-fix shape-renam))))
  :enable uniq-ispace-var-params)

; UNIQ-BIND preserves the kind of its bind (immediate per case; no
; induction), so the relation and extension functions below dispatch on a
; known kind in the bind-list case of the bridge proof.

(defruled bind-kind-of-uniq-bind
  (equal (bind-kind (mv-nth 1 (uniq-bind x used r)))
         (bind-kind x))
  :expand ((uniq-bind x used r)))

; The UNIQ-EXPR-PARAMS normalization rules.

(defruled uniq-expr-params-new-params-to-uniq-name-list
  (equal (mv-nth 1 (uniq-expr-params params used avoid renam))
         (var+type?-list-set-vars
          (mv-nth 1 (uniq-name-list (var+type?-list->var params) used avoid))
          params))
  :induct (uniq-expr-params params used avoid renam)
  :enable (uniq-expr-params
           uniq-name-list
           var+type?-list-set-vars
           var+type?-list->var))

(defruled uniq-expr-params-new-renam-to-extend-renaming-list
  (equal (mv-nth 2 (uniq-expr-params params used avoid renam))
         (extend-renaming-list
          (var+type?-list->var params)
          (mv-nth 1 (uniq-name-list (var+type?-list->var params) used avoid))
          renam))
  :induct (uniq-expr-params params used avoid renam)
  :enable (uniq-expr-params
           uniq-name-list
           extend-renaming-list
           var+type?-list->var))

; The type-variable and ispace-variable parameter helpers agree with the
; corresponding *-ALPHA-EXTEND recomputations, with the OKP flag true.

(defruled type-var-list-alpha-extend-of-uniq-type-var-params
  (b* (((mv & new-params new-atom new-array)
        (uniq-type-var-params params used avoid atom-renam array-renam)))
    (equal (type-var-list-alpha-extend new-params params
                                       atom-renam array-renam)
           (mv t new-atom new-array)))
  :induct (uniq-type-var-params params used avoid atom-renam array-renam)
  :enable (uniq-type-var-params
           type-var-list-alpha-extend
           type-var->name
           extend-renaming))

(defruled ispace-var-list-alpha-extend-of-uniq-ispace-var-params
  (b* (((mv & new-params new-dim new-shape)
        (uniq-ispace-var-params params used avoid dim-renam shape-renam)))
    (equal (ispace-var-list-alpha-extend new-params params
                                         dim-renam shape-renam)
           (mv t new-dim new-shape)))
  :induct (uniq-ispace-var-params params used avoid dim-renam shape-renam)
  :enable (uniq-ispace-var-params
           ispace-var-list-alpha-extend
           ispace-var->name
           extend-renaming))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The :APPN requirement, in the CONSP-of-CDR form the goals arise in.
; UNIQUE-NAMES proves the two-or-more-ness of the rebuilt argument list as
; the linear rule LEN->=-2-OF-UNIQ-EXPR-LIST, which does not apply to a
; goal about (CONSP (CDR ...)); the sibling cases need no such bridge
; because their argument lists are rebuilt by DEFFOLD-MAP renamings, whose
; length theorems are equalities.

(defruled consp-of-cdr-of-uniq-expr-list
  (implies (consp (cdr x))
           (consp (cdr (mv-nth 1 (uniq-expr-list x used r)))))
  :use len->=-2-of-uniq-expr-list
  :enable (len
           len->=-2-when-consp-of-cdr
           positive-len-when-consp
           consp-when-positive-len))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The bridge theorem: the output of the uniquification traversal is
; alpha-related to its input under the renamings in force, and the
; renamings that UNIQ-BIND(-LIST) return are exactly the alpha extensions
; recomputed from the two sides' binder names.  Hypothesis-free: the
; relation was designed to have exactly the traversal's structure, minus
; the fresh-name policy.

(defret-mutual uniq-alpha-bridge
  (defret expr-alpha-related-p-of-uniq-expr
    (expr-alpha-related-p new-x x r)
    :fn uniq-expr)
  (defret expr-list-alpha-related-p-of-uniq-expr-list
    (expr-list-alpha-related-p new-x x r)
    :fn uniq-expr-list)
  (defret atom-alpha-related-p-of-uniq-atom
    (atom-alpha-related-p new-x x r)
    :fn uniq-atom)
  (defret atom-list-alpha-related-p-of-uniq-atom-list
    (atom-list-alpha-related-p new-x x r)
    :fn uniq-atom-list)
  (defret bind-alpha-related-p-of-uniq-bind
    (and (bind-alpha-related-p new-x x r)
         (equal new-r (bind-alpha-extended-renamings new-x x r)))
    :fn uniq-bind)
  (defret bind-list-alpha-related-p-of-uniq-bind-list
    (and (bind-list-alpha-related-p new-x x r)
         (equal new-r (bind-list-alpha-extended-renamings new-x x r)))
    :fn uniq-bind-list)
  :mutual-recursion uniquify-names-impl
  ;; The traversal and relation definitions are opened only at the
  ;; top-level call of each induction subgoal, as in the proofs of
  ;; unique-names.lisp; BIND-ALPHA-EXTENDED-RENAMINGS additionally opens
  ;; only against the known-kind bind X, never against the unknown-kind
  ;; result of an inner UNIQ-BIND, which BIND-KIND-OF-UNIQ-BIND and the
  ;; closed IH equation handle instead.
  :hints
  (("Goal"
    :expand ((uniq-expr x used r)
             (uniq-expr-list x used r)
             (uniq-atom x used r)
             (uniq-atom-list x used r)
             (uniq-bind x used r)
             (uniq-bind-list x used r)
             (:free (new-x) (expr-alpha-related-p new-x x r))
             (:free (new-x) (expr-list-alpha-related-p new-x x r))
             (:free (new-x) (atom-alpha-related-p new-x x r))
             (:free (new-x) (atom-list-alpha-related-p new-x x r))
             (:free (new-x) (bind-alpha-related-p new-x x r))
             (:free (new-x) (bind-list-alpha-related-p new-x x r))
             (:free (new-x) (bind-alpha-extended-renamings new-x x r)))
    :in-theory (e/d (bind-list-alpha-extended-renamings
                     bind-kind-of-uniq-bind
                     bind-name
                     type-var->name
                     ispace-var->name
                     type-var-list-alpha-extend
                     ispace-var-list-alpha-extend
                     uniq-expr-params-new-params-to-uniq-name-list
                     uniq-expr-params-new-renam-to-extend-renaming-list
                     type-var-list-alpha-extend-of-uniq-type-var-params
                     ispace-var-list-alpha-extend-of-uniq-ispace-var-params
                     uniq-ispace-var-params-when-endp
                     uniq-type-var-params-when-endp
                     uniq-name-list-when-endp
                     var+type?-list->var-of-var+type?-list-rename-all-vars
                     var+type?-list->var-of-var+type?-list-set-vars
                     len-of-uniq-expr-params-new-params
                     len-of-uniq-name-list-new-names
                     len-of-var+type?-list-set-vars
                     len-of-var+type?-list-rename-all-vars
                     list-of-car-when-len-1
                     len
                     len-of-uniq-ispace-var-params
                     ; The n-ary application, binder, and boxing cases
                     ; need the two-or-more-ness of their rebuilt argument
                     ; and parameter lists, each following from the
                     ; respective product's -REQUIREMENTS theorem through a
                     ; length-preservation rule.  This mirrors the hint of
                     ; VERIFY-GUARDS UNIQ-EXPR in UNIQUE-NAMES.
                     acl2::lt-len-const
                     len->=-2-of-uniq-expr-list
                     consp-of-cdr-of-uniq-expr-list
                     len-of-type-list-rename-all-vars
                     len-of-ispace-list-rename-ispace-vars
                     consp-of-cdr-of-expr-appn->args
                     consp-of-cdr-of-expr-tappn->args
                     consp-of-cdr-of-expr-iappn->args
                     consp-of-cdr-of-expr-unboxn->ispaces
                     consp-of-cdr-of-atom-lambdan->params
                     consp-of-cdr-of-atom-tlambdan->params
                     consp-of-cdr-of-atom-ilambdan->params
                     consp-of-cdr-of-atom-boxn->ispaces)
                    (uniq-expr uniq-expr-list uniq-atom
                     uniq-atom-list uniq-bind uniq-bind-list
                     expr-alpha-related-p expr-list-alpha-related-p
                     atom-alpha-related-p atom-list-alpha-related-p
                     bind-alpha-related-p bind-list-alpha-related-p
                     bind-alpha-extended-renamings)))))

; Corollary at the top level: the output of EXPR-UNIQUIFY-NAMES is
; alpha-related to its input under the initial renaming bundle (all five
; maps empty; the AVOID component is irrelevant to the relation but is
; part of the bundle that the traversal receives).

(defrule expr-alpha-related-p-of-expr-uniquify-names
  (expr-alpha-related-p (expr-uniquify-names expr)
                        expr
                        (make-var-renamings :dim nil
                                            :shape nil
                                            :atom nil
                                            :array nil
                                            :expr nil
                                            :avoid (expr-all-var-names expr)))
  :enable expr-uniquify-names
  :disable expr-alpha-related-p-of-uniq-expr
  :use ((:instance expr-alpha-related-p-of-uniq-expr
                   (x (expr-fix expr))
                   (used (set::union (expr-free-var-names expr) (primop-names)))
                   (r (make-var-renamings :dim nil
                                          :shape nil
                                          :atom nil
                                          :array nil
                                          :expr nil
                                          :avoid (expr-all-var-names expr))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rename-var-string-set ((names string-setp) (renam string-string-mapp))
  :returns (new-names string-setp)
  :short "Image of a set of expression-variable names under a renaming map."
  (b* (((when (set::emptyp (string-sfix names))) nil))
    (set::insert (rename-var-string (set::head names) renam)
                 (rename-var-string-set (set::tail names) renam)))
  :prepwork ((local (in-theory (enable acl2::emptyp-of-string-sfix))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Freshness companion to the AST alpha-relatedness relation.
;
; The relation EXPRS-ALPHA-RELATED-P allows the left-hand side to bind
; ANY names.  The main evaluation induction additionally needs, at each
; binder, the hypotheses of the environment-extension lemmas: the new
; name must not collide with the keys of the (new-side) environments,
; with the keys of the in-scope renaming map of its namespace, or with
; the values of that map reduced at the old name; and for the binders
; that build closures, the new name must not capture a renamed free
; variable of the body (the conjunct that the value relation carries at
; closure nodes).  This fold mirrors the relation's traversal and
; asserts exactly those conditions.
;
; The environment keys are covered through the support set B: the
; invariant tying the fold to evaluation is keys(new environments) <= B.
; At non-closure binders (unbox, let binds) the new name joins B for the
; body; at closure binders the environment is restricted to the renamed
; free variables of the body at application time, so B is REPLACED by
; the name strings of those renamed free-variable sets (plus the new
; parameters, which join through the renamings).
;
; A kept name (new name = old name) needs no B or key condition: the
; corresponding environment extension is a same-key shadowing update on
; both sides, sound under the values condition alone (the shadow
; variants of the extension lemmas).
;
; Embedded types are renamed deterministically, so at each embedded
; type position the fold asserts the no-capture conditions that
; EVAL-TYPE-ALPHA takes as hypotheses, under the renamings in scope at
; that position.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Freshness of one binder-name correspondence against one namespace's
; renaming map and the support set.

(define name-fresh-ok ((name stringp) (new-name stringp)
                       (m string-string-mapp) (b string-setp))
  :returns (yes/no booleanp)
  :short "Freshness conditions for one binder name in one namespace."
  (b* ((name (str-fix name))
       (new-name (str-fix new-name))
       (m (string-string-map-fix m)))
    (and (implies (not (equal new-name name))
                  (and (not (set::in new-name (string-sfix b)))
                       (not (omap::assoc new-name m))))
         (not (set::in new-name (omap::values (omap::delete name m)))))))

(define string-list-fresh-ok ((names string-listp)
                              (new-names string-listp)
                              (m string-string-mapp)
                              (b string-setp))
  :returns (yes/no booleanp)
  :short "Sequential freshness of a list of binder-name correspondences
          in one namespace, threading the map extensions and growing the
          support set as @(tsee extend-renaming-list) threads the map."
  (b* (((when (endp names)) t)
       ((when (endp new-names)) t)
       (name (car names))
       (new-name (car new-names)))
    (and (name-fresh-ok name new-name m b)
         (string-list-fresh-ok (cdr names) (cdr new-names)
                               (extend-renaming name new-name m)
                               (set::insert (str-fix new-name)
                                            (string-sfix b))))))

(define type-var-list-fresh-ok ((new-vars type-var-listp)
                                (vars type-var-listp)
                                (atom-renam string-string-mapp)
                                (array-renam string-string-mapp)
                                (b string-setp))
  :returns (yes/no booleanp)
  :short "Sequential freshness of a type-variable parameter
          correspondence, mirroring @(tsee type-var-list-alpha-extend)."
  (b* (((when (endp vars)) t)
       ((when (endp new-vars)) t)
       (var (car vars))
       (new-var (car new-vars)))
    (type-var-case
     var
     :atom (b* (((unless (type-var-case new-var :atom)) t))
             (and (name-fresh-ok var.name (type-var-atom->name new-var)
                                 atom-renam b)
                  (type-var-list-fresh-ok
                   (cdr new-vars) (cdr vars)
                   (extend-renaming var.name (type-var-atom->name new-var)
                                    atom-renam)
                   array-renam
                   (set::insert (type-var-atom->name new-var)
                                (string-sfix b)))))
     :array (b* (((unless (type-var-case new-var :array)) t))
              (and (name-fresh-ok var.name (type-var-array->name new-var)
                                  array-renam b)
                   (type-var-list-fresh-ok
                    (cdr new-vars) (cdr vars)
                    atom-renam
                    (extend-renaming var.name (type-var-array->name new-var)
                                     array-renam)
                    (set::insert (type-var-array->name new-var)
                                 (string-sfix b))))))))

(define ispace-var-list-fresh-ok ((new-vars ispace-var-listp)
                                  (vars ispace-var-listp)
                                  (dim-renam string-string-mapp)
                                  (shape-renam string-string-mapp)
                                  (b string-setp))
  :returns (yes/no booleanp)
  :short "Sequential freshness of an ispace-variable parameter
          correspondence, mirroring @(tsee ispace-var-list-alpha-extend)."
  (b* (((when (endp vars)) t)
       ((when (endp new-vars)) t)
       (var (car vars))
       (new-var (car new-vars)))
    (ispace-var-case
     var
     :dim (b* (((unless (ispace-var-case new-var :dim)) t))
            (and (name-fresh-ok var.name (ispace-var-dim->name new-var)
                                dim-renam b)
                 (ispace-var-list-fresh-ok
                  (cdr new-vars) (cdr vars)
                  (extend-renaming var.name (ispace-var-dim->name new-var)
                                   dim-renam)
                  shape-renam
                  (set::insert (ispace-var-dim->name new-var)
                               (string-sfix b)))))
     :shape (b* (((unless (ispace-var-case new-var :shape)) t))
              (and (name-fresh-ok var.name (ispace-var-shape->name new-var)
                                  shape-renam b)
                   (ispace-var-list-fresh-ok
                    (cdr new-vars) (cdr vars)
                    dim-renam
                    (extend-renaming var.name
                                     (ispace-var-shape->name new-var)
                                     shape-renam)
                    (set::insert (ispace-var-shape->name new-var)
                                 (string-sfix b))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; No-capture of the deterministic renaming of embedded types, in the
; form that EVAL-TYPE-ALPHA takes as hypotheses.

(define type-fresh-ok ((ty typep) (r var-renamings-p))
  :returns (yes/no booleanp)
  :short "No-capture of the deterministic renaming of an embedded type."
  (b* (((var-renamings r-) r))
    (and (type-rename-ispace-vars-no-capture-p ty r-.dim r-.shape)
         (type-rename-type-vars-no-capture-p
          (type-rename-ispace-vars ty r-.dim r-.shape)
          r-.atom r-.array))))

(define type-option-fresh-ok ((ty? type-optionp) (r var-renamings-p))
  :returns (yes/no booleanp)
  :short "No-capture of the deterministic renaming of an optional type."
  (type-option-case
   ty?
   :none t
   :some (type-fresh-ok ty?.val r)))

(define type-list-fresh-ok ((tys type-listp) (r var-renamings-p))
  :returns (yes/no booleanp)
  :short "No-capture of the deterministic renaming of a list of types."
  (or (endp tys)
      (and (type-fresh-ok (car tys) r)
           (type-list-fresh-ok (cdr tys) r))))

(define type-list-option-fresh-ok ((tys? type-list-optionp)
                                   (r var-renamings-p))
  :returns (yes/no booleanp)
  :short "No-capture of the deterministic renaming of an optional list
          of types."
  (type-list-option-case
   tys?
   :none t
   :some (type-list-fresh-ok tys?.val r)))

(define var+type?-list-types-fresh-ok ((params var+type?-listp)
                                       (r var-renamings-p))
  :returns (yes/no booleanp)
  :short "No-capture of the deterministic renaming of the type
          annotations of a parameter list."
  (or (endp params)
      (and (type-option-fresh-ok (var+type?->type? (car params)) r)
           (var+type?-list-types-fresh-ok (cdr params) r))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The support set for the body of a closure: at application time the
; closure's environment is its creation-time environment restricted to
; the (renamed) free variables of the body, extended with the (new)
; parameters; the parameters enter through the extended renamings, so
; the renamed free-variable sets under the body renamings cover both.

(define expr-body-support-names ((body exprp) (r var-renamings-p))
  :returns (names string-setp)
  :short "Support-set bound for the environments in which the body of a
          closure is evaluated: name strings of the renamed free
          variables of the body, in all namespaces, under the body's
          renamings."
  (b* (((var-renamings r-) r))
    (set::union
     (ispace-var-set-names
      (ispace-var-set-rename-ispace-vars (expr-free-ispace-vars body)
                                         r-.dim r-.shape))
     (set::union
      (type-var-set-names
       (type-var-set-rename-type-vars (expr-free-type-vars body)
                                      r-.atom r-.array))
      (rename-var-string-set (expr-free-expr-vars body) r-.expr))))
  ;; The callees are not guard-verified uniformly, so this stays in
  ;; :logic mode without guard verification.
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; No-capture of one let bind's new name against the renamed free
; variables of its scope (the rest of the let), in the bind's namespace.
; The variable sets passed in are the scope's free variables per
; namespace; the caller threads deletions and renaming extensions.

(define bind-nocapture-ok ((new-b bindp) (b bindp)
                           (r var-renamings-p)
                           (evars string-setp)
                           (tvars type-var-setp)
                           (ivars ispace-var-setp))
  :returns (yes/no booleanp)
  :short "No-capture of a bind's new name against the renamed free
          variables of its scope."
  :verify-guards nil
  (b* (((var-renamings r-) r))
    (bind-case
     b
     :ispace (b* (((unless (bind-case new-b :ispace)) t))
               (not (set::in (bind-ispace->var new-b)
                             (ispace-var-set-rename-ispace-vars
                              (set::delete b.var
                                           (ispace-var-set-fix ivars))
                              r-.dim r-.shape))))
     :type (b* (((unless (bind-case new-b :type)) t))
             (not (set::in (bind-type->var new-b)
                           (type-var-set-rename-type-vars
                            (set::delete b.var (type-var-set-fix tvars))
                            r-.atom r-.array))))
     :otherwise (not (set::in (str-fix (bind-name new-b))
                              (rename-var-string-set
                               (set::delete (str-fix (bind-name b))
                                            (string-sfix evars))
                               r-.expr))))))

(define bind-list-body-scope-fresh-ok ((new-binds bind-listp)
                                       (binds bind-listp)
                                       (r var-renamings-p)
                                       (evars string-setp)
                                       (tvars type-var-setp)
                                       (ivars ispace-var-setp))
  :returns (yes/no booleanp)
  :short "No-capture of each let bind's new name against the renamed
          free variables of the let body, threading the renaming
          extensions through the sequential scopes.  The variable sets
          are NOT reduced as the binds are traversed: each bind's new
          name must avoid the image of the whole body scope (minus that
          bind's own name), which is what the inductive step of the
          scope lemma consumes."
  :verify-guards nil
  (b* (((when (endp binds)) t)
       ((unless (consp new-binds)) t))
    (and (bind-nocapture-ok (car new-binds) (car binds) r
                            evars tvars ivars)
         (bind-list-body-scope-fresh-ok
          (cdr new-binds) (cdr binds)
          (bind-alpha-extended-renamings (car new-binds) (car binds) r)
          evars tvars ivars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Fixing congruences for the helpers, needed by the fold's own mutual
; congruence proof below.

(fty::deffixequiv name-fresh-ok
  :hints (("Goal" :in-theory (enable name-fresh-ok))))

(fty::deffixequiv string-list-fresh-ok
  :hints (("Goal" :in-theory (enable string-list-fresh-ok))))

(fty::deffixequiv type-var-list-fresh-ok
  :hints (("Goal" :in-theory (enable type-var-list-fresh-ok))))

(fty::deffixequiv ispace-var-list-fresh-ok
  :hints (("Goal" :in-theory (enable ispace-var-list-fresh-ok))))

(fty::deffixequiv type-fresh-ok
  :hints (("Goal" :in-theory (enable type-fresh-ok))))

(fty::deffixequiv type-option-fresh-ok
  :hints (("Goal" :in-theory (enable type-option-fresh-ok))))

(fty::deffixequiv type-list-fresh-ok
  :hints (("Goal" :in-theory (enable type-list-fresh-ok))))

(fty::deffixequiv type-list-option-fresh-ok
  :hints (("Goal" :in-theory (enable type-list-option-fresh-ok))))

(fty::deffixequiv var+type?-list-types-fresh-ok
  :hints (("Goal" :in-theory (enable var+type?-list-types-fresh-ok))))

(fty::deffixequiv expr-body-support-names
  :hints (("Goal" :in-theory (enable expr-body-support-names))))

(fty::deffixequiv bind-nocapture-ok
  :hints (("Goal" :in-theory (enable bind-nocapture-ok))))

(fty::deffixequiv bind-list-body-scope-fresh-ok
  :hints (("Goal" :in-theory (enable bind-list-body-scope-fresh-ok))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The expressions that the evaluator builds for a combined function bind
; (see the :CFUN case of EVAL-BIND): the bind's expression wrapped in a
; term abstraction over its parameters (if any), that in an ispace
; abstraction over its ispace parameters (if any), and that in a type
; abstraction over its type parameters (if any), each abstraction being a
; scalar array of one atom.  The freshness conditions of a combined
; function bind are those of these nested abstractions, layer by layer, so
; the free-variable sets of the intermediate layers are needed there;
; these functions build the layers exactly as the evaluator does.

(define cfun-lambda-expr ((params var+type?-listp) (expr exprp) (type typep))
  :returns (lam-expr exprp)
  :short "The term abstraction layer of a desugared combined function bind."
  (if (consp params)
      (make-expr-array :dims nil
                       :atoms (list (make-atom-lambda/lambdan params
                                                              expr
                                                              (type-fix type))))
    (expr-fix expr)))

(define cfun-ilambda-expr ((iparams ispace-var-listp) (expr exprp))
  :returns (ilam-expr exprp)
  :short "The ispace abstraction layer of a desugared combined function bind."
  (if (consp iparams)
      (make-expr-array :dims nil
                       :atoms (list (make-atom-ilambda/ilambdan iparams expr)))
    (expr-fix expr)))

(define cfun-tlambda-expr ((tparams type-var-listp) (expr exprp))
  :returns (tlam-expr exprp)
  :short "The type abstraction layer of a desugared combined function bind."
  (if (consp tparams)
      (make-expr-array :dims nil
                       :atoms (list (make-atom-tlambda/tlambdan tparams expr)))
    (expr-fix expr)))

(define cfun-layer-support ((params true-listp)
                            (new-names string-listp)
                            (body exprp)
                            (r var-renamings-p)
                            (bset string-setp))
  :returns (b string-setp)
  :short "Support set passed down by one (possibly absent) abstraction
          layer of a desugared combined function bind."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the layer is present (its parameter list is not empty), the
     support set for its body is the one of the abstraction atom cases of
     @(tsee atom-alpha-fresh-p): the new parameter names together with the
     renamed free variables of the body under the body's renamings.
     Otherwise the incoming support set passes through."))
  (if (consp params)
      (set::union (list-to-oset (str::string-list-fix new-names))
                  (expr-body-support-names body r))
    (string-sfix bset))
  :verify-guards nil)

(fty::deffixequiv cfun-lambda-expr
  :hints (("Goal" :in-theory (enable cfun-lambda-expr))))

(fty::deffixequiv cfun-ilambda-expr
  :hints (("Goal" :in-theory (enable cfun-ilambda-expr))))

(fty::deffixequiv cfun-tlambda-expr
  :hints (("Goal" :in-theory (enable cfun-tlambda-expr))))

(fty::deffixequiv cfun-layer-support
  :args ((new-names string-listp) (body exprp) (r var-renamings-p)
         (bset string-setp))
  :hints (("Goal" :in-theory (enable cfun-layer-support))))

; The freshness fold over the relation's traversal.

(defines exprs-alpha-fresh-p
  :parents (uniquify-alpha-relations)
  :short "The freshness fold over the traversal of
          @(tsee exprs-alpha-related-p)."
  :flag-local nil
  :verify-guards nil

  (define expr-alpha-fresh-p ((new-x exprp) (x exprp)
                              (r var-renamings-p) (b string-setp))
    :returns (yes/no booleanp)
    :parents (uniquify-alpha-relations)
    :short "Freshness companion of @(tsee expr-alpha-related-p)."
    :measure (expr-count x)
    (b* (((var-renamings r-) r))
      (expr-case
       x
       :var t
       :atom (b* (((unless (expr-case new-x :atom)) t))
               (atom-alpha-fresh-p (expr-atom->atom new-x) x.atom r b))
       :array (b* (((unless (expr-case new-x :array)) t))
                (atom-list-alpha-fresh-p (expr-array->atoms new-x)
                                         x.atoms r b))
       :array-empty (type-fresh-ok x.type r)
       :frame (b* (((unless (expr-case new-x :frame)) t))
                (expr-list-alpha-fresh-p (expr-frame->exprs new-x)
                                         x.exprs r b))
       :frame-empty (type-fresh-ok x.type r)
       :string t
       :app (b* (((unless (expr-case new-x :app)) t))
              (and (expr-alpha-fresh-p (expr-app->fun new-x) x.fun r b)
                   (expr-alpha-fresh-p (expr-app->arg new-x) x.arg r b)))
       :appn (b* (((unless (expr-case new-x :appn)) t))
               (and (expr-alpha-fresh-p (expr-appn->fun new-x) x.fun r b)
                    (expr-list-alpha-fresh-p (expr-appn->args new-x)
                                             x.args r b)))
       :tapp (b* (((unless (expr-case new-x :tapp)) t))
               (and (expr-alpha-fresh-p (expr-tapp->fun new-x) x.fun r b)
                    (type-fresh-ok x.arg r)))
       :tappn (b* (((unless (expr-case new-x :tappn)) t))
                (and (expr-alpha-fresh-p (expr-tappn->fun new-x) x.fun r b)
                     (type-list-fresh-ok x.args r)))
       :iapp (b* (((unless (expr-case new-x :iapp)) t))
               (expr-alpha-fresh-p (expr-iapp->fun new-x) x.fun r b))
       :iappn (b* (((unless (expr-case new-x :iappn)) t))
                (expr-alpha-fresh-p (expr-iappn->fun new-x) x.fun r b))
       :capp (b* (((unless (expr-case new-x :capp)) t))
               (and (expr-alpha-fresh-p (expr-capp->fun new-x) x.fun r b)
                    (type-list-option-fresh-ok x.targs r)
                    (expr-list-alpha-fresh-p (expr-capp->args new-x)
                                             x.args r b)))
       :unbox
       (b* (((unless (expr-case new-x :unbox)) t)
            ((expr-unbox u) new-x)
            ((mv okp dim-renam shape-renam)
             (ispace-var-list-alpha-extend (list u.ispace) (list x.ispace)
                                           r-.dim r-.shape))
            ((unless okp) t)
            (body-r (change-var-renamings
                     r
                     :dim dim-renam
                     :shape shape-renam
                     :expr (extend-renaming x.var u.var r-.expr))))
         (and (expr-alpha-fresh-p u.target x.target r b)
              (type-option-fresh-ok x.type? r)
              (ispace-var-list-fresh-ok (list u.ispace) (list x.ispace)
                                        r-.dim r-.shape b)
              (name-fresh-ok x.var u.var r-.expr
                             (set::insert (ispace-var->name u.ispace)
                                          (string-sfix b)))
              (not (set::in (ispace-var-fix u.ispace)
                            (ispace-var-set-rename-ispace-vars
                             (set::delete (ispace-var-fix x.ispace)
                                          (expr-free-ispace-vars x.body))
                             r-.dim r-.shape)))
              (not (set::in (str-fix u.var)
                            (rename-var-string-set
                             (set::delete (str-fix x.var)
                                          (expr-free-expr-vars x.body))
                             r-.expr)))
              (expr-alpha-fresh-p
               u.body x.body body-r
               (set::insert (ispace-var->name u.ispace)
                            (set::insert (str-fix u.var)
                                         (string-sfix b))))))
       :unboxn
       (b* (((unless (expr-case new-x :unboxn)) t)
            ((expr-unboxn u) new-x)
            ((mv okp dim-renam shape-renam)
             (ispace-var-list-alpha-extend u.ispaces x.ispaces
                                           r-.dim r-.shape))
            ((unless okp) t)
            (body-r (change-var-renamings
                     r
                     :dim dim-renam
                     :shape shape-renam
                     :expr (extend-renaming x.var u.var r-.expr)))
            (b1 (set::union (list-to-oset (ispace-var-list->name u.ispaces))
                            (string-sfix b))))
         (and (expr-alpha-fresh-p u.target x.target r b)
              (type-option-fresh-ok x.type? r)
              (ispace-var-list-fresh-ok u.ispaces x.ispaces
                                        r-.dim r-.shape b)
              (no-duplicatesp-equal (ispace-var-list-fix u.ispaces))
              (name-fresh-ok x.var u.var r-.expr b1)
              (set::emptyp
               (set::intersect
                (set::mergesort (ispace-var-list-fix u.ispaces))
                (ispace-var-set-rename-ispace-vars
                 (set::difference (expr-free-ispace-vars x.body)
                                  (set::mergesort
                                   (ispace-var-list-fix x.ispaces)))
                 r-.dim r-.shape)))
              (not (set::in (str-fix u.var)
                            (rename-var-string-set
                             (set::delete (str-fix x.var)
                                          (expr-free-expr-vars x.body))
                             r-.expr)))
              (expr-alpha-fresh-p u.body x.body body-r
                                  (set::insert (str-fix u.var) b1))))
       :bracket (b* (((unless (expr-case new-x :bracket)) t))
                  (expr-list-alpha-fresh-p (expr-bracket->exprs new-x)
                                           x.exprs r b))
       :let
       (b* (((unless (expr-case new-x :let)) t)
            ((expr-let u) new-x))
         (and (bind-list-alpha-fresh-p u.binds x.binds r b)
              (bind-list-body-scope-fresh-ok
               u.binds x.binds r
               (expr-free-expr-vars x.body)
               (expr-free-type-vars x.body)
               (expr-free-ispace-vars x.body))
              (expr-alpha-fresh-p
               u.body x.body
               (bind-list-alpha-extended-renamings u.binds x.binds r)
               (set::union (list-to-oset (bind-list-names u.binds))
                           (string-sfix b))))))))

  (define expr-list-alpha-fresh-p ((new-x expr-listp) (x expr-listp)
                                   (r var-renamings-p) (b string-setp))
    :returns (yes/no booleanp)
    :parents (uniquify-alpha-relations exprs-alpha-fresh-p)
    :short "Freshness companion of @(tsee expr-list-alpha-related-p)."
    :measure (expr-list-count x)
    (b* (((when (endp x)) t)
         ((unless (consp new-x)) t))
      (and (expr-alpha-fresh-p (car new-x) (car x) r b)
           (expr-list-alpha-fresh-p (cdr new-x) (cdr x) r b))))

  (define atom-alpha-fresh-p ((new-a atomp) (a atomp)
                              (r var-renamings-p) (b string-setp))
    :returns (yes/no booleanp)
    :parents (uniquify-alpha-relations exprs-alpha-fresh-p)
    :short "Freshness companion of @(tsee atom-alpha-related-p)."
    :measure (atom-count a)
    (b* (((var-renamings r-) r))
      (atom-case
       a
       :base t
       :lambda
       (b* (((unless (atom-case new-a :lambda)) t)
            ((atom-lambda u) new-a)
            (name (var+type?->var a.param))
            (new-name (var+type?->var u.param))
            (body-r (change-var-renamings
                     r :expr (extend-renaming name new-name r-.expr))))
         (and (type-option-fresh-ok (var+type?->type? a.param) r)
              (type-option-fresh-ok a.type? r)
              (name-fresh-ok name new-name r-.expr b)
              (not (set::in (str-fix new-name)
                            (rename-var-string-set
                             (set::delete (str-fix name)
                                          (expr-free-expr-vars a.body))
                             r-.expr)))
              (expr-alpha-fresh-p
               u.body a.body body-r
               (set::insert (str-fix new-name)
                            (expr-body-support-names a.body body-r)))))
       :lambdan
       (b* (((unless (atom-case new-a :lambdan)) t)
            ((atom-lambdan u) new-a)
            (names (var+type?-list->var a.params))
            (new-names (var+type?-list->var u.params))
            (body-r (change-var-renamings
                     r :expr (extend-renaming-list names new-names
                                                   r-.expr))))
         (and (var+type?-list-types-fresh-ok a.params r)
              (type-option-fresh-ok a.type? r)
              (string-list-fresh-ok names new-names r-.expr b)
              (no-duplicatesp-equal (str::string-list-fix new-names))
              (set::emptyp
               (set::intersect
                (list-to-oset (str::string-list-fix new-names))
                (rename-var-string-set
                 (set::difference (expr-free-expr-vars a.body)
                                  (set::mergesort
                                   (str::string-list-fix names)))
                 r-.expr)))
              (expr-alpha-fresh-p
               u.body a.body body-r
               (set::union (list-to-oset (str::string-list-fix new-names))
                           (expr-body-support-names a.body body-r)))))
       :tlambda
       (b* (((unless (atom-case new-a :tlambda)) t)
            ((atom-tlambda u) new-a)
            ((mv okp atom-renam array-renam)
             (type-var-list-alpha-extend (list u.param) (list a.param)
                                         r-.atom r-.array))
            ((unless okp) t)
            (body-r (change-var-renamings r
                                          :atom atom-renam
                                          :array array-renam)))
         (and (type-var-list-fresh-ok (list u.param) (list a.param)
                                      r-.atom r-.array b)
              (not (set::in (type-var-fix u.param)
                            (type-var-set-rename-type-vars
                             (set::delete (type-var-fix a.param)
                                          (expr-free-type-vars a.body))
                             r-.atom r-.array)))
              (expr-alpha-fresh-p
               u.body a.body body-r
               (set::insert (type-var->name u.param)
                            (expr-body-support-names a.body body-r)))))
       :tlambdan
       (b* (((unless (atom-case new-a :tlambdan)) t)
            ((atom-tlambdan u) new-a)
            ((mv okp atom-renam array-renam)
             (type-var-list-alpha-extend u.params a.params
                                         r-.atom r-.array))
            ((unless okp) t)
            (body-r (change-var-renamings r
                                          :atom atom-renam
                                          :array array-renam)))
         (and (type-var-list-fresh-ok u.params a.params
                                      r-.atom r-.array b)
              (no-duplicatesp-equal (type-var-list-fix u.params))
              (set::emptyp
               (set::intersect
                (set::mergesort (type-var-list-fix u.params))
                (type-var-set-rename-type-vars
                 (set::difference (expr-free-type-vars a.body)
                                  (set::mergesort
                                   (type-var-list-fix a.params)))
                 r-.atom r-.array)))
              (expr-alpha-fresh-p
               u.body a.body body-r
               (set::union (list-to-oset (type-var-list->name u.params))
                           (expr-body-support-names a.body body-r)))))
       :ilambda
       (b* (((unless (atom-case new-a :ilambda)) t)
            ((atom-ilambda u) new-a)
            ((mv okp dim-renam shape-renam)
             (ispace-var-list-alpha-extend (list u.param) (list a.param)
                                           r-.dim r-.shape))
            ((unless okp) t)
            (body-r (change-var-renamings r
                                          :dim dim-renam
                                          :shape shape-renam)))
         (and (ispace-var-list-fresh-ok (list u.param) (list a.param)
                                        r-.dim r-.shape b)
              (not (set::in (ispace-var-fix u.param)
                            (ispace-var-set-rename-ispace-vars
                             (set::delete (ispace-var-fix a.param)
                                          (expr-free-ispace-vars a.body))
                             r-.dim r-.shape)))
              (expr-alpha-fresh-p
               u.body a.body body-r
               (set::insert (ispace-var->name u.param)
                            (expr-body-support-names a.body body-r)))))
       :ilambdan
       (b* (((unless (atom-case new-a :ilambdan)) t)
            ((atom-ilambdan u) new-a)
            ((mv okp dim-renam shape-renam)
             (ispace-var-list-alpha-extend u.params a.params
                                           r-.dim r-.shape))
            ((unless okp) t)
            (body-r (change-var-renamings r
                                          :dim dim-renam
                                          :shape shape-renam)))
         (and (ispace-var-list-fresh-ok u.params a.params
                                        r-.dim r-.shape b)
              (no-duplicatesp-equal (ispace-var-list-fix u.params))
              (set::emptyp
               (set::intersect
                (set::mergesort (ispace-var-list-fix u.params))
                (ispace-var-set-rename-ispace-vars
                 (set::difference (expr-free-ispace-vars a.body)
                                  (set::mergesort
                                   (ispace-var-list-fix a.params)))
                 r-.dim r-.shape)))
              (expr-alpha-fresh-p
               u.body a.body body-r
               (set::union (list-to-oset (ispace-var-list->name u.params))
                           (expr-body-support-names a.body body-r)))))
       :box (b* (((unless (atom-case new-a :box)) t))
              (and (expr-alpha-fresh-p (atom-box->array new-a) a.array r b)
                   (type-option-fresh-ok a.type? r)))
       :boxn (b* (((unless (atom-case new-a :boxn)) t))
               (and (expr-alpha-fresh-p (atom-boxn->array new-a)
                                        a.array r b)
                    (type-option-fresh-ok a.type? r))))))

  (define atom-list-alpha-fresh-p ((new-a atom-listp) (a atom-listp)
                                   (r var-renamings-p) (b string-setp))
    :returns (yes/no booleanp)
    :parents (uniquify-alpha-relations exprs-alpha-fresh-p)
    :short "Freshness companion of @(tsee atom-list-alpha-related-p)."
    :measure (atom-list-count a)
    (b* (((when (endp a)) t)
         ((unless (consp new-a)) t))
      (and (atom-alpha-fresh-p (car new-a) (car a) r b)
           (atom-list-alpha-fresh-p (cdr new-a) (cdr a) r b))))

  (define bind-alpha-fresh-p ((new-b bindp) (b bindp)
                              (r var-renamings-p) (bset string-setp))
    :returns (yes/no booleanp)
    :parents (uniquify-alpha-relations exprs-alpha-fresh-p)
    :short "Freshness companion of @(tsee bind-alpha-related-p).  The
            bind's own name is checked here against the incoming
            renamings and support set; its extension into scope is the
            business of the enclosing let (via
            @(tsee bind-list-alpha-fresh-p))."
    :measure (bind-count b)
    (b* (((var-renamings r-) r)
         (name (bind-name b))
         (new-name (bind-name new-b))
         (name-ok
          (bind-case
           b
           :ispace (ispace-var-case
                    b.var
                    :dim (name-fresh-ok name new-name r-.dim bset)
                    :shape (name-fresh-ok name new-name r-.shape bset))
           :type (type-var-case
                  b.var
                  :atom (name-fresh-ok name new-name r-.atom bset)
                  :array (name-fresh-ok name new-name r-.array bset))
           :otherwise (name-fresh-ok name new-name r-.expr bset))))
      (and name-ok
           (bind-case
            b
            :ispace t
            :type (type-fresh-ok (bind-type->type b) r)
            :val (b* (((unless (bind-case new-b :val)) t))
                   (and (type-option-fresh-ok (bind-val->type? b) r)
                        (expr-alpha-fresh-p (bind-val->expr new-b)
                                            (bind-val->expr b) r bset)))
            :fun
            (b* (((unless (bind-case new-b :fun)) t)
                 ((bind-fun u) new-b)
                 (names (var+type?-list->var b.params))
                 (new-names (var+type?-list->var u.params))
                 (body-r (change-var-renamings
                          r :expr (extend-renaming-list names new-names
                                                        r-.expr))))
              (and (var+type?-list-types-fresh-ok b.params r)
                   (type-option-fresh-ok b.type? r)
                   (string-list-fresh-ok names new-names r-.expr bset)
                   (no-duplicatesp-equal
                    (str::string-list-fix new-names))
                   (set::emptyp
                    (set::intersect
                     (list-to-oset (str::string-list-fix new-names))
                     (rename-var-string-set
                      (set::difference (expr-free-expr-vars b.expr)
                                       (set::mergesort
                                        (str::string-list-fix names)))
                      r-.expr)))
                   (expr-alpha-fresh-p
                    u.expr b.expr body-r
                    (set::union (list-to-oset
                                 (str::string-list-fix new-names))
                                (set::union (string-sfix bset) (expr-body-support-names b.expr body-r))))))
            :tfun
            (b* (((unless (bind-case new-b :tfun)) t)
                 ((bind-tfun u) new-b)
                 ((mv okp atom-renam array-renam)
                  (type-var-list-alpha-extend u.params b.params
                                              r-.atom r-.array))
                 ((unless okp) t)
                 (body-r (change-var-renamings r
                                               :atom atom-renam
                                               :array array-renam)))
              (and (type-var-list-fresh-ok u.params b.params
                                           r-.atom r-.array bset)
                   (no-duplicatesp-equal (type-var-list-fix u.params))
                   (type-option-fresh-ok b.type? body-r)
                   (set::emptyp
                    (set::intersect
                     (set::mergesort (type-var-list-fix u.params))
                     (type-var-set-rename-type-vars
                      (set::difference
                       (set::union
                        (type-option-free-type-vars b.type?)
                        (expr-free-type-vars b.expr))
                       (set::mergesort (type-var-list-fix b.params)))
                      r-.atom r-.array)))
                   (expr-alpha-fresh-p
                    u.expr b.expr body-r
                    (set::union (list-to-oset
                                 (type-var-list->name u.params))
                                (set::union (string-sfix bset) (expr-body-support-names b.expr body-r))))))
            :ifun
            (b* (((unless (bind-case new-b :ifun)) t)
                 ((bind-ifun u) new-b)
                 ((mv okp dim-renam shape-renam)
                  (ispace-var-list-alpha-extend u.params b.params
                                                r-.dim r-.shape))
                 ((unless okp) t)
                 (body-r (change-var-renamings r
                                               :dim dim-renam
                                               :shape shape-renam)))
              (and (ispace-var-list-fresh-ok u.params b.params
                                             r-.dim r-.shape bset)
                   (no-duplicatesp-equal
                    (ispace-var-list-fix u.params))
                   (type-option-fresh-ok b.type? body-r)
                   (set::emptyp
                    (set::intersect
                     (set::mergesort (ispace-var-list-fix u.params))
                     (ispace-var-set-rename-ispace-vars
                      (set::difference
                       (set::union
                        (type-option-free-ispace-vars b.type?)
                        (expr-free-ispace-vars b.expr))
                       (set::mergesort (ispace-var-list-fix b.params)))
                      r-.dim r-.shape)))
                   (expr-alpha-fresh-p
                    u.expr b.expr body-r
                    (set::union (list-to-oset
                                 (ispace-var-list->name u.params))
                                (set::union (string-sfix bset) (expr-body-support-names b.expr body-r))))))
            :cfun
            ;; The evaluator desugars a combined function bind into nested
            ;; type, ispace, and term abstractions, each a scalar array of
            ;; one atom (see EVAL-BIND and CFUN-LAMBDA-EXPR etc.), and
            ;; evaluates the result; so the conditions are those of the
            ;; abstraction atom cases above, layer by layer, the support set
            ;; of each layer's body being the one its abstraction passes
            ;; down (the new parameters plus the renamed free variables of
            ;; the body), and the innermost one being on the bind's
            ;; expression.  Absent layers contribute vacuous conditions and
            ;; pass the support set through.  The no-capture conditions on
            ;; the new type and ispace parameters are over the free
            ;; variables of all the bind's components (which include those
            ;; of the nested layers), as the free-variable image laws below
            ;; require even when the bind has no parameters.
            (b* (((unless (bind-case new-b :cfun)) t)
                 ((bind-cfun u) new-b)
                 (tparams (type-var-list-option-case b.tparams?
                                                     :some b.tparams?.val
                                                     :none nil))
                 (new-tparams (type-var-list-option-case u.tparams?
                                                         :some u.tparams?.val
                                                         :none nil))
                 ((unless (equal (type-var-list-option-case u.tparams?
                                                            :some)
                                 (type-var-list-option-case b.tparams?
                                                            :some)))
                  t)
                 (iparams (ispace-var-list-option-case b.iparams?
                                                       :some b.iparams?.val
                                                       :none nil))
                 (new-iparams (ispace-var-list-option-case u.iparams?
                                                           :some u.iparams?.val
                                                           :none nil))
                 ((unless (equal (ispace-var-list-option-case u.iparams?
                                                              :some)
                                 (ispace-var-list-option-case b.iparams?
                                                              :some)))
                  t)
                 ((mv okp1 atom-renam array-renam)
                  (type-var-list-alpha-extend new-tparams tparams
                                              r-.atom r-.array))
                 ((unless okp1) t)
                 ((mv okp2 dim-renam shape-renam)
                  (ispace-var-list-alpha-extend new-iparams iparams
                                                r-.dim r-.shape))
                 ((unless okp2) t)
                 (tbody-r (change-var-renamings r
                                                :atom atom-renam
                                                :array array-renam))
                 (inner-r (change-var-renamings tbody-r
                                                :dim dim-renam
                                                :shape shape-renam))
                 ((var-renamings inner-r-) inner-r)
                 (names (var+type?-list->var b.params))
                 (new-names (var+type?-list->var u.params))
                 (body-r (change-var-renamings
                          inner-r
                          :expr (extend-renaming-list names new-names
                                                      inner-r-.expr)))
                 (lam-expr (cfun-lambda-expr b.params b.expr b.type))
                 (ilam-expr (cfun-ilambda-expr iparams lam-expr))
                 (tbset (cfun-layer-support tparams
                                            (type-var-list->name new-tparams)
                                            ilam-expr tbody-r bset))
                 (ibset (cfun-layer-support iparams
                                            (ispace-var-list->name new-iparams)
                                            lam-expr inner-r tbset))
                 (lbset (cfun-layer-support b.params new-names
                                            b.expr body-r ibset)))
              (and ;; the type abstraction layer
                   (type-var-list-fresh-ok new-tparams tparams
                                           r-.atom r-.array bset)
                   (no-duplicatesp-equal
                    (type-var-list-fix new-tparams))
                   (set::emptyp
                    (set::intersect
                     (set::mergesort (type-var-list-fix new-tparams))
                     (type-var-set-rename-type-vars
                      (set::difference
                       (set::union
                        (var+type?-list-free-type-vars b.params)
                        (set::union (type-free-type-vars b.type)
                                    (expr-free-type-vars b.expr)))
                       (set::mergesort (type-var-list-fix tparams)))
                      r-.atom r-.array)))
                   ;; the ispace abstraction layer
                   (ispace-var-list-fresh-ok new-iparams iparams
                                             r-.dim r-.shape tbset)
                   (no-duplicatesp-equal
                    (ispace-var-list-fix new-iparams))
                   (set::emptyp
                    (set::intersect
                     (set::mergesort (ispace-var-list-fix new-iparams))
                     (ispace-var-set-rename-ispace-vars
                      (set::difference
                       (set::union
                        (var+type?-list-free-ispace-vars b.params)
                        (set::union (type-free-ispace-vars b.type)
                                    (expr-free-ispace-vars b.expr)))
                       (set::mergesort (ispace-var-list-fix iparams)))
                      r-.dim r-.shape)))
                   ;; the term abstraction layer
                   (var+type?-list-types-fresh-ok b.params inner-r)
                   (type-fresh-ok b.type inner-r)
                   (string-list-fresh-ok names new-names
                                         inner-r-.expr ibset)
                   (no-duplicatesp-equal
                    (str::string-list-fix new-names))
                   (set::emptyp
                    (set::intersect
                     (list-to-oset (str::string-list-fix new-names))
                     (rename-var-string-set
                      (set::difference (expr-free-expr-vars b.expr)
                                       (set::mergesort
                                        (str::string-list-fix names)))
                      inner-r-.expr)))
                   ;; the body
                   (expr-alpha-fresh-p u.expr b.expr body-r lbset)))))))

  (define bind-list-alpha-fresh-p ((new-b bind-listp) (b bind-listp)
                                   (r var-renamings-p) (bset string-setp))
    :returns (yes/no booleanp)
    :parents (uniquify-alpha-relations exprs-alpha-fresh-p)
    :short "Freshness companion of @(tsee bind-list-alpha-related-p),
            threading the extended renamings and growing the support set
            with each bind's new name."
    :measure (bind-list-count b)
    (b* (((when (endp b)) t)
         ((unless (consp new-b)) t))
      (and (bind-alpha-fresh-p (car new-b) (car b) r bset)
           (bind-nocapture-ok (car new-b) (car b) r
                              (bind-list-free-expr-vars (cdr b))
                              (bind-list-free-type-vars (cdr b))
                              (bind-list-free-ispace-vars (cdr b)))
           (bind-list-alpha-fresh-p
            (cdr new-b) (cdr b)
            (bind-alpha-extended-renamings (car new-b) (car b) r)
            (set::insert (str-fix (bind-name (car new-b)))
                         (string-sfix bset))))))

  ///

  (fty::deffixequiv-mutual exprs-alpha-fresh-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Failure-direction conditions for the type-variable and
; expression-variable layers, restricted to a variable set, as for
; DENV-ISPACE-VARS-AVOIDED-P above: a lookup that fails on the original
; side fails at the renamed key, for the variables in the set.  The
; evaluation theorems instantiate the set with the free variables of the
; AST under evaluation.

(acl2::defun-sk string-expr-value-map-avoided-p (new-map map renam vars)
  (forall (var)
          (implies (and (set::in var (string-sfix vars))
                        (not (omap::assoc var
                                          (string-expr-value-map-fix map))))
                   (not (omap::assoc (rename-var-string var renam)
                                     (string-expr-value-map-fix new-map)))))
  :rewrite :direct)

(in-theory (disable string-expr-value-map-avoided-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Bounds on the captured environments of closures, as the value relations
; below record them: the keys of the (original) captured environment are
; among the free variables of the closure's body, and the two captured
; environments satisfy the failure-direction relation at those variables.
; Both are established by the environment restriction performed at
; closure creation, and consumed when the closure is applied.

(define type-denv-keys-within-p ((tenv type-denvp)
                                 (ivars ispace-var-setp)
                                 (tvars type-var-setp))
  :returns (yes/no booleanp)
  :short "The keys of a type environment are within the given sets."
  (and (set::subset (omap::keys (ispace-denv->ispaces (type-denv->ienv tenv)))
                    (ispace-var-set-fix ivars))
       (set::subset (omap::keys (type-denv->types tenv))
                    (type-var-set-fix tvars))))

(define type-denv-alpha-avoided-p ((new-tenv type-denvp)
                                   (tenv type-denvp)
                                   (r var-renamings-p)
                                   (ivars ispace-var-setp)
                                   (tvars type-var-setp))
  :returns (yes/no booleanp)
  :short "Failure-direction relation of two type environments,
          at the given variables, in both layers."
  :verify-guards nil
  (b* (((var-renamings r-) r))
    (and (denv-ispace-vars-avoided-p (type-denv->ienv new-tenv)
                                     (type-denv->ienv tenv)
                                     r-.dim r-.shape ivars)
         (type-var-map-avoided-p (type-denv->types new-tenv)
                                 (type-denv->types tenv)
                                 r-.atom r-.array tvars))))

(define expr-denv-keys-within-p ((denv expr-denvp)
                                 (ivars ispace-var-setp)
                                 (tvars type-var-setp)
                                 (evars string-setp))
  :returns (yes/no booleanp)
  :short "The keys of an expression environment are within the given sets."
  (and (type-denv-keys-within-p (expr-denv->tenv denv) ivars tvars)
       (set::subset (omap::keys (expr-denv->exprs denv))
                    (string-sfix evars))))

; The keys of the typed maps are typed sets.

(defrule string-setp-of-keys-when-string-expr-value-mapp
  (implies (string-expr-value-mapp map)
           (string-setp (omap::keys map)))
  :induct t
  :enable (omap::keys string-expr-value-mapp))

(defrule type-var-setp-of-keys-when-type-var-type-value-mapp
  (implies (type-var-type-value-mapp map)
           (type-var-setp (omap::keys map)))
  :induct t
  :enable (omap::keys type-var-type-value-mapp))

(defrule ispace-var-setp-of-keys-when-ispace-var-ispace-value-mapp
  (implies (ispace-var-ispace-value-mapp map)
           (ispace-var-setp (omap::keys map)))
  :induct t
  :enable (omap::keys ispace-var-ispace-value-mapp))

; The support invariant of the induction: the keys of the original
; environment, in each namespace, are among the support set of the
; freshness fold or the keys of that namespace's renaming map.  It is what
; lets the freshness of a binder name (see NAME-FRESH-OK) exclude every
; collision of the new name with the renaming of another key of the
; original environment, which the extension lemmas require; it is
; preserved at each binder, since a renamed name enters the renaming's
; keys and a kept name enters the support set.

(define string-set-supported-p ((keys string-setp)
                                (renam string-string-mapp)
                                (b string-setp))
  :returns (yes/no booleanp)
  :short "A set of names is within a support set or the keys of a
          renaming map."
  (set::subset (string-sfix keys)
               (set::union (string-sfix b)
                           (omap::keys (string-string-map-fix renam)))))

(define expr-denv-keys-supported-p ((denv expr-denvp)
                                    (r var-renamings-p)
                                    (b string-setp))
  :returns (yes/no booleanp)
  :short "The keys of an environment are within the support set or the
          renaming maps' keys, in each namespace."
  (b* (((var-renamings r-) r)
       (ikeys (omap::keys (ispace-denv->ispaces
                           (type-denv->ienv (expr-denv->tenv denv)))))
       (tkeys (omap::keys (type-denv->types (expr-denv->tenv denv))))
       ((mv dim-names shape-names) (dim/shape-names-of-ispace-vars ikeys))
       ((mv atom-names array-names) (atom/array-names-of-type-vars tkeys)))
    (and (string-set-supported-p dim-names r-.dim b)
         (string-set-supported-p shape-names r-.shape b)
         (string-set-supported-p atom-names r-.atom b)
         (string-set-supported-p array-names r-.array b)
         (string-set-supported-p (omap::keys (expr-denv->exprs denv))
                                 r-.expr b))))

(define expr-denv-alpha-avoided-p ((new-denv expr-denvp)
                                   (denv expr-denvp)
                                   (r var-renamings-p)
                                   (ivars ispace-var-setp)
                                   (tvars type-var-setp)
                                   (evars string-setp))
  :returns (yes/no booleanp)
  :short "Failure-direction relation of two expression environments,
          at the given variables, in all three layers."
  :verify-guards nil
  (and (type-denv-alpha-avoided-p (expr-denv->tenv new-denv)
                                  (expr-denv->tenv denv)
                                  r ivars tvars)
       (string-expr-value-map-avoided-p (expr-denv->exprs new-denv)
                                        (expr-denv->exprs denv)
                                        (var-renamings->expr r)
                                        evars)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The witness-indexed value relations, which the main induction uses (see
; the design notes at the end of this book for why a shared-renaming
; relation cannot support it).
;
; Each closure pair is related under its OWN renaming bundle --- the one
; in scope where the value was created --- and the entries of a captured
; environment each carry their own witness in turn.  The same holds one
; level down: type values composed by evaluation mix sub-values drawn
; from environment entries with different creation scopes, so type values
; also relate via witness TREES (a renaming bundle at each
; universal/product/sum node, sub-witnesses at composite nodes, and
; per-entry witnesses for the captured type environments), rather than by
; one composed renaming.  Since an existential quantifier cannot appear
; inside a recursive clique, the witnesses are explicit arguments;
; DEFUN-SK wrappers below restore the existential form for use in theorem
; statements.
;
; The closure cases of the expression-value relation also carry the
; no-capture conditions that the application step of the main induction
; needs: the new parameter name must not collide with the renaming-image
; of the body's other free variables (in the parameter's namespace).  The
; freshness facts of UNIQ-EXPR discharge these conditions at closure
; creation (see UNIQUIFY-FRESHNESS).  The type-value closures carry the
; corresponding TYPE-FRESH-OK condition on their bodies, used when
; EVAL-TAPP and EVAL-IAPP instantiate universal and product type values.
;
; Primitive-operation values relate pointwise (PRIMOP-VALUE-ALPHA-RELATED-
; VIA-P): a partially applied primitive stores type values and expression
; values received so far, which are only alpha-related across the two
; runs, so they relate via witnesses of their own.
;
; A leaf witness (:LEAF for type values, :ATOM for expression values)
; stands for plain equality, so that ground sub-values need no witness
; construction.
;
; The closure cases carry what the application step of the main induction
; needs to evaluate the closure's body in its captured environment: the
; no-capture of the (new) parameter against the renaming-image of the
; body's other free variables; the freshness of the body (the fold of the
; freshness companion above); the bound of the (original) captured
; environment's keys by the body's free variables, and the failure-
; direction relation of the two captured environments at those
; variables.  The type-value closures carry the analogous conditions for
; the deterministic renaming of their bodies.

; Environment relations, split by direction.
;
; Unlike the pure-renaming development, where binder names are preserved
; and environment extensions add THE SAME keys on both sides (so that
; universally quantified pair-equality relations, as in the first design,
; are preserved by extension), the uniquified run extends its environments
; at FRESHENED keys.  An extension at a fresh key leaves the new-side
; environment with entries at names the original program never mentions,
; so a both-ways (iff-style) domain correspondence is not invariant under
; extension.  The invariant therefore splits by direction:
;
; - the SUCCESS direction (below, -COVERED-P; and, for the type and
;   expression layers, the recursive pointwise relations, which iterate
;   the ORIGINAL environment's entries): a lookup that succeeds on the
;   original side succeeds, suitably related, at the renamed key;
;
; - the FAILURE direction (-AVOIDED-P), restricted to an explicit
;   variable set (in the evaluation theorems, the free variables of the
;   AST under evaluation; those are the only variables either run can
;   mention): a lookup that fails on the original side fails at the
;   renamed key, giving error equivalence.  The restriction to a set is
;   what makes the condition invariant: the stale new-side entries at
;   freshened keys are never the renaming of a variable the original
;   scope can mention (no-capture), so they escape the quantifier.

(fty::deftypes type-value-witnesses
  (fty::deftagsum type-value-witness
    (:leaf ())
    (:array ((elem type-value-witness)))
    (:fun ((in type-value-witness)
           (out type-value-witness)))
    (:closure ((r var-renamings)
               (types type-var-type-value-witness-map)))
    :pred type-value-witness-p
    :measure (two-nats-measure (acl2-count x) 0))
  (fty::deflist type-value-witness-list
    :elt-type type-value-witness
    :true-listp t
    :pred type-value-witness-listp
    :measure (two-nats-measure (acl2-count x) 0))
  (fty::defomap type-var-type-value-witness-map
    :key-type type-var
    :val-type type-value-witness
    :pred type-var-type-value-witness-mapp
    :measure (two-nats-measure (acl2-count x) 0)))

; The type-value relation mirrors the case structure of the composed
; deterministic renamings of types (see TYPE-RENAME-ISPACE-VARS and
; TYPE-RENAME-TYPE-VARS): at a universal node the type-variable
; renamings are reduced at the (kept) parameter for the body, at a
; product/sum node the ispace-variable renamings are; the captured
; environment's keys are renamed under the node's (unreduced) bundle and
; its entries relate via their own witnesses.

(defines type-value-alpha-related-via-p
  :flag-local nil

  (define type-value-alpha-related-via-p ((new-tval type-valuep)
                                          (tval type-valuep)
                                          (w type-value-witness-p))
    :returns (yes/no booleanp)
    :parents (uniquify-alpha-relations)
    :short "Alpha-relatedness of type values via an explicit renaming
            witness."
    :measure (type-value-count tval)
    (b* (((when (type-value-witness-case w :leaf))
          (and (equal (type-value-fix new-tval) (type-value-fix tval))
               (type-value-groundp tval))))
     (type-value-case
     tval
     :base (and (type-value-case new-tval :base)
                (equal (type-value-base->type new-tval) tval.type))
     :array (and (type-value-case new-tval :array)
                 (type-value-witness-case w :array)
                 (equal (type-value-array->dims new-tval) tval.dims)
                 (type-value-alpha-related-via-p
                  (type-value-array->elem new-tval)
                  tval.elem
                  (type-value-witness-array->elem w)))
     :fun (and (type-value-case new-tval :fun)
               (type-value-witness-case w :fun)
               (type-value-alpha-related-via-p
                (type-value-fun->in new-tval)
                tval.in
                (type-value-witness-fun->in w))
               (type-value-alpha-related-via-p
                (type-value-fun->out new-tval)
                tval.out
                (type-value-witness-fun->out w)))
     :forall
     (b* (((unless (type-value-case new-tval :forall)) nil)
          ((unless (type-value-witness-case w :closure)) nil)
          ((type-value-witness-closure w-) w)
          ((var-renamings r-) w-.r)
          ((type-value-forall u) new-tval)
          ((mv & & body-atom-renam body-array-renam)
           (atom/array-rename-remove-bound (set::insert tval.param nil)
                                           r-.atom r-.array))
          (body-r (change-var-renamings w-.r
                                        :atom body-atom-renam
                                        :array body-array-renam))
          (free-ivars (type-free-ispace-vars tval.body))
          (free-tvars (set::delete tval.param
                                   (type-free-type-vars tval.body))))
       (and (equal u.param tval.param)
            (equal u.body
                   (type-rename-type-vars
                    (type-rename-ispace-vars tval.body r-.dim r-.shape)
                    body-atom-renam body-array-renam))
            (not (set::in tval.param
                          (type-var-set-rename-type-vars
                           free-tvars body-atom-renam body-array-renam)))
            (type-fresh-ok tval.body body-r)
            (type-denv-alpha-related-via-p u.denv tval.denv w-.r w-.types)
            (type-denv-keys-within-p tval.denv free-ivars free-tvars)
            (type-denv-alpha-avoided-p u.denv tval.denv w-.r
                                       free-ivars free-tvars)))
     :pi
     (b* (((unless (type-value-case new-tval :pi)) nil)
          ((unless (type-value-witness-case w :closure)) nil)
          ((type-value-witness-closure w-) w)
          ((var-renamings r-) w-.r)
          ((type-value-pi u) new-tval)
          ((mv & & body-dim-renam body-shape-renam)
           (dim/shape-rename-remove-bound (set::insert tval.param nil)
                                          r-.dim r-.shape))
          (body-r (change-var-renamings w-.r
                                        :dim body-dim-renam
                                        :shape body-shape-renam))
          (free-ivars (set::delete tval.param
                                   (type-free-ispace-vars tval.body)))
          (free-tvars (type-free-type-vars tval.body)))
       (and (equal u.param tval.param)
            (equal u.body
                   (type-rename-type-vars
                    (type-rename-ispace-vars tval.body
                                             body-dim-renam
                                             body-shape-renam)
                    r-.atom r-.array))
            (not (set::in tval.param
                          (ispace-var-set-rename-ispace-vars
                           free-ivars body-dim-renam body-shape-renam)))
            (type-fresh-ok tval.body body-r)
            (type-denv-alpha-related-via-p u.denv tval.denv w-.r w-.types)
            (type-denv-keys-within-p tval.denv free-ivars free-tvars)
            (type-denv-alpha-avoided-p u.denv tval.denv w-.r
                                       free-ivars free-tvars)))
     :sigma
     (b* (((unless (type-value-case new-tval :sigma)) nil)
          ((unless (type-value-witness-case w :closure)) nil)
          ((type-value-witness-closure w-) w)
          ((var-renamings r-) w-.r)
          ((type-value-sigma u) new-tval)
          ((mv & & body-dim-renam body-shape-renam)
           (dim/shape-rename-remove-bound (set::insert tval.param nil)
                                          r-.dim r-.shape))
          (body-r (change-var-renamings w-.r
                                        :dim body-dim-renam
                                        :shape body-shape-renam))
          (free-ivars (set::delete tval.param
                                   (type-free-ispace-vars tval.body)))
          (free-tvars (type-free-type-vars tval.body)))
       (and (equal u.param tval.param)
            (equal u.body
                   (type-rename-type-vars
                    (type-rename-ispace-vars tval.body
                                             body-dim-renam
                                             body-shape-renam)
                    r-.atom r-.array))
            (not (set::in tval.param
                          (ispace-var-set-rename-ispace-vars
                           free-ivars body-dim-renam body-shape-renam)))
            (type-fresh-ok tval.body body-r)
            (type-denv-alpha-related-via-p u.denv tval.denv w-.r w-.types)
            (type-denv-keys-within-p tval.denv free-ivars free-tvars)
            (type-denv-alpha-avoided-p u.denv tval.denv w-.r
                                       free-ivars free-tvars))))))

  (define type-value-list-alpha-related-via-p ((new-tvals type-value-listp)
                                               (tvals type-value-listp)
                                               (ws type-value-witness-listp))
    :returns (yes/no booleanp)
    :parents (uniquify-alpha-relations type-value-alpha-related-via-p)
    :short "Alpha-relatedness of lists of type values via witnesses."
    :measure (type-value-list-count tvals)
    (if (endp tvals)
        (endp new-tvals)
      (and (consp new-tvals)
           (consp ws)
           (type-value-alpha-related-via-p (car new-tvals) (car tvals)
                                           (car ws))
           (type-value-list-alpha-related-via-p (cdr new-tvals) (cdr tvals)
                                                (cdr ws)))))

  (define type-var-type-value-map-alpha-related-via-p
    ((new-map type-var-type-value-mapp)
     (map type-var-type-value-mapp)
     (r var-renamings-p)
     (wmap type-var-type-value-witness-mapp))
    :returns (yes/no booleanp)
    :parents (uniquify-alpha-relations type-value-alpha-related-via-p)
    :short "Pointwise alpha-relatedness of type-variable maps: keys
            renamed under the in-scope renamings, each value related to
            the original under its own per-entry witness."
    :measure (type-var-type-value-map-count map)
    (b* ((map (type-var-type-value-map-fix map))
         ((when (omap::emptyp map)) t)
         ((mv var tval) (omap::head map))
         ((var-renamings r-) r)
         (pair (omap::assoc (rename-type-var var r-.atom r-.array)
                            (type-var-type-value-map-fix new-map)))
         (wpair (omap::assoc (type-var-fix var)
                             (type-var-type-value-witness-map-fix wmap)))
         (w (if wpair (cdr wpair) (type-value-witness-leaf))))
      (and pair
           (type-value-alpha-related-via-p (cdr pair) tval w)
           (type-var-type-value-map-alpha-related-via-p new-map
                                                        (omap::tail map)
                                                        r wmap))))

  (define type-denv-alpha-related-via-p ((new-tenv type-denvp)
                                         (tenv type-denvp)
                                         (r var-renamings-p)
                                         (wmap type-var-type-value-witness-mapp))
    :returns (yes/no booleanp)
    :parents (uniquify-alpha-relations type-value-alpha-related-via-p)
    :short "Alpha-relatedness of type dynamic environments: the ispace
            layer by renamed-key lookup with equal (ground) values under
            the in-scope renamings (success direction only, see above),
            the type-variable layer pointwise with per-entry witnesses."
    :measure (type-denv-count tenv)
    (b* (((var-renamings r-) r))
      (and (denv-ispace-vars-covered-p (type-denv->ienv new-tenv)
                                       (type-denv->ienv tenv)
                                       r-.dim r-.shape)
           (type-var-type-value-map-alpha-related-via-p
            (type-denv->types new-tenv)
            (type-denv->types tenv)
            r wmap)
           t)))

  :verify-guards nil)

(define type-value-option-alpha-related-via-p ((new-tval? type-value-optionp)
                                               (tval? type-value-optionp)
                                               (w type-value-witness-p))
  :returns (yes/no booleanp)
  ;; The type-value relation is not guard-verified (it calls a defun-sk).
  :verify-guards nil
  :short "Alpha-relatedness of optional type values via a witness."
  (type-value-option-case
   tval?
   :none (type-value-option-case new-tval? :none)
   :some (and (type-value-option-case new-tval? :some)
              (type-value-alpha-related-via-p
               (type-value-option-some->val new-tval?)
               tval?.val
               w))))

(fty::deftypes expr-value-witnesses
  (fty::deftagsum expr-value-witness
    (:atom ())
    (:primop ((tws type-value-witness-list)
              (ws expr-value-witness-list)))
    (:closure ((r var-renamings)
               (ptype type-value-witness)
               (rtype type-value-witness)
               (denv denv-witness)
               (b acl2::string-set)))
    (:box ((type type-value-witness)
           (array expr-value-witness)))
    (:vector ((elems expr-value-witness-list)))
    (:vempty ((elem type-value-witness)))
    :pred expr-value-witness-p
    :measure (two-nats-measure (acl2-count x) 0))
  (fty::deflist expr-value-witness-list
    :elt-type expr-value-witness
    :true-listp t
    :pred expr-value-witness-listp
    :measure (two-nats-measure (acl2-count x) 0))
  (fty::defomap string-expr-value-witness-map
    :key-type acl2::string
    :val-type expr-value-witness
    :pred string-expr-value-witness-mapp
    :measure (two-nats-measure (acl2-count x) 0))
  (fty::defprod denv-witness
    ((types type-var-type-value-witness-map)
     (exprs string-expr-value-witness-map))
    :pred denv-witness-p
    :measure (two-nats-measure (acl2-count x) 1)))

(defines expr-value-alpha-related-via-p
  :flag-local nil

  (define expr-value-alpha-related-via-p ((new-val expr-valuep)
                                          (val expr-valuep)
                                          (w expr-value-witness-p))
    :returns (yes/no booleanp)
    :parents (uniquify-alpha-relations)
    :short "Alpha-relatedness of expression values via an explicit
            renaming witness."
    :measure (expr-value-count val)
    (b* (((when (expr-value-witness-case w :atom))
          (and (equal (expr-value-fix new-val) (expr-value-fix val))
               (expr-value-groundp val))))
     (expr-value-case
     val
     :base (and (expr-value-case new-val :base)
                (equal (expr-value-base->val new-val) val.val))
     :primop (and (expr-value-case new-val :primop)
                  (expr-value-witness-case w :primop)
                  (primop-value-alpha-related-via-p
                   (expr-value-primop->val new-val)
                   val.val
                   (expr-value-witness-primop->tws w)
                   (expr-value-witness-primop->ws w)))
     :lambda
     (b* (((unless (expr-value-case new-val :lambda)) nil)
          ((unless (expr-value-witness-case w :closure)) nil)
          ((expr-value-witness-closure w-) w)
          ((var-renamings r-) w-.r)
          ((expr-value-lambda u) new-val)
          (old-name (var+typevalue->var val.param))
          (new-name (var+typevalue->var u.param))
          (body-r (change-var-renamings
                   w-.r :expr (extend-renaming old-name new-name r-.expr)))
          (free-ivars (expr-free-ispace-vars val.body))
          (free-tvars (expr-free-type-vars val.body))
          (free-evars (set::delete old-name
                                   (expr-free-expr-vars val.body))))
       (and (type-value-alpha-related-via-p
             (var+typevalue->type u.param)
             (var+typevalue->type val.param)
             w-.ptype)
            (type-value-option-alpha-related-via-p u.type? val.type?
                                                   w-.rtype)
            (expr-alpha-related-p u.body val.body body-r)
            (expr-alpha-fresh-p u.body val.body body-r
                                (set::insert new-name w-.b))
            (expr-denv-keys-supported-p val.denv body-r
                                        (set::insert new-name w-.b))
            (not (set::in new-name
                          (rename-var-string-set free-evars r-.expr)))
            (expr-denv-alpha-related-via-p u.denv val.denv w-.r w-.denv)
            (expr-denv-keys-within-p val.denv
                                     free-ivars free-tvars free-evars)
            (expr-denv-alpha-avoided-p u.denv val.denv w-.r
                                       free-ivars free-tvars free-evars)))
     :tlambda
     (b* (((unless (expr-value-case new-val :tlambda)) nil)
          ((unless (expr-value-witness-case w :closure)) nil)
          ((expr-value-witness-closure w-) w)
          ((var-renamings r-) w-.r)
          ((expr-value-tlambda u) new-val)
          ((mv okp atom-renam array-renam)
           (type-var-list-alpha-extend (list u.param) (list val.param)
                                       r-.atom r-.array))
          ((unless okp) nil)
          (body-r (change-var-renamings w-.r
                                        :atom atom-renam
                                        :array array-renam))
          (free-ivars (expr-free-ispace-vars val.body))
          (free-tvars (set::delete (type-var-fix val.param)
                                   (expr-free-type-vars val.body)))
          (free-evars (expr-free-expr-vars val.body)))
       (and (expr-alpha-related-p u.body val.body body-r)
            (expr-alpha-fresh-p u.body val.body body-r
                                (set::insert (type-var->name u.param) w-.b))
            (expr-denv-keys-supported-p val.denv body-r
                                        (set::insert (type-var->name u.param)
                                                     w-.b))
            (not (set::in (type-var-fix u.param)
                          (type-var-set-rename-type-vars
                           free-tvars r-.atom r-.array)))
            (expr-denv-alpha-related-via-p u.denv val.denv w-.r w-.denv)
            (expr-denv-keys-within-p val.denv
                                     free-ivars free-tvars free-evars)
            (expr-denv-alpha-avoided-p u.denv val.denv w-.r
                                       free-ivars free-tvars free-evars)))
     :ilambda
     (b* (((unless (expr-value-case new-val :ilambda)) nil)
          ((unless (expr-value-witness-case w :closure)) nil)
          ((expr-value-witness-closure w-) w)
          ((var-renamings r-) w-.r)
          ((expr-value-ilambda u) new-val)
          ((mv okp dim-renam shape-renam)
           (ispace-var-list-alpha-extend (list u.param) (list val.param)
                                         r-.dim r-.shape))
          ((unless okp) nil)
          (body-r (change-var-renamings w-.r
                                        :dim dim-renam
                                        :shape shape-renam))
          (free-ivars (set::delete (ispace-var-fix val.param)
                                   (expr-free-ispace-vars val.body)))
          (free-tvars (expr-free-type-vars val.body))
          (free-evars (expr-free-expr-vars val.body)))
       (and (expr-alpha-related-p u.body val.body body-r)
            (expr-alpha-fresh-p u.body val.body body-r
                                (set::insert (ispace-var->name u.param) w-.b))
            (expr-denv-keys-supported-p val.denv body-r
                                        (set::insert (ispace-var->name u.param)
                                                     w-.b))
            (not (set::in (ispace-var-fix u.param)
                          (ispace-var-set-rename-ispace-vars
                           free-ivars r-.dim r-.shape)))
            (expr-denv-alpha-related-via-p u.denv val.denv w-.r w-.denv)
            (expr-denv-keys-within-p val.denv
                                     free-ivars free-tvars free-evars)
            (expr-denv-alpha-avoided-p u.denv val.denv w-.r
                                       free-ivars free-tvars free-evars)))
     :box
     (b* (((unless (expr-value-case new-val :box)) nil)
          ((unless (expr-value-witness-case w :box)) nil)
          ((expr-value-witness-box w-) w))
       (and (equal (expr-value-box->ispace new-val) val.ispace)
            (expr-value-alpha-related-via-p (expr-value-box->array new-val)
                                            val.array w-.array)
            (type-value-alpha-related-via-p (expr-value-box->type new-val)
                                            val.type w-.type)))
     :vector (and (expr-value-case new-val :vector)
                  (expr-value-witness-case w :vector)
                  (expr-value-list-alpha-related-via-p
                   (expr-value-vector->elems new-val)
                   val.elems
                   (expr-value-witness-vector->elems w)))
     :vector-empty (and (expr-value-case new-val :vector-empty)
                        (expr-value-witness-case w :vempty)
                        (equal (expr-value-vector-empty->dims new-val)
                               val.dims)
                        (type-value-alpha-related-via-p
                         (expr-value-vector-empty->elem new-val)
                         val.elem
                         (expr-value-witness-vempty->elem w))))))

  (define expr-value-list-alpha-related-via-p ((new-vals expr-value-listp)
                                               (vals expr-value-listp)
                                               (ws expr-value-witness-listp))
    :returns (yes/no booleanp)
    :parents (uniquify-alpha-relations expr-value-alpha-related-via-p)
    :short "Alpha-relatedness of lists of expression values via witnesses."
    :measure (expr-value-list-count vals)
    (if (endp vals)
        (endp new-vals)
      (and (consp new-vals)
           (consp ws)
           (expr-value-alpha-related-via-p (car new-vals) (car vals) (car ws))
           (expr-value-list-alpha-related-via-p (cdr new-vals) (cdr vals)
                                                (cdr ws)))))

  (define string-expr-value-map-alpha-related-via-p
    ((new-map string-expr-value-mapp)
     (map string-expr-value-mapp)
     (renam string-string-mapp)
     (wmap string-expr-value-witness-mapp))
    :returns (yes/no booleanp)
    :parents (uniquify-alpha-relations expr-value-alpha-related-via-p)
    :short "One-sided pointwise alpha-relatedness of expression-variable
            maps: keys renamed under the in-scope renaming, each value
            related to the original under its own per-entry witness."
    :measure (string-expr-value-map-count map)
    (b* ((map (string-expr-value-map-fix map))
         ((when (omap::emptyp map)) t)
         ((mv var val) (omap::head map))
         (pair (omap::assoc (rename-var-string var renam)
                            (string-expr-value-map-fix new-map)))
         (wpair (omap::assoc var
                             (string-expr-value-witness-map-fix wmap)))
         (w (if wpair (cdr wpair) (expr-value-witness-atom))))
      (and pair
           (expr-value-alpha-related-via-p (cdr pair) val w)
           (string-expr-value-map-alpha-related-via-p new-map
                                                      (omap::tail map)
                                                      renam wmap))))

  (define expr-denv-alpha-related-via-p ((new-denv expr-denvp)
                                         (denv expr-denvp)
                                         (r var-renamings-p)
                                         (dw denv-witness-p))
    :returns (yes/no booleanp)
    :parents (uniquify-alpha-relations expr-value-alpha-related-via-p)
    :short "Alpha-relatedness of expression dynamic environments at an
            in-scope renaming, via per-entry witnesses."
    :measure (expr-denv-count denv)
    (and (type-denv-alpha-related-via-p (expr-denv->tenv new-denv)
                                        (expr-denv->tenv denv)
                                        r
                                        (denv-witness->types dw))
         (string-expr-value-map-alpha-related-via-p
          (expr-denv->exprs new-denv)
          (expr-denv->exprs denv)
          (var-renamings->expr r)
          (denv-witness->exprs dw))))

  (define primop-value-alpha-related-via-p ((new-op primop-valuep)
                                            (op primop-valuep)
                                            (tws type-value-witness-listp)
                                            (ws expr-value-witness-listp))
    :returns (yes/no booleanp)
    :short "Alpha-relatedness of primitive-operation values, via witnesses
            for the embedded type values (in order, from @('tws')) and
            for the embedded expression values (in order, from @('ws'))."
    :long
    (xdoc::topstring
     (xdoc::p
      "The two values must be at the same instantiation stage of the same
       operation, with equal non-value fields (operation codes,
       dimensions, and shapes); each embedded type value and expression
       value of the original is related to the corresponding one of the
       new value via the corresponding witness."))
    :measure (primop-value-count op)
    (b* ((tws (type-value-witness-list-fix tws))
         (ws (expr-value-witness-list-fix ws)))
      (primop-value-case
       op
       :int-unary (and (primop-value-case new-op :int-unary)
                       (equal (primop-value-int-unary->op new-op) op.op))
       :int-binary (and (primop-value-case new-op :int-binary)
                        (equal (primop-value-int-binary->op new-op) op.op))
       :int-binary-x (and (primop-value-case new-op :int-binary-x)
                          (equal (primop-value-int-binary-x->op new-op) op.op)
                          (expr-value-alpha-related-via-p (primop-value-int-binary-x->xval new-op) op.xval (car ws)))
       :int-rel (and (primop-value-case new-op :int-rel)
                     (equal (primop-value-int-rel->op new-op) op.op))
       :int-rel-x (and (primop-value-case new-op :int-rel-x)
                       (equal (primop-value-int-rel-x->op new-op) op.op)
                       (expr-value-alpha-related-via-p (primop-value-int-rel-x->xval new-op) op.xval (car ws)))
       :int-to-float (primop-value-case new-op :int-to-float)
       :int-to-bool (primop-value-case new-op :int-to-bool)
       :float-unary (and (primop-value-case new-op :float-unary)
                         (equal (primop-value-float-unary->op new-op) op.op))
       :float-binary (and (primop-value-case new-op :float-binary)
                          (equal (primop-value-float-binary->op new-op) op.op))
       :float-binary-x (and (primop-value-case new-op :float-binary-x)
                            (equal (primop-value-float-binary-x->op new-op) op.op)
                            (expr-value-alpha-related-via-p (primop-value-float-binary-x->xval new-op) op.xval (car ws)))
       :float-rel (and (primop-value-case new-op :float-rel)
                       (equal (primop-value-float-rel->op new-op) op.op))
       :float-rel-x (and (primop-value-case new-op :float-rel-x)
                         (equal (primop-value-float-rel-x->op new-op) op.op)
                         (expr-value-alpha-related-via-p (primop-value-float-rel-x->xval new-op) op.xval (car ws)))
       :float-truncate (primop-value-case new-op :float-truncate)
       :float-round (primop-value-case new-op :float-round)
       :float-ceiling (primop-value-case new-op :float-ceiling)
       :float-floor (primop-value-case new-op :float-floor)
       :bool-unary (and (primop-value-case new-op :bool-unary)
                        (equal (primop-value-bool-unary->op new-op) op.op))
       :bool-binary (and (primop-value-case new-op :bool-binary)
                         (equal (primop-value-bool-binary->op new-op) op.op))
       :bool-binary-x (and (primop-value-case new-op :bool-binary-x)
                           (equal (primop-value-bool-binary-x->op new-op) op.op)
                           (expr-value-alpha-related-via-p (primop-value-bool-binary-x->xval new-op) op.xval (car ws)))
       :bool-rel (and (primop-value-case new-op :bool-rel)
                      (equal (primop-value-bool-rel->op new-op) op.op))
       :bool-rel-x (and (primop-value-case new-op :bool-rel-x)
                        (equal (primop-value-bool-rel-x->op new-op) op.op)
                        (expr-value-alpha-related-via-p (primop-value-bool-rel-x->xval new-op) op.xval (car ws)))
       :bool-to-int (primop-value-case new-op :bool-to-int)
       :bool-to-float (primop-value-case new-op :bool-to-float)
       :head (primop-value-case new-op :head)
       :head-t (and (primop-value-case new-op :head-t)
                    (type-value-alpha-related-via-p (primop-value-head-t->tval new-op) op.tval (car tws)))
       :head-t-d (and (primop-value-case new-op :head-t-d)
                      (type-value-alpha-related-via-p (primop-value-head-t-d->tval new-op) op.tval (car tws))
                      (equal (primop-value-head-t-d->dval new-op) op.dval))
       :head-t-d-s (and (primop-value-case new-op :head-t-d-s)
                        (type-value-alpha-related-via-p (primop-value-head-t-d-s->tval new-op) op.tval (car tws))
                        (equal (primop-value-head-t-d-s->dval new-op) op.dval)
                        (equal (primop-value-head-t-d-s->sval new-op) op.sval))
       :tail (primop-value-case new-op :tail)
       :tail-t (and (primop-value-case new-op :tail-t)
                    (type-value-alpha-related-via-p (primop-value-tail-t->tval new-op) op.tval (car tws)))
       :tail-t-d (and (primop-value-case new-op :tail-t-d)
                      (type-value-alpha-related-via-p (primop-value-tail-t-d->tval new-op) op.tval (car tws))
                      (equal (primop-value-tail-t-d->dval new-op) op.dval))
       :tail-t-d-s (and (primop-value-case new-op :tail-t-d-s)
                        (type-value-alpha-related-via-p (primop-value-tail-t-d-s->tval new-op) op.tval (car tws))
                        (equal (primop-value-tail-t-d-s->dval new-op) op.dval)
                        (equal (primop-value-tail-t-d-s->sval new-op) op.sval))
       :length (primop-value-case new-op :length)
       :length-t (and (primop-value-case new-op :length-t)
                      (type-value-alpha-related-via-p (primop-value-length-t->tval new-op) op.tval (car tws)))
       :length-t-d (and (primop-value-case new-op :length-t-d)
                        (type-value-alpha-related-via-p (primop-value-length-t-d->tval new-op) op.tval (car tws))
                        (equal (primop-value-length-t-d->dval new-op) op.dval))
       :length-t-d-s (and (primop-value-case new-op :length-t-d-s)
                          (type-value-alpha-related-via-p (primop-value-length-t-d-s->tval new-op) op.tval (car tws))
                          (equal (primop-value-length-t-d-s->dval new-op) op.dval)
                          (equal (primop-value-length-t-d-s->sval new-op) op.sval))
       :append (primop-value-case new-op :append)
       :append-t (and (primop-value-case new-op :append-t)
                      (type-value-alpha-related-via-p (primop-value-append-t->tval new-op) op.tval (car tws)))
       :append-t-m (and (primop-value-case new-op :append-t-m)
                        (type-value-alpha-related-via-p (primop-value-append-t-m->tval new-op) op.tval (car tws))
                        (equal (primop-value-append-t-m->mval new-op) op.mval))
       :append-t-m-n (and (primop-value-case new-op :append-t-m-n)
                          (type-value-alpha-related-via-p (primop-value-append-t-m-n->tval new-op) op.tval (car tws))
                          (equal (primop-value-append-t-m-n->mval new-op) op.mval)
                          (equal (primop-value-append-t-m-n->nval new-op) op.nval))
       :append-t-m-n-s (and (primop-value-case new-op :append-t-m-n-s)
                            (type-value-alpha-related-via-p (primop-value-append-t-m-n-s->tval new-op) op.tval (car tws))
                            (equal (primop-value-append-t-m-n-s->mval new-op) op.mval)
                            (equal (primop-value-append-t-m-n-s->nval new-op) op.nval)
                            (equal (primop-value-append-t-m-n-s->sval new-op) op.sval))
       :append-t-m-n-s-x (and (primop-value-case new-op :append-t-m-n-s-x)
                              (type-value-alpha-related-via-p (primop-value-append-t-m-n-s-x->tval new-op) op.tval (car tws))
                              (equal (primop-value-append-t-m-n-s-x->mval new-op) op.mval)
                              (equal (primop-value-append-t-m-n-s-x->nval new-op) op.nval)
                              (equal (primop-value-append-t-m-n-s-x->sval new-op) op.sval)
                              (expr-value-alpha-related-via-p (primop-value-append-t-m-n-s-x->xval new-op) op.xval (car ws)))
       :reverse (primop-value-case new-op :reverse)
       :reverse-t (and (primop-value-case new-op :reverse-t)
                       (type-value-alpha-related-via-p (primop-value-reverse-t->tval new-op) op.tval (car tws)))
       :reverse-t-d (and (primop-value-case new-op :reverse-t-d)
                         (type-value-alpha-related-via-p (primop-value-reverse-t-d->tval new-op) op.tval (car tws))
                         (equal (primop-value-reverse-t-d->dval new-op) op.dval))
       :reverse-t-d-s (and (primop-value-case new-op :reverse-t-d-s)
                           (type-value-alpha-related-via-p (primop-value-reverse-t-d-s->tval new-op) op.tval (car tws))
                           (equal (primop-value-reverse-t-d-s->dval new-op) op.dval)
                           (equal (primop-value-reverse-t-d-s->sval new-op) op.sval))
       :index (primop-value-case new-op :index)
       :index-t (and (primop-value-case new-op :index-t)
                     (type-value-alpha-related-via-p (primop-value-index-t->tval new-op) op.tval (car tws)))
       :index-t-m (and (primop-value-case new-op :index-t-m)
                       (type-value-alpha-related-via-p (primop-value-index-t-m->tval new-op) op.tval (car tws))
                       (equal (primop-value-index-t-m->mval new-op) op.mval))
       :index-t-m-x (and (primop-value-case new-op :index-t-m-x)
                         (type-value-alpha-related-via-p (primop-value-index-t-m-x->tval new-op) op.tval (car tws))
                         (equal (primop-value-index-t-m-x->mval new-op) op.mval)
                         (expr-value-alpha-related-via-p (primop-value-index-t-m-x->xval new-op) op.xval (car ws)))
       :index2d (primop-value-case new-op :index2d)
       :index2d-t (and (primop-value-case new-op :index2d-t)
                       (type-value-alpha-related-via-p (primop-value-index2d-t->tval new-op) op.tval (car tws)))
       :index2d-t-m (and (primop-value-case new-op :index2d-t-m)
                         (type-value-alpha-related-via-p (primop-value-index2d-t-m->tval new-op) op.tval (car tws))
                         (equal (primop-value-index2d-t-m->mval new-op) op.mval))
       :index2d-t-m-n (and (primop-value-case new-op :index2d-t-m-n)
                           (type-value-alpha-related-via-p (primop-value-index2d-t-m-n->tval new-op) op.tval (car tws))
                           (equal (primop-value-index2d-t-m-n->mval new-op) op.mval)
                           (equal (primop-value-index2d-t-m-n->nval new-op) op.nval))
       :index2d-t-m-n-x (and (primop-value-case new-op :index2d-t-m-n-x)
                             (type-value-alpha-related-via-p (primop-value-index2d-t-m-n-x->tval new-op) op.tval (car tws))
                             (equal (primop-value-index2d-t-m-n-x->mval new-op) op.mval)
                             (equal (primop-value-index2d-t-m-n-x->nval new-op) op.nval)
                             (expr-value-alpha-related-via-p (primop-value-index2d-t-m-n-x->xval new-op) op.xval (car ws)))
       :sum (primop-value-case new-op :sum)
       :sum-s (and (primop-value-case new-op :sum-s)
                   (equal (primop-value-sum-s->sval new-op) op.sval))
       :reshape (primop-value-case new-op :reshape)
       :reshape-t (and (primop-value-case new-op :reshape-t)
                       (type-value-alpha-related-via-p (primop-value-reshape-t->tval new-op) op.tval (car tws)))
       :reshape-t-s1 (and (primop-value-case new-op :reshape-t-s1)
                          (type-value-alpha-related-via-p (primop-value-reshape-t-s1->tval new-op) op.tval (car tws))
                          (equal (primop-value-reshape-t-s1->s1val new-op) op.s1val))
       :reshape-t-s1-s2 (and (primop-value-case new-op :reshape-t-s1-s2)
                             (type-value-alpha-related-via-p (primop-value-reshape-t-s1-s2->tval new-op) op.tval (car tws))
                             (equal (primop-value-reshape-t-s1-s2->s1val new-op) op.s1val)
                             (equal (primop-value-reshape-t-s1-s2->s2val new-op) op.s2val))
       :flatten (primop-value-case new-op :flatten)
       :flatten-t (and (primop-value-case new-op :flatten-t)
                       (type-value-alpha-related-via-p (primop-value-flatten-t->tval new-op) op.tval (car tws)))
       :flatten-t-m (and (primop-value-case new-op :flatten-t-m)
                         (type-value-alpha-related-via-p (primop-value-flatten-t-m->tval new-op) op.tval (car tws))
                         (equal (primop-value-flatten-t-m->mval new-op) op.mval))
       :flatten-t-m-n (and (primop-value-case new-op :flatten-t-m-n)
                           (type-value-alpha-related-via-p (primop-value-flatten-t-m-n->tval new-op) op.tval (car tws))
                           (equal (primop-value-flatten-t-m-n->mval new-op) op.mval)
                           (equal (primop-value-flatten-t-m-n->nval new-op) op.nval))
       :flatten-t-m-n-s (and (primop-value-case new-op :flatten-t-m-n-s)
                             (type-value-alpha-related-via-p (primop-value-flatten-t-m-n-s->tval new-op) op.tval (car tws))
                             (equal (primop-value-flatten-t-m-n-s->mval new-op) op.mval)
                             (equal (primop-value-flatten-t-m-n-s->nval new-op) op.nval)
                             (equal (primop-value-flatten-t-m-n-s->sval new-op) op.sval))
       :transpose2d (primop-value-case new-op :transpose2d)
       :transpose2d-t (and (primop-value-case new-op :transpose2d-t)
                           (type-value-alpha-related-via-p (primop-value-transpose2d-t->tval new-op) op.tval (car tws)))
       :transpose2d-t-m (and (primop-value-case new-op :transpose2d-t-m)
                             (type-value-alpha-related-via-p (primop-value-transpose2d-t-m->tval new-op) op.tval (car tws))
                             (equal (primop-value-transpose2d-t-m->mval new-op) op.mval))
       :transpose2d-t-m-n (and (primop-value-case new-op :transpose2d-t-m-n)
                               (type-value-alpha-related-via-p (primop-value-transpose2d-t-m-n->tval new-op) op.tval (car tws))
                               (equal (primop-value-transpose2d-t-m-n->mval new-op) op.mval)
                               (equal (primop-value-transpose2d-t-m-n->nval new-op) op.nval))
       :iota/static (primop-value-case new-op :iota/static)
       :reduce (primop-value-case new-op :reduce)
       :reduce-t (and (primop-value-case new-op :reduce-t)
                      (type-value-alpha-related-via-p (primop-value-reduce-t->tval new-op) op.tval (car tws)))
       :reduce-t-d (and (primop-value-case new-op :reduce-t-d)
                        (type-value-alpha-related-via-p (primop-value-reduce-t-d->tval new-op) op.tval (car tws))
                        (equal (primop-value-reduce-t-d->dval new-op) op.dval))
       :reduce-t-d-s (and (primop-value-case new-op :reduce-t-d-s)
                          (type-value-alpha-related-via-p (primop-value-reduce-t-d-s->tval new-op) op.tval (car tws))
                          (equal (primop-value-reduce-t-d-s->dval new-op) op.dval)
                          (equal (primop-value-reduce-t-d-s->sval new-op) op.sval))
       :reduce-t-d-s-f (and (primop-value-case new-op :reduce-t-d-s-f)
                            (type-value-alpha-related-via-p (primop-value-reduce-t-d-s-f->tval new-op) op.tval (car tws))
                            (equal (primop-value-reduce-t-d-s-f->dval new-op) op.dval)
                            (equal (primop-value-reduce-t-d-s-f->sval new-op) op.sval)
                            (expr-value-alpha-related-via-p (primop-value-reduce-t-d-s-f->fval new-op) op.fval (car ws)))
       :fold (primop-value-case new-op :fold)
       :fold-t (and (primop-value-case new-op :fold-t)
                    (type-value-alpha-related-via-p (primop-value-fold-t->tval new-op) op.tval (car tws)))
       :fold-t-t2 (and (primop-value-case new-op :fold-t-t2)
                       (type-value-alpha-related-via-p (primop-value-fold-t-t2->tval new-op) op.tval (car tws))
                       (type-value-alpha-related-via-p (primop-value-fold-t-t2->t2val new-op) op.t2val (cadr tws)))
       :fold-t-t2-d (and (primop-value-case new-op :fold-t-t2-d)
                         (type-value-alpha-related-via-p (primop-value-fold-t-t2-d->tval new-op) op.tval (car tws))
                         (type-value-alpha-related-via-p (primop-value-fold-t-t2-d->t2val new-op) op.t2val (cadr tws))
                         (equal (primop-value-fold-t-t2-d->dval new-op) op.dval))
       :fold-t-t2-d-s (and (primop-value-case new-op :fold-t-t2-d-s)
                           (type-value-alpha-related-via-p (primop-value-fold-t-t2-d-s->tval new-op) op.tval (car tws))
                           (type-value-alpha-related-via-p (primop-value-fold-t-t2-d-s->t2val new-op) op.t2val (cadr tws))
                           (equal (primop-value-fold-t-t2-d-s->dval new-op) op.dval)
                           (equal (primop-value-fold-t-t2-d-s->sval new-op) op.sval))
       :fold-t-t2-d-s-s2 (and (primop-value-case new-op :fold-t-t2-d-s-s2)
                              (type-value-alpha-related-via-p (primop-value-fold-t-t2-d-s-s2->tval new-op) op.tval (car tws))
                              (type-value-alpha-related-via-p (primop-value-fold-t-t2-d-s-s2->t2val new-op) op.t2val (cadr tws))
                              (equal (primop-value-fold-t-t2-d-s-s2->dval new-op) op.dval)
                              (equal (primop-value-fold-t-t2-d-s-s2->sval new-op) op.sval)
                              (equal (primop-value-fold-t-t2-d-s-s2->s2val new-op) op.s2val))
       :fold-t-t2-d-s-s2-f (and (primop-value-case new-op :fold-t-t2-d-s-s2-f)
                                (type-value-alpha-related-via-p (primop-value-fold-t-t2-d-s-s2-f->tval new-op) op.tval (car tws))
                                (type-value-alpha-related-via-p (primop-value-fold-t-t2-d-s-s2-f->t2val new-op) op.t2val (cadr tws))
                                (equal (primop-value-fold-t-t2-d-s-s2-f->dval new-op) op.dval)
                                (equal (primop-value-fold-t-t2-d-s-s2-f->sval new-op) op.sval)
                                (equal (primop-value-fold-t-t2-d-s-s2-f->s2val new-op) op.s2val)
                                (expr-value-alpha-related-via-p (primop-value-fold-t-t2-d-s-s2-f->fval new-op) op.fval (car ws)))
       :fold-t-t2-d-s-s2-f-z (and (primop-value-case new-op :fold-t-t2-d-s-s2-f-z)
                                  (type-value-alpha-related-via-p (primop-value-fold-t-t2-d-s-s2-f-z->tval new-op) op.tval (car tws))
                                  (type-value-alpha-related-via-p (primop-value-fold-t-t2-d-s-s2-f-z->t2val new-op) op.t2val (cadr tws))
                                  (equal (primop-value-fold-t-t2-d-s-s2-f-z->dval new-op) op.dval)
                                  (equal (primop-value-fold-t-t2-d-s-s2-f-z->sval new-op) op.sval)
                                  (equal (primop-value-fold-t-t2-d-s-s2-f-z->s2val new-op) op.s2val)
                                  (expr-value-alpha-related-via-p (primop-value-fold-t-t2-d-s-s2-f-z->fval new-op) op.fval (car ws))
                                  (expr-value-alpha-related-via-p (primop-value-fold-t-t2-d-s-s2-f-z->zval new-op) op.zval (cadr ws)))
       :reify-dim (primop-value-case new-op :reify-dim)
       :reify-shape (primop-value-case new-op :reify-shape)
       :iota (primop-value-case new-op :iota)
       :iota-d (and (primop-value-case new-op :iota-d)
                    (equal (primop-value-iota-d->dval new-op) op.dval))
       :trace (primop-value-case new-op :trace)
       :trace-t (and (primop-value-case new-op :trace-t)
                     (type-value-alpha-related-via-p (primop-value-trace-t->tval new-op) op.tval (car tws)))
       :trace-t-r (and (primop-value-case new-op :trace-t-r)
                       (type-value-alpha-related-via-p (primop-value-trace-t-r->tval new-op) op.tval (car tws))
                       (type-value-alpha-related-via-p (primop-value-trace-t-r->rval new-op) op.rval (cadr tws)))
       :trace-t-r-s (and (primop-value-case new-op :trace-t-r-s)
                         (type-value-alpha-related-via-p (primop-value-trace-t-r-s->tval new-op) op.tval (car tws))
                         (type-value-alpha-related-via-p (primop-value-trace-t-r-s->rval new-op) op.rval (cadr tws))
                         (equal (primop-value-trace-t-r-s->sval new-op) op.sval))
       :trace-t-r-s-q (and (primop-value-case new-op :trace-t-r-s-q)
                           (type-value-alpha-related-via-p (primop-value-trace-t-r-s-q->tval new-op) op.tval (car tws))
                           (type-value-alpha-related-via-p (primop-value-trace-t-r-s-q->rval new-op) op.rval (cadr tws))
                           (equal (primop-value-trace-t-r-s-q->sval new-op) op.sval)
                           (equal (primop-value-trace-t-r-s-q->qval new-op) op.qval))
       :trace-t-r-s-q-x (and (primop-value-case new-op :trace-t-r-s-q-x)
                             (type-value-alpha-related-via-p (primop-value-trace-t-r-s-q-x->tval new-op) op.tval (car tws))
                             (type-value-alpha-related-via-p (primop-value-trace-t-r-s-q-x->rval new-op) op.rval (cadr tws))
                             (equal (primop-value-trace-t-r-s-q-x->sval new-op) op.sval)
                             (equal (primop-value-trace-t-r-s-q-x->qval new-op) op.qval)
                             (expr-value-alpha-related-via-p (primop-value-trace-t-r-s-q-x->xval new-op) op.xval (car ws)))
       :undefined (primop-value-case new-op :undefined)
       :undefined-t (and (primop-value-case new-op :undefined-t)
                         (type-value-alpha-related-via-p (primop-value-undefined-t->tval new-op) op.tval (car tws))))))
  :verify-guards nil)

; The existential forms, for theorem statements: two values (or two
; environments at an in-scope renaming) are alpha-equivalent when SOME
; witness relates them.  The evaluator theorems establish these by
; exhibiting explicit witnesses case by case.

(acl2::defun-sk type-value-alpha-equiv-p (new-tval tval)
  (exists (w) (type-value-alpha-related-via-p new-tval tval w)))

(acl2::defun-sk expr-value-alpha-equiv-p (new-val val)
  (exists (w) (expr-value-alpha-related-via-p new-val val w)))

(acl2::defun-sk expr-denv-alpha-equiv-p (new-denv denv r)
  (exists (dw) (expr-denv-alpha-related-via-p new-denv denv r dw)))

; Fixing congruences for the witness-indexed relation cliques (which contain
; no quantified members, so the congruences go through directly).

(fty::deffixequiv-mutual type-value-alpha-related-via-p)

(fty::deffixequiv-mutual expr-value-alpha-related-via-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Consequences of the witness-indexed value relations needed by the main
; induction (UNIQUIFY-EVALUATION).

(defruled type-value-kind-when-type-value-alpha-related-via-p
  (implies (type-value-alpha-related-via-p new-tval tval w)
           (equal (type-value-kind new-tval)
                  (type-value-kind tval)))
  :expand ((type-value-alpha-related-via-p new-tval tval w)))

(defruled expr-value-kind-when-expr-value-alpha-related-via-p
  (implies (expr-value-alpha-related-via-p new-val val w)
           (equal (expr-value-kind new-val)
                  (expr-value-kind val)))
  :expand ((expr-value-alpha-related-via-p new-val val w)))

; The same, guarded against the self-instance (new-val = val, which the
; leaf case of the relation produces by congruence), where it would loop.

(defruled expr-value-kind-when-expr-value-alpha-related-via-p-safe
  (implies (and (expr-value-alpha-related-via-p new-val val w)
                (syntaxp (not (equal new-val val))))
           (equal (expr-value-kind new-val)
                  (expr-value-kind val)))
  :use expr-value-kind-when-expr-value-alpha-related-via-p)

(defruled len-when-expr-value-list-alpha-related-via-p
  (implies (expr-value-list-alpha-related-via-p new-vals vals ws)
           (equal (len new-vals) (len vals)))
  :induct (three-cdrs-induct new-vals vals ws)
  :enable (three-cdrs-induct
           len expr-value-list-alpha-related-via-p))

; Witness-related well-formed values have equal dimensions: the relation
; pairs equal kinds, forces the dimension-bearing components equal, and
; relates vector elements pointwise with equal lengths.  The lambda cases
; contribute no dimensions, so the one-sided environment relation is never
; consulted; both-sides well-formedness is however needed, since the
; dimension checker descends into the captured environments (available in
; the induction from EXPR-VALUE-WFP-OF-EVAL-EXPR).

(defret-mutual check-dims-when-expr-value-alpha-related-via-p
  (defret check-dims-when-expr-value-alpha-related-via-p
    (implies (and yes/no
                  (not (reserrp (check-dims-of-expr-value val)))
                  (not (reserrp (check-dims-of-expr-value new-val))))
             (equal (check-dims-of-expr-value new-val)
                    (check-dims-of-expr-value val)))
    :fn expr-value-alpha-related-via-p)
  (defret check-dims-when-expr-value-list-alpha-related-via-p
    (implies (and yes/no
                  (not (reserrp (check-dims-of-expr-value-list vals)))
                  (not (reserrp (check-dims-of-expr-value-list new-vals))))
             (equal (check-dims-of-expr-value-list new-vals)
                    (check-dims-of-expr-value-list vals)))
    :fn expr-value-list-alpha-related-via-p)
  :mutual-recursion expr-value-alpha-related-via-p
  :skip-others t
  :hints (("Goal"
           :expand ((expr-value-alpha-related-via-p new-val val w)
                    (expr-value-list-alpha-related-via-p new-vals vals ws)
                    (check-dims-of-expr-value val)
                    (check-dims-of-expr-value new-val)
                    (check-dims-of-expr-value-list vals)
                    (check-dims-of-expr-value-list new-vals))
           :in-theory (e/d (len-when-expr-value-list-alpha-related-via-p
                            expr-value-kind-when-expr-value-alpha-related-via-p-safe)
                           (expr-value-alpha-related-via-p
                            expr-value-list-alpha-related-via-p
                            check-dims-of-expr-value
                            check-dims-of-expr-value-list
                            expr-value-groundp
                            expr-value-list-groundp
                            primop-value-groundp
                            string-expr-value-map-groundp
                            expr-denv-groundp)))))

(defruled dims-of-expr-value-when-expr-value-alpha-related-via-p
  (implies (and (expr-value-alpha-related-via-p new-val val w)
                (expr-value-wfp val)
                (expr-value-wfp new-val))
           (equal (dims-of-expr-value new-val)
                  (dims-of-expr-value val)))
  :enable (dims-of-expr-value
           expr-value-wfp
           check-dims-when-expr-value-alpha-related-via-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Support for the closure conjuncts of the value relation in the type
; evaluation theorem below: what the restriction at closure creation
; gives (a bound on the captured keys, and the failure-direction relation
; at the body's free variables), and what the binder's no-capture condition
; gives for the parameter, both for the unary binders and for the n-ary
; ones through their curried bodies.

; ---- generic: restriction bounds keys; disjoint difference

(defruled subset-keys-of-restrict
  (set::subset (omap::keys (omap::restrict s m)) s)
  :enable omap::keys-of-restrict)

; ---- no-capture is anti-monotone in the bound names

(defruled renaming-no-capture-p-when-subset
  (implies (and (renaming-no-capture-p names m)
                (set::subset (string-sfix names1) (string-sfix names)))
           (renaming-no-capture-p names1 m))
  :enable renaming-no-capture-p
  :use ((:instance emptyp-of-intersect-when-subsets
                   (a (string-sfix names1))
                   (a2 (string-sfix names))
                   (b (omap::values (string-string-map-fix m)))
                   (b2 (omap::values (string-string-map-fix m))))))

; ---- restriction preserves the failure-direction relations at variables
;      the restriction keeps (ispace and type layers)

(defruled denv-ispace-vars-avoided-p-of-restrict
  (implies (and (denv-ispace-vars-avoided-p new-ienv ienv
                                            dim-renam shape-renam vars)
                (set::subset (ispace-var-set-fix vars) s))
           (denv-ispace-vars-avoided-p
            (ispace-denv (omap::restrict new-s (ispace-denv->ispaces new-ienv)))
            (ispace-denv (omap::restrict s (ispace-denv->ispaces ienv)))
            dim-renam shape-renam vars))
  :expand ((denv-ispace-vars-avoided-p
            (ispace-denv (omap::restrict new-s (ispace-denv->ispaces new-ienv)))
            (ispace-denv (omap::restrict s (ispace-denv->ispaces ienv)))
            dim-renam shape-renam vars))
  :enable omap::assoc-of-restrict
  :use ((:instance denv-ispace-vars-avoided-p-necc
                   (new-denv new-ienv) (denv ienv)
                   (var (denv-ispace-vars-avoided-p-witness
                         (ispace-denv (omap::restrict
                                       new-s (ispace-denv->ispaces new-ienv)))
                         (ispace-denv (omap::restrict
                                       s (ispace-denv->ispaces ienv)))
                         dim-renam shape-renam vars)))
        (:instance set::subset-in
                   (a (denv-ispace-vars-avoided-p-witness
                       (ispace-denv (omap::restrict
                                     new-s (ispace-denv->ispaces new-ienv)))
                       (ispace-denv (omap::restrict
                                     s (ispace-denv->ispaces ienv)))
                       dim-renam shape-renam vars))
                   (x (ispace-var-set-fix vars))
                   (y s))))

(defruled type-var-map-avoided-p-of-restrict
  (implies (and (type-var-map-avoided-p new-map map atom-renam array-renam vars)
                (type-var-type-value-mapp new-map)
                (type-var-type-value-mapp map)
                (set::subset (type-var-set-fix vars) s))
           (type-var-map-avoided-p (omap::restrict new-s new-map)
                                   (omap::restrict s map)
                                   atom-renam array-renam vars))
  :expand ((type-var-map-avoided-p (omap::restrict new-s new-map)
                                   (omap::restrict s map)
                                   atom-renam array-renam vars))
  :enable omap::assoc-of-restrict
  :use ((:instance type-var-map-avoided-p-necc
                   (var (type-var-map-avoided-p-witness
                         (omap::restrict new-s new-map)
                         (omap::restrict s map)
                         atom-renam array-renam vars)))
        (:instance set::subset-in
                   (a (type-var-map-avoided-p-witness
                       (omap::restrict new-s new-map)
                       (omap::restrict s map)
                       atom-renam array-renam vars))
                   (x (type-var-set-fix vars))
                   (y s))))

(defruled string-expr-value-map-avoided-p-of-restrict
  (implies (and (string-expr-value-map-avoided-p new-map map renam vars)
                (string-expr-value-mapp new-map)
                (string-expr-value-mapp map)
                (set::subset (string-sfix vars) s))
           (string-expr-value-map-avoided-p (omap::restrict new-s new-map)
                                            (omap::restrict s map)
                                            renam vars))
  :expand ((string-expr-value-map-avoided-p (omap::restrict new-s new-map)
                                            (omap::restrict s map)
                                            renam vars))
  :enable omap::assoc-of-restrict
  :use ((:instance string-expr-value-map-avoided-p-necc
                   (var (string-expr-value-map-avoided-p-witness
                         (omap::restrict new-s new-map)
                         (omap::restrict s map)
                         renam vars)))
        (:instance set::subset-in
                   (a (string-expr-value-map-avoided-p-witness
                       (omap::restrict new-s new-map)
                       (omap::restrict s map)
                       renam vars))
                   (x (string-sfix vars))
                   (y s))))

(defruled type-denv-keys-within-p-of-restrict
  (implies (and (ispace-var-ispace-value-mapp ispaces)
                (type-var-type-value-mapp types)
                (set::subset si (ispace-var-set-fix ivars))
                (set::subset st (type-var-set-fix tvars)))
           (type-denv-keys-within-p
            (type-denv (ispace-denv (omap::restrict si ispaces))
                       (omap::restrict st types))
            ivars tvars))
  :enable (type-denv-keys-within-p
           omap::keys-of-restrict)
  :use ((:instance set::subset-transitive
                   (x (omap::keys (omap::restrict si ispaces)))
                   (y si)
                   (z (ispace-var-set-fix ivars)))
        (:instance set::subset-transitive
                   (x (omap::keys (omap::restrict st types)))
                   (y st)
                   (z (type-var-set-fix tvars)))
        (:instance subset-keys-of-restrict (s si) (m ispaces))
        (:instance subset-keys-of-restrict (s st) (m types))))

; ---- free variables of the curried bodies of the n-ary type binders

(defruled delete-of-type-free-ispace-vars-of-sigma-curried-body
  (implies (and (ispace-var-listp params)
                (consp (cdr params)))
           (equal (set::delete (car params)
                               (type-free-ispace-vars
                                (sigma-curried-body params body)))
                  (set::difference (type-free-ispace-vars body)
                                   (set::mergesort params))))
  :enable (sigma-curried-body
           make-type-sigma/sigman
           type-free-ispace-vars
           mergesort-when-consp))

(defruled delete-of-type-free-ispace-vars-of-pi-curried-body
  (implies (and (ispace-var-listp params)
                (consp (cdr params)))
           (equal (set::delete (car params)
                               (type-free-ispace-vars
                                (pi-curried-body params body)))
                  (set::difference (type-free-ispace-vars body)
                                   (set::mergesort params))))
  :enable (pi-curried-body
           make-type-pi/pin
           type-free-ispace-vars
           mergesort-when-consp))

(defruled delete-of-type-free-type-vars-of-forall-curried-body
  (implies (and (type-var-listp params)
                (consp (cdr params)))
           (equal (set::delete (car params)
                               (type-free-type-vars
                                (forall-curried-body params body)))
                  (set::difference (type-free-type-vars body)
                                   (set::mergesort params))))
  :enable (forall-curried-body
           make-type-forall/foralln
           type-free-type-vars
           mergesort-when-consp))

(defruled type-free-type-vars-of-sigma-curried-body
  (equal (type-free-type-vars (sigma-curried-body params body))
         (type-free-type-vars body))
  :enable (sigma-curried-body
           make-type-sigma/sigman
           type-free-type-vars))

(defruled type-free-type-vars-of-pi-curried-body
  (equal (type-free-type-vars (pi-curried-body params body))
         (type-free-type-vars body))
  :enable (pi-curried-body
           make-type-pi/pin
           type-free-type-vars))

(defruled type-free-ispace-vars-of-forall-curried-body
  (equal (type-free-ispace-vars (forall-curried-body params body))
         (type-free-ispace-vars body))
  :enable (forall-curried-body
           make-type-forall/foralln
           type-free-ispace-vars))

; ---- no-capture of the curried bodies: the namespace the binder does not
;      touch passes through; the binder's own namespace reduces the maps
;      by the first parameter and then by the rest, which is by all.

(defruled type-rename-type-vars-no-capture-p-of-sigma-curried-body
  (equal (type-rename-type-vars-no-capture-p (sigma-curried-body params body)
                                             atom-renam array-renam)
         (type-rename-type-vars-no-capture-p body atom-renam array-renam))
  :enable (sigma-curried-body
           make-type-sigma/sigman
           type-rename-type-vars-no-capture-p))

(defruled type-rename-type-vars-no-capture-p-of-pi-curried-body
  (equal (type-rename-type-vars-no-capture-p (pi-curried-body params body)
                                             atom-renam array-renam)
         (type-rename-type-vars-no-capture-p body atom-renam array-renam))
  :enable (pi-curried-body
           make-type-pi/pin
           type-rename-type-vars-no-capture-p))

(defruled type-rename-ispace-vars-no-capture-p-of-forall-curried-body
  (equal (type-rename-ispace-vars-no-capture-p
          (forall-curried-body params body) dim-renam shape-renam)
         (type-rename-ispace-vars-no-capture-p body dim-renam shape-renam))
  :enable (forall-curried-body
           make-type-forall/foralln
           type-rename-ispace-vars-no-capture-p))

(defruledl subset-dim-names-when-subset
  (implies (and (ispace-var-setp a)
                (ispace-var-setp b)
                (set::subset a b))
           (set::subset (mv-nth 0 (dim/shape-names-of-ispace-vars a))
                        (mv-nth 0 (dim/shape-names-of-ispace-vars b))))
  :enable (set::pick-a-point-subset-strategy set::subset-in))

(defruledl subset-shape-names-when-subset
  (implies (and (ispace-var-setp a)
                (ispace-var-setp b)
                (set::subset a b))
           (set::subset (mv-nth 1 (dim/shape-names-of-ispace-vars a))
                        (mv-nth 1 (dim/shape-names-of-ispace-vars b))))
  :enable (set::pick-a-point-subset-strategy set::subset-in))

(defruledl subset-atom-names-when-subset
  (implies (and (type-var-setp a)
                (type-var-setp b)
                (set::subset a b))
           (set::subset (mv-nth 0 (atom/array-names-of-type-vars a))
                        (mv-nth 0 (atom/array-names-of-type-vars b))))
  :enable (set::pick-a-point-subset-strategy set::subset-in))

(defruledl subset-array-names-when-subset
  (implies (and (type-var-setp a)
                (type-var-setp b)
                (set::subset a b))
           (set::subset (mv-nth 1 (atom/array-names-of-type-vars a))
                        (mv-nth 1 (atom/array-names-of-type-vars b))))
  :enable (set::pick-a-point-subset-strategy set::subset-in))

; ---- renaming under maps reduced by bound variables a variable is not among

(defruled rename-var-string-of-delete*
  (equal (rename-var-string name
                            (omap::delete* keys (string-string-map-fix renam)))
         (if (set::in (str-fix name) keys)
             (str-fix name)
           (rename-var-string name renam)))
  :enable (rename-var-string omap::assoc-of-delete*))

(defruled rename-type-var-of-remove-bound-when-not-in
  (implies (and (type-varp var)
                (type-var-setp bound)
                (not (set::in var bound)))
           (b* (((mv & & atom1 array1)
                 (atom/array-rename-remove-bound bound atom-renam array-renam)))
             (equal (rename-type-var var atom1 array1)
                    (rename-type-var var atom-renam array-renam))))
  :enable (rename-type-var
           atom/array-rename-remove-bound
           rename-var-string-of-delete*
           in-of-atom-names-of-type-vars
           in-of-array-names-of-type-vars))

(defruled ispace-var-set-rename-ispace-vars-of-remove-bound-when-disjoint
  (implies (and (ispace-var-setp vars)
                (ispace-var-setp bound)
                (set::emptyp (set::intersect vars bound)))
           (b* (((mv & & dim1 shape1)
                 (dim/shape-rename-remove-bound bound dim-renam shape-renam)))
             (equal (ispace-var-set-rename-ispace-vars vars dim1 shape1)
                    (ispace-var-set-rename-ispace-vars vars
                                                       dim-renam
                                                       shape-renam))))
  :induct (ispace-var-set-rename-ispace-vars vars dim-renam shape-renam)
  :enable (ispace-var-set-rename-ispace-vars
           rename-ispace-var-of-remove-bound-when-not-in)
  :hints (("Subgoal *1/2"
           :use ((:instance not-in-when-disjoint
                            (a (set::head vars)) (x vars) (y bound))
                 (:instance emptyp-of-intersect-when-subsets
                            (a (set::tail vars)) (a2 vars)
                            (b bound) (b2 bound))
                 (:instance set::intersect-symmetric
                            (x vars) (y bound))))))

(defruled type-var-set-rename-type-vars-of-remove-bound-when-disjoint
  (implies (and (type-var-setp vars)
                (type-var-setp bound)
                (set::emptyp (set::intersect vars bound)))
           (b* (((mv & & atom1 array1)
                 (atom/array-rename-remove-bound bound atom-renam array-renam)))
             (equal (type-var-set-rename-type-vars vars atom1 array1)
                    (type-var-set-rename-type-vars vars
                                                   atom-renam
                                                   array-renam))))
  :induct (type-var-set-rename-type-vars vars atom-renam array-renam)
  :enable (type-var-set-rename-type-vars
           rename-type-var-of-remove-bound-when-not-in)
  :hints (("Subgoal *1/2"
           :use ((:instance not-in-when-disjoint
                            (a (set::head vars)) (x vars) (y bound))
                 (:instance emptyp-of-intersect-when-subsets
                            (a (set::tail vars)) (a2 vars)
                            (b bound) (b2 bound))
                 (:instance set::intersect-symmetric
                            (x vars) (y bound))))))

; ---- the sets the parameter lemmas reduce over are disjoint from the parameter

(defruled emptyp-of-intersect-of-delete-with-singleton
  (set::emptyp (set::intersect (set::delete a x) (set::insert a nil)))
  :use ((:instance set::in-head
                   (x (set::intersect (set::delete a x) (set::insert a nil)))))
  :disable set::in-head)

(defruled emptyp-of-intersect-of-difference-with-singleton-of-member
  (implies (member-equal a l)
           (set::emptyp (set::intersect (set::difference x (set::mergesort l))
                                        (set::insert a nil))))
  :use ((:instance set::in-head
                   (x (set::intersect (set::difference x (set::mergesort l))
                                      (set::insert a nil)))))
  :disable set::in-head)

(defruled not-in-image-of-delete-under-param-ispace
  (implies (and (ispace-var-setp vars)
                (ispace-varp var)
                (renaming-no-capture-p
                 (mv-nth 0 (dim/shape-rename-remove-bound (set::insert var nil)
                                                          dim-renam shape-renam))
                 (mv-nth 2 (dim/shape-rename-remove-bound (set::insert var nil)
                                                          dim-renam shape-renam)))
                (renaming-no-capture-p
                 (mv-nth 1 (dim/shape-rename-remove-bound (set::insert var nil)
                                                          dim-renam shape-renam))
                 (mv-nth 3 (dim/shape-rename-remove-bound (set::insert var nil)
                                                          dim-renam shape-renam))))
           (not (set::in var
                         (ispace-var-set-rename-ispace-vars
                          (set::delete var vars)
                          (mv-nth 2 (dim/shape-rename-remove-bound
                                     (set::insert var nil) dim-renam shape-renam))
                          (mv-nth 3 (dim/shape-rename-remove-bound
                                     (set::insert var nil) dim-renam shape-renam))))))
  :use ((:instance ispace-var-set-rename-ispace-vars-of-remove-bound-when-disjoint
                   (vars (set::delete var vars))
                   (bound (set::insert var nil)))
        ispace-var-set-rename-ispace-vars-of-delete
        (:instance emptyp-of-intersect-of-delete-with-singleton
                   (a var) (x vars)))
  :disable (set::intersect-delete-x set::intersect-delete-y))

(defruled not-in-image-of-delete-under-param-type
  (implies (and (type-var-setp vars)
                (type-varp var)
                (renaming-no-capture-p
                 (mv-nth 0 (atom/array-rename-remove-bound (set::insert var nil)
                                                           atom-renam array-renam))
                 (mv-nth 2 (atom/array-rename-remove-bound (set::insert var nil)
                                                           atom-renam array-renam)))
                (renaming-no-capture-p
                 (mv-nth 1 (atom/array-rename-remove-bound (set::insert var nil)
                                                           atom-renam array-renam))
                 (mv-nth 3 (atom/array-rename-remove-bound (set::insert var nil)
                                                           atom-renam array-renam))))
           (not (set::in var
                         (type-var-set-rename-type-vars
                          (set::delete var vars)
                          (mv-nth 2 (atom/array-rename-remove-bound
                                     (set::insert var nil) atom-renam array-renam))
                          (mv-nth 3 (atom/array-rename-remove-bound
                                     (set::insert var nil) atom-renam array-renam))))))
  :use ((:instance type-var-set-rename-type-vars-of-remove-bound-when-disjoint
                   (vars (set::delete var vars))
                   (bound (set::insert var nil)))
        type-var-set-rename-type-vars-of-delete
        (:instance emptyp-of-intersect-of-delete-with-singleton
                   (a var) (x vars)))
  :disable (set::intersect-delete-x set::intersect-delete-y))

(defruled not-in-image-of-difference-under-first-param-ispace
  (implies (and (ispace-var-setp vars)
                (ispace-var-listp params)
                (consp params)
                (renaming-no-capture-p
                 (mv-nth 0 (dim/shape-rename-remove-bound (set::mergesort params)
                                                          dim-renam shape-renam))
                 (mv-nth 2 (dim/shape-rename-remove-bound (set::mergesort params)
                                                          dim-renam shape-renam)))
                (renaming-no-capture-p
                 (mv-nth 1 (dim/shape-rename-remove-bound (set::mergesort params)
                                                          dim-renam shape-renam))
                 (mv-nth 3 (dim/shape-rename-remove-bound (set::mergesort params)
                                                          dim-renam shape-renam))))
           (not (set::in (car params)
                         (ispace-var-set-rename-ispace-vars
                          (set::difference vars (set::mergesort params))
                          (mv-nth 2 (dim/shape-rename-remove-bound
                                     (set::insert (car params) nil)
                                     dim-renam shape-renam))
                          (mv-nth 3 (dim/shape-rename-remove-bound
                                     (set::insert (car params) nil)
                                     dim-renam shape-renam))))))
  :use ((:instance ispace-var-set-rename-ispace-vars-of-remove-bound-when-disjoint
                   (vars (set::difference vars (set::mergesort params)))
                   (bound (set::insert (car params) nil)))
        (:instance ispace-var-set-rename-ispace-vars-of-difference
                   (bound (set::mergesort params)))
        (:instance emptyp-of-intersect-of-difference-with-singleton-of-member
                   (a (car params)) (l params) (x vars)))
  :disable (set::intersect-delete-x set::intersect-delete-y))

(defruled not-in-image-of-difference-under-first-param-type
  (implies (and (type-var-setp vars)
                (type-var-listp params)
                (consp params)
                (renaming-no-capture-p
                 (mv-nth 0 (atom/array-rename-remove-bound (set::mergesort params)
                                                           atom-renam array-renam))
                 (mv-nth 2 (atom/array-rename-remove-bound (set::mergesort params)
                                                           atom-renam array-renam)))
                (renaming-no-capture-p
                 (mv-nth 1 (atom/array-rename-remove-bound (set::mergesort params)
                                                           atom-renam array-renam))
                 (mv-nth 3 (atom/array-rename-remove-bound (set::mergesort params)
                                                           atom-renam array-renam))))
           (not (set::in (car params)
                         (type-var-set-rename-type-vars
                          (set::difference vars (set::mergesort params))
                          (mv-nth 2 (atom/array-rename-remove-bound
                                     (set::insert (car params) nil)
                                     atom-renam array-renam))
                          (mv-nth 3 (atom/array-rename-remove-bound
                                     (set::insert (car params) nil)
                                     atom-renam array-renam))))))
  :use ((:instance type-var-set-rename-type-vars-of-remove-bound-when-disjoint
                   (vars (set::difference vars (set::mergesort params)))
                   (bound (set::insert (car params) nil)))
        (:instance type-var-set-rename-type-vars-of-difference
                   (bound (set::mergesort params)))
        (:instance emptyp-of-intersect-of-difference-with-singleton-of-member
                   (a (car params)) (l params) (x vars)))
  :disable (set::intersect-delete-x set::intersect-delete-y))

; ---- no-capture of the curried bodies in the binder's own namespace

(defruled type-rename-ispace-vars-no-capture-p-of-sigma-curried-body
  (implies (and (ispace-var-listp params)
                (consp (cdr params))
                (renaming-no-capture-p
                 (mv-nth 0 (dim/shape-rename-remove-bound (set::mergesort params)
                                                          dim-renam shape-renam))
                 (mv-nth 2 (dim/shape-rename-remove-bound (set::mergesort params)
                                                          dim-renam shape-renam)))
                (renaming-no-capture-p
                 (mv-nth 1 (dim/shape-rename-remove-bound (set::mergesort params)
                                                          dim-renam shape-renam))
                 (mv-nth 3 (dim/shape-rename-remove-bound (set::mergesort params)
                                                          dim-renam shape-renam)))
                (type-rename-ispace-vars-no-capture-p
                 body
                 (mv-nth 2 (dim/shape-rename-remove-bound (set::mergesort params)
                                                          dim-renam shape-renam))
                 (mv-nth 3 (dim/shape-rename-remove-bound (set::mergesort params)
                                                          dim-renam shape-renam))))
           (type-rename-ispace-vars-no-capture-p
            (sigma-curried-body params body)
            (mv-nth 2 (dim/shape-rename-remove-bound (set::insert (car params) nil)
                                                     dim-renam shape-renam))
            (mv-nth 3 (dim/shape-rename-remove-bound (set::insert (car params) nil)
                                                     dim-renam shape-renam))))
  :enable (sigma-curried-body
           make-type-sigma/sigman
           type-rename-ispace-vars-no-capture-p
           mergesort-when-singleton
           dim/shape-rename-remove-bound
           subset-of-mergesort-of-cdr
           acl2::equal-len-const)
  :use ((:instance dim/shape-rename-remove-bound-of-insert-then-rest
                   (var (car params)) (rest (cdr params)))
        (:instance renaming-no-capture-p-when-subset
                   (names (mv-nth 0 (dim/shape-names-of-ispace-vars
                                     (set::mergesort params))))
                   (names1 (mv-nth 0 (dim/shape-names-of-ispace-vars
                                      (set::mergesort (cdr params)))))
                   (m (omap::delete* (mv-nth 0 (dim/shape-names-of-ispace-vars
                                                (set::mergesort params)))
                                     (string-string-map-fix dim-renam))))
        (:instance renaming-no-capture-p-when-subset
                   (names (mv-nth 1 (dim/shape-names-of-ispace-vars
                                     (set::mergesort params))))
                   (names1 (mv-nth 1 (dim/shape-names-of-ispace-vars
                                      (set::mergesort (cdr params)))))
                   (m (omap::delete* (mv-nth 1 (dim/shape-names-of-ispace-vars
                                                (set::mergesort params)))
                                     (string-string-map-fix shape-renam))))
        (:instance subset-dim-names-when-subset
                   (a (set::mergesort (cdr params))) (b (set::mergesort params)))
        (:instance subset-shape-names-when-subset
                   (a (set::mergesort (cdr params))) (b (set::mergesort params)))))

(defruled type-rename-ispace-vars-no-capture-p-of-pi-curried-body
  (implies (and (ispace-var-listp params)
                (consp (cdr params))
                (renaming-no-capture-p
                 (mv-nth 0 (dim/shape-rename-remove-bound (set::mergesort params)
                                                          dim-renam shape-renam))
                 (mv-nth 2 (dim/shape-rename-remove-bound (set::mergesort params)
                                                          dim-renam shape-renam)))
                (renaming-no-capture-p
                 (mv-nth 1 (dim/shape-rename-remove-bound (set::mergesort params)
                                                          dim-renam shape-renam))
                 (mv-nth 3 (dim/shape-rename-remove-bound (set::mergesort params)
                                                          dim-renam shape-renam)))
                (type-rename-ispace-vars-no-capture-p
                 body
                 (mv-nth 2 (dim/shape-rename-remove-bound (set::mergesort params)
                                                          dim-renam shape-renam))
                 (mv-nth 3 (dim/shape-rename-remove-bound (set::mergesort params)
                                                          dim-renam shape-renam))))
           (type-rename-ispace-vars-no-capture-p
            (pi-curried-body params body)
            (mv-nth 2 (dim/shape-rename-remove-bound (set::insert (car params) nil)
                                                     dim-renam shape-renam))
            (mv-nth 3 (dim/shape-rename-remove-bound (set::insert (car params) nil)
                                                     dim-renam shape-renam))))
  :enable (pi-curried-body
           make-type-pi/pin
           type-rename-ispace-vars-no-capture-p
           mergesort-when-singleton
           dim/shape-rename-remove-bound
           subset-of-mergesort-of-cdr
           acl2::equal-len-const)
  :use ((:instance dim/shape-rename-remove-bound-of-insert-then-rest
                   (var (car params)) (rest (cdr params)))
        (:instance renaming-no-capture-p-when-subset
                   (names (mv-nth 0 (dim/shape-names-of-ispace-vars
                                     (set::mergesort params))))
                   (names1 (mv-nth 0 (dim/shape-names-of-ispace-vars
                                      (set::mergesort (cdr params)))))
                   (m (omap::delete* (mv-nth 0 (dim/shape-names-of-ispace-vars
                                                (set::mergesort params)))
                                     (string-string-map-fix dim-renam))))
        (:instance renaming-no-capture-p-when-subset
                   (names (mv-nth 1 (dim/shape-names-of-ispace-vars
                                     (set::mergesort params))))
                   (names1 (mv-nth 1 (dim/shape-names-of-ispace-vars
                                      (set::mergesort (cdr params)))))
                   (m (omap::delete* (mv-nth 1 (dim/shape-names-of-ispace-vars
                                                (set::mergesort params)))
                                     (string-string-map-fix shape-renam))))
        (:instance subset-dim-names-when-subset
                   (a (set::mergesort (cdr params))) (b (set::mergesort params)))
        (:instance subset-shape-names-when-subset
                   (a (set::mergesort (cdr params))) (b (set::mergesort params)))))

(defruled type-rename-type-vars-no-capture-p-of-forall-curried-body
  (implies (and (type-var-listp params)
                (consp (cdr params))
                (renaming-no-capture-p
                 (mv-nth 0 (atom/array-rename-remove-bound (set::mergesort params)
                                                           atom-renam array-renam))
                 (mv-nth 2 (atom/array-rename-remove-bound (set::mergesort params)
                                                           atom-renam array-renam)))
                (renaming-no-capture-p
                 (mv-nth 1 (atom/array-rename-remove-bound (set::mergesort params)
                                                           atom-renam array-renam))
                 (mv-nth 3 (atom/array-rename-remove-bound (set::mergesort params)
                                                           atom-renam array-renam)))
                (type-rename-type-vars-no-capture-p
                 body
                 (mv-nth 2 (atom/array-rename-remove-bound (set::mergesort params)
                                                           atom-renam array-renam))
                 (mv-nth 3 (atom/array-rename-remove-bound (set::mergesort params)
                                                           atom-renam array-renam))))
           (type-rename-type-vars-no-capture-p
            (forall-curried-body params body)
            (mv-nth 2 (atom/array-rename-remove-bound (set::insert (car params) nil)
                                                      atom-renam array-renam))
            (mv-nth 3 (atom/array-rename-remove-bound (set::insert (car params) nil)
                                                      atom-renam array-renam))))
  :enable (forall-curried-body
           make-type-forall/foralln
           type-rename-type-vars-no-capture-p
           mergesort-when-singleton
           atom/array-rename-remove-bound
           subset-of-mergesort-of-cdr
           acl2::equal-len-const)
  :use ((:instance atom/array-rename-remove-bound-of-insert-then-rest
                   (var (car params)) (rest (cdr params)))
        (:instance renaming-no-capture-p-when-subset
                   (names (mv-nth 0 (atom/array-names-of-type-vars
                                     (set::mergesort params))))
                   (names1 (mv-nth 0 (atom/array-names-of-type-vars
                                      (set::mergesort (cdr params)))))
                   (m (omap::delete* (mv-nth 0 (atom/array-names-of-type-vars
                                                (set::mergesort params)))
                                     (string-string-map-fix atom-renam))))
        (:instance renaming-no-capture-p-when-subset
                   (names (mv-nth 1 (atom/array-names-of-type-vars
                                     (set::mergesort params))))
                   (names1 (mv-nth 1 (atom/array-names-of-type-vars
                                      (set::mergesort (cdr params)))))
                   (m (omap::delete* (mv-nth 1 (atom/array-names-of-type-vars
                                                (set::mergesort params)))
                                     (string-string-map-fix array-renam))))
        (:instance subset-atom-names-when-subset
                   (a (set::mergesort (cdr params))) (b (set::mergesort params)))
        (:instance subset-array-names-when-subset
                   (a (set::mergesort (cdr params))) (b (set::mergesort params)))))

(defruled type-denv-alpha-avoided-p-of-restrict-layers
  (implies (and (denv-ispace-vars-avoided-p (type-denv->ienv new-tenv)
                                            (type-denv->ienv tenv)
                                            (var-renamings->dim r)
                                            (var-renamings->shape r)
                                            ivars)
                (type-var-map-avoided-p (type-denv->types new-tenv)
                                        (type-denv->types tenv)
                                        (var-renamings->atom r)
                                        (var-renamings->array r)
                                        tvars)
                (type-var-type-value-mapp (type-denv->types new-tenv))
                (type-var-type-value-mapp (type-denv->types tenv))
                (set::subset (ispace-var-set-fix ivars) si)
                (set::subset (type-var-set-fix tvars) st))
           (type-denv-alpha-avoided-p
            (type-denv (ispace-denv (omap::restrict
                                     new-si
                                     (ispace-denv->ispaces
                                      (type-denv->ienv new-tenv))))
                       (omap::restrict new-st (type-denv->types new-tenv)))
            (type-denv (ispace-denv (omap::restrict
                                     si
                                     (ispace-denv->ispaces
                                      (type-denv->ienv tenv))))
                       (omap::restrict st (type-denv->types tenv)))
            r ivars tvars))
  :enable (type-denv-alpha-avoided-p
           denv-ispace-vars-avoided-p-of-restrict
           type-var-map-avoided-p-of-restrict))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Evaluation under the alpha relations: the structurally recursive levels.
;
; These are the analogues, for the split environment relations above, of
; the first design's eval-dim/shape/ispace theorems (since removed from
; renaming-evaluation.lisp): given
; the success direction of the ispace-layer relation, and the failure
; direction at the free ispace variables of the AST under evaluation, the
; renamed AST evaluates in the new environment exactly as the original
; does in the old one (errors included).
;
; The AVOIDED-P hypothesis shrinks with the AST in the inductions, so its
; anti-monotonicity in the variable set comes first.

(defthm-eval-dims-flag
  (defthm eval-dim-alpha
    (implies (and (denv-ispace-vars-covered-p new-denv denv
                                              dim-renam shape-renam)
                  (denv-ispace-vars-avoided-p new-denv denv
                                              dim-renam shape-renam
                                              (dim-free-ispace-vars dim)))
             (equal (eval-dim (dim-rename-dim-vars dim dim-renam) new-denv)
                    (eval-dim dim denv)))
    :flag eval-dim)
  (defthm eval-dim-list-alpha
    (implies (and (denv-ispace-vars-covered-p new-denv denv
                                              dim-renam shape-renam)
                  (denv-ispace-vars-avoided-p new-denv denv
                                              dim-renam shape-renam
                                              (dim-list-free-ispace-vars dims)))
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
                       ispace-denv-lookup-ispace
                       dim-free-ispace-vars
                       dim-list-free-ispace-vars
                       denv-ispace-vars-avoided-p-monotone))
   (and acl2::stable-under-simplificationp
        '(:use ((:instance denv-ispace-vars-covered-p-necc
                           (var (ispace-var-dim (dim-var->name dim))))
                (:instance denv-ispace-vars-avoided-p-necc
                           (vars (dim-free-ispace-vars dim))
                           (var (ispace-var-dim (dim-var->name dim)))))))))

(defthm-eval-shapes/ispaces-flag
  (defthm eval-shape-alpha
    (implies (and (denv-ispace-vars-covered-p new-denv denv
                                              dim-renam shape-renam)
                  (denv-ispace-vars-avoided-p new-denv denv
                                              dim-renam shape-renam
                                              (shape-free-ispace-vars shape)))
             (equal (eval-shape (shape-rename-ispace-vars shape
                                                          dim-renam
                                                          shape-renam)
                                new-denv)
                    (eval-shape shape denv)))
    :flag eval-shape)
  (defthm eval-shape-list-alpha
    (implies (and (denv-ispace-vars-covered-p new-denv denv
                                              dim-renam shape-renam)
                  (denv-ispace-vars-avoided-p new-denv denv
                                              dim-renam shape-renam
                                              (shape-list-free-ispace-vars
                                               shapes)))
             (equal (eval-shape-list (shape-list-rename-ispace-vars
                                      shapes dim-renam shape-renam)
                                     new-denv)
                    (eval-shape-list shapes denv)))
    :flag eval-shape-list)
  (defthm eval-ispace-alpha
    (implies (and (denv-ispace-vars-covered-p new-denv denv
                                              dim-renam shape-renam)
                  (denv-ispace-vars-avoided-p new-denv denv
                                              dim-renam shape-renam
                                              (ispace-free-ispace-vars
                                               ispace)))
             (equal (eval-ispace (ispace-rename-ispace-vars ispace
                                                            dim-renam
                                                            shape-renam)
                                 new-denv)
                    (eval-ispace ispace denv)))
    :flag eval-ispace)
  (defthm eval-ispace-list-alpha
    (implies (and (denv-ispace-vars-covered-p new-denv denv
                                              dim-renam shape-renam)
                  (denv-ispace-vars-avoided-p new-denv denv
                                              dim-renam shape-renam
                                              (ispace-list-free-ispace-vars
                                               ispaces)))
             (equal (eval-ispace-list (ispace-list-rename-ispace-vars
                                       ispaces dim-renam shape-renam)
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
                       ispace-denv-lookup-ispace
                       shape-free-ispace-vars
                       shape-list-free-ispace-vars
                       ispace-free-ispace-vars
                       ispace-list-free-ispace-vars
                       denv-ispace-vars-avoided-p-monotone))
   (and acl2::stable-under-simplificationp
        '(:use ((:instance denv-ispace-vars-covered-p-necc
                           (var (ispace-var-shape (shape-var->name shape))))
                (:instance denv-ispace-vars-avoided-p-necc
                           (vars (shape-free-ispace-vars shape))
                           (var (ispace-var-shape
                                 (shape-var->name shape)))))))))

; Type layer: pointwise characterization of the recursive map relation.
;
; The type-variable map relation inside the value-relation clique is
; recursive (a universal quantifier cannot appear there), but its
; preservation proofs are much easier against a universally quantified
; form, where the established witness/refuter technique applies.  So the
; recursive relation is proved equivalent to the pointwise DEFUN-SK form
; below, and the preservation lemmas (the image-form extension lemmas of
; UNIQUIFY-EVALUATION) are carried out at the pointwise level, converting
; to and from the recursive form at the boundaries.

(acl2::defun-sk type-var-type-value-map-covered-p (new-map map r wmap)
  (forall (var)
          (implies
           (and (type-varp var)
                (omap::assoc var (type-var-type-value-map-fix map)))
           (b* (((var-renamings r-) r)
                (pair (omap::assoc (rename-type-var var r-.atom r-.array)
                                   (type-var-type-value-map-fix new-map)))
                (wpair (omap::assoc var
                                    (type-var-type-value-witness-map-fix
                                     wmap)))
                (w (if wpair (cdr wpair) (type-value-witness-leaf))))
             (and pair
                  (type-value-alpha-related-via-p
                   (cdr pair)
                   (cdr (omap::assoc var
                                     (type-var-type-value-map-fix map)))
                   w)))))
  :rewrite :direct)

(in-theory (disable type-var-type-value-map-covered-p))

(defruled type-var-type-value-map-alpha-related-via-p-implies-check
  (implies (and (type-var-type-value-map-alpha-related-via-p
                 new-map map r wmap)
                (type-varp var)
                (omap::assoc var (type-var-type-value-map-fix map)))
           (b* (((var-renamings r-) r)
                (pair (omap::assoc (rename-type-var var r-.atom r-.array)
                                   (type-var-type-value-map-fix new-map)))
                (wpair (omap::assoc var
                                    (type-var-type-value-witness-map-fix
                                     wmap)))
                (w (if wpair (cdr wpair) (type-value-witness-leaf))))
             (and pair
                  (type-value-alpha-related-via-p
                   (cdr pair)
                   (cdr (omap::assoc var
                                     (type-var-type-value-map-fix map)))
                   w))))
  :induct (omap::size map)
  :expand ((type-var-type-value-map-alpha-related-via-p new-map map r wmap))
  :enable (omap::size
           omap::assoc))

(defruled type-var-type-value-map-covered-p-when-alpha-related-via-p
  (implies (type-var-type-value-map-alpha-related-via-p new-map map r wmap)
           (type-var-type-value-map-covered-p new-map map r wmap))
  :expand ((type-var-type-value-map-covered-p new-map map r wmap))
  :use ((:instance type-var-type-value-map-alpha-related-via-p-implies-check
                   (var (type-var-type-value-map-covered-p-witness
                         new-map map r wmap)))))

(defruled type-var-type-value-map-covered-p-of-tail
  (implies (type-var-type-value-map-covered-p new-map map r wmap)
           (type-var-type-value-map-covered-p
            new-map
            (omap::tail (type-var-type-value-map-fix map))
            r wmap))
  :expand ((type-var-type-value-map-covered-p
            new-map
            (omap::tail (type-var-type-value-map-fix map))
            r wmap))
  :enable (assoc-when-assoc-of-tail)
  :use ((:instance type-var-type-value-map-covered-p-necc
                   (var (type-var-type-value-map-covered-p-witness
                         new-map
                         (omap::tail (type-var-type-value-map-fix map))
                         r wmap)))
        (:instance omap::assoc-when-assoc-tail
                   (omap::key (type-var-type-value-map-covered-p-witness
                               new-map
                               (omap::tail
                                (type-var-type-value-map-fix map))
                               r wmap))
                   (omap::map (type-var-type-value-map-fix map)))))

(defruled type-var-type-value-map-covered-p-of-tail-mapp
  (implies (and (type-var-type-value-mapp map)
                (type-var-type-value-map-covered-p new-map map r wmap))
           (type-var-type-value-map-covered-p new-map (omap::tail map)
                                              r wmap))
  :use type-var-type-value-map-covered-p-of-tail
  :disable type-var-type-value-map-covered-p-of-tail)

(defruled type-var-type-value-map-alpha-related-via-p-when-covered-p
  (implies (type-var-type-value-map-covered-p new-map map r wmap)
           (type-var-type-value-map-alpha-related-via-p
            new-map map r wmap))
  :induct (omap::size map)
  :expand ((type-var-type-value-map-alpha-related-via-p new-map map r wmap))
  :enable (omap::size
           type-var-type-value-map-covered-p-of-tail
           type-var-type-value-map-covered-p-of-tail-mapp)
  :disable type-var-type-value-map-covered-p
  :hints ((and acl2::stable-under-simplificationp
               '(:use ((:instance type-var-type-value-map-covered-p-necc
                                  (var (mv-nth 0
                                               (omap::head
                                                (type-var-type-value-map-fix
                                                 map)))))
                       (:instance omap::assoc-of-head
                                  (omap::map
                                   (type-var-type-value-map-fix map))))))))

; Expression layer: pointwise characterization, mirroring the type layer
; (simpler: string keys, no kind dispatch).

(acl2::defun-sk string-expr-value-map-covered-p (new-map map renam wmap)
  (forall (var)
          (implies
           (and (stringp var)
                (omap::assoc var (string-expr-value-map-fix map)))
           (b* ((pair (omap::assoc (rename-var-string var renam)
                                   (string-expr-value-map-fix new-map)))
                (wpair (omap::assoc var
                                    (string-expr-value-witness-map-fix
                                     wmap)))
                (w (if wpair (cdr wpair) (expr-value-witness-atom))))
             (and pair
                  (expr-value-alpha-related-via-p
                   (cdr pair)
                   (cdr (omap::assoc var
                                     (string-expr-value-map-fix map)))
                   w)))))
  :rewrite :direct)

(in-theory (disable string-expr-value-map-covered-p))

(defruled string-expr-value-map-alpha-related-via-p-implies-check
  (implies (and (string-expr-value-map-alpha-related-via-p
                 new-map map renam wmap)
                (stringp var)
                (omap::assoc var (string-expr-value-map-fix map)))
           (b* ((pair (omap::assoc (rename-var-string var renam)
                                   (string-expr-value-map-fix new-map)))
                (wpair (omap::assoc var
                                    (string-expr-value-witness-map-fix
                                     wmap)))
                (w (if wpair (cdr wpair) (expr-value-witness-atom))))
             (and pair
                  (expr-value-alpha-related-via-p
                   (cdr pair)
                   (cdr (omap::assoc var
                                     (string-expr-value-map-fix map)))
                   w))))
  :induct (omap::size map)
  :expand ((string-expr-value-map-alpha-related-via-p new-map map renam wmap))
  :enable (omap::size
           omap::assoc))

(defruled string-expr-value-map-covered-p-when-alpha-related-via-p
  (implies (string-expr-value-map-alpha-related-via-p new-map map renam wmap)
           (string-expr-value-map-covered-p new-map map renam wmap))
  :expand ((string-expr-value-map-covered-p new-map map renam wmap))
  :use ((:instance string-expr-value-map-alpha-related-via-p-implies-check
                   (var (string-expr-value-map-covered-p-witness
                         new-map map renam wmap)))))

(defruled string-expr-value-map-covered-p-of-tail
  (implies (string-expr-value-map-covered-p new-map map renam wmap)
           (string-expr-value-map-covered-p
            new-map
            (omap::tail (string-expr-value-map-fix map))
            renam wmap))
  :expand ((string-expr-value-map-covered-p
            new-map
            (omap::tail (string-expr-value-map-fix map))
            renam wmap))
  :enable (assoc-when-assoc-of-tail
           string-expr-value-map-covered-p)
  :use ((:instance string-expr-value-map-covered-p-necc
                   (var (string-expr-value-map-covered-p-witness
                         new-map
                         (omap::tail (string-expr-value-map-fix map))
                         renam wmap)))
        (:instance omap::assoc-when-assoc-tail
                   (omap::key (string-expr-value-map-covered-p-witness
                               new-map
                               (omap::tail
                                (string-expr-value-map-fix map))
                               renam wmap))
                   (omap::map (string-expr-value-map-fix map)))))

(defruled string-expr-value-map-covered-p-of-tail-mapp
  (implies (and (string-expr-value-mapp map)
                (string-expr-value-map-covered-p new-map map renam wmap))
           (string-expr-value-map-covered-p new-map (omap::tail map)
                                            renam wmap))
  :use string-expr-value-map-covered-p-of-tail
  :disable string-expr-value-map-covered-p-of-tail)

(defruled string-expr-value-map-alpha-related-via-p-when-covered-p
  (implies (string-expr-value-map-covered-p new-map map renam wmap)
           (string-expr-value-map-alpha-related-via-p
            new-map map renam wmap))
  :induct (omap::size map)
  :expand ((string-expr-value-map-alpha-related-via-p new-map map renam wmap))
  :enable (omap::size
           string-expr-value-map-covered-p-of-tail
           string-expr-value-map-covered-p-of-tail-mapp)
  :hints ((and acl2::stable-under-simplificationp
               '(:use ((:instance string-expr-value-map-covered-p-necc
                                  (var (mv-nth 0
                                               (omap::head
                                                (string-expr-value-map-fix
                                                 map)))))
                       (:instance omap::assoc-of-head
                                  (omap::map
                                   (string-expr-value-map-fix map))))))))

; The unfolding of renaming under an extension (the preservation of the
; pointwise relation under the binder extension is in UNIQUIFY-EVALUATION,
; in image form).

(defruled rename-var-string-of-extend-renaming
  (equal (rename-var-string x (extend-renaming n n2 renam))
         (if (equal (str-fix x) (str-fix n))
             (str-fix n2)
           (rename-var-string x renam)))
  :enable (rename-var-string
           extend-renaming
           omap::assoc-of-delete))

; Restriction lemmas, for closure creation: restricting both environments
; preserves the pointwise relations, provided the new-side restriction
; set includes the renaming-image of the old-side one.  (The image
; inclusions are discharged from the free-variable correspondence of
; alpha-related ASTs, proved below for the three namespaces from the
; no-capture conjuncts of the freshness companion.)

(defruled in-of-rename-var-string-of-rename-var-string-set
  (implies (set::in x (string-sfix vars))
           (set::in (rename-var-string x renam)
                    (rename-var-string-set vars renam)))
  :induct (rename-var-string-set vars renam)
  :enable (rename-var-string-set
           acl2::emptyp-of-string-sfix))

(defruled string-expr-value-map-covered-p-of-restrict
  (implies (and (string-expr-value-map-covered-p new-map map renam wmap)
                (string-setp vars)
                (string-setp new-vars)
                (set::subset (rename-var-string-set vars renam) new-vars))
           (string-expr-value-map-covered-p
            (omap::restrict new-vars (string-expr-value-map-fix new-map))
            (omap::restrict vars (string-expr-value-map-fix map))
            renam wmap))
  :enable (string-expr-value-map-covered-p
           omap::assoc-of-restrict
           in-of-rename-var-string-of-rename-var-string-set)
  :expand ((string-expr-value-map-covered-p
            (omap::restrict new-vars (string-expr-value-map-fix new-map))
            (omap::restrict vars (string-expr-value-map-fix map))
            renam wmap))
  :use ((:instance string-expr-value-map-covered-p-necc
                   (var (string-expr-value-map-covered-p-witness
                         (omap::restrict new-vars
                                         (string-expr-value-map-fix
                                          new-map))
                         (omap::restrict vars
                                         (string-expr-value-map-fix map))
                         renam wmap)))
        (:instance in-of-rename-var-string-of-rename-var-string-set
                   (x (string-expr-value-map-covered-p-witness
                       (omap::restrict new-vars
                                       (string-expr-value-map-fix new-map))
                       (omap::restrict vars
                                       (string-expr-value-map-fix map))
                       renam wmap)))
        (:instance set::subset-in-2
                   (x (rename-var-string-set vars renam))
                   (y new-vars)
                   (a (rename-var-string
                       (string-expr-value-map-covered-p-witness
                        (omap::restrict new-vars
                                        (string-expr-value-map-fix new-map))
                        (omap::restrict vars
                                        (string-expr-value-map-fix map))
                        renam wmap)
                       renam)))))

(defruled type-var-type-value-map-covered-p-of-restrict
  (implies (and (type-var-type-value-map-covered-p new-map map r wmap)
                (type-var-setp vars)
                (type-var-setp new-vars)
                (set::subset (type-var-set-rename-type-vars
                              vars
                              (var-renamings->atom r)
                              (var-renamings->array r))
                             new-vars))
           (type-var-type-value-map-covered-p
            (omap::restrict new-vars (type-var-type-value-map-fix new-map))
            (omap::restrict vars (type-var-type-value-map-fix map))
            r wmap))
  :enable (type-var-type-value-map-covered-p
           omap::assoc-of-restrict)
  :expand ((type-var-type-value-map-covered-p
            (omap::restrict new-vars (type-var-type-value-map-fix new-map))
            (omap::restrict vars (type-var-type-value-map-fix map))
            r wmap))
  :use ((:instance type-var-type-value-map-covered-p-necc
                   (var (type-var-type-value-map-covered-p-witness
                         (omap::restrict new-vars
                                         (type-var-type-value-map-fix
                                          new-map))
                         (omap::restrict vars
                                         (type-var-type-value-map-fix map))
                         r wmap)))
        (:instance in-of-rename-type-var-of-type-var-set-rename-type-vars
                   (var (type-var-type-value-map-covered-p-witness
                         (omap::restrict new-vars
                                         (type-var-type-value-map-fix
                                          new-map))
                         (omap::restrict vars
                                         (type-var-type-value-map-fix map))
                         r wmap))
                   (vars vars)
                   (atom-renam (var-renamings->atom r))
                   (array-renam (var-renamings->array r)))
        (:instance set::subset-in-2
                   (x (type-var-set-rename-type-vars
                       vars
                       (var-renamings->atom r)
                       (var-renamings->array r)))
                   (y new-vars)
                   (a (rename-type-var
                       (type-var-type-value-map-covered-p-witness
                        (omap::restrict new-vars
                                        (type-var-type-value-map-fix
                                         new-map))
                        (omap::restrict vars
                                        (type-var-type-value-map-fix map))
                        r wmap)
                       (var-renamings->atom r)
                       (var-renamings->array r))))))

; Witness for nested function type values, and the corresponding
; congruence of the witness relation with the nesting (used by the
; :funn case of the type evaluation theorem).

(define nest-function-type-value-witnesses
  ((in-ws type-value-witness-listp)
   (out-w type-value-witness-p))
  :returns (w type-value-witness-p)
  :short "Witness for a nested function type value built by
          @(tsee nest-function-type-values), from witnesses for the input
          type values and the output type value."
  (cond ((endp in-ws) (type-value-witness-fix out-w))
        (t (type-value-witness-fun
            (car in-ws)
            (nest-function-type-value-witnesses (cdr in-ws) out-w)))))

(defruled type-value-alpha-related-via-p-of-nest-function-type-values
  (implies (and (type-value-list-alpha-related-via-p new-in-tvals in-tvals
                                                     in-ws)
                (equal (len in-ws) (len in-tvals))
                (type-value-alpha-related-via-p new-out-tval out-tval
                                                out-w))
           (type-value-alpha-related-via-p
            (nest-function-type-values new-in-tvals new-out-tval)
            (nest-function-type-values in-tvals out-tval)
            (nest-function-type-value-witnesses in-ws out-w)))
  :induct (three-cdrs-induct new-in-tvals in-tvals in-ws)
  :enable (three-cdrs-induct
           nest-function-type-values
           nest-function-type-value-witnesses
           type-value-list-alpha-related-via-p
           len)
  :expand ((:free (new-tval tval w)
            (type-value-alpha-related-via-p (type-value-fun
                                             (car new-in-tvals)
                                             new-tval)
                                            (type-value-fun (car in-tvals)
                                                            tval)
                                            w))))

; Anti-monotonicity of the type-variable failure-direction relation in
; the variable set, mirroring DENV-ISPACE-VARS-AVOIDED-P-MONOTONE.

; The witness constructions for the evaluation of types: they mirror the
; case structure of EVAL-TYPE, so that the preservation theorem below is
; quantifier-free (the witness for each evaluation result is constructed,
; not asserted to exist).  At a variable the witness is the environment
; witness map's entry (the map relation's default LEAF if absent); at
; composite types the witness is built from the sub-witnesses; at binder
; types (which evaluate to closures) it is the closure witness carrying
; the current renamings and the environment witness map (the captured
; environments are restrictions, and the map relation only consults the
; witness map at the old environment's keys, so no restriction of the
; witness map is needed).

(defines eval-type-witnesses
  :verify-guards nil
  (define eval-type-witness ((ty typep)
                             (r var-renamings-p)
                             (wmap type-var-type-value-witness-mapp))
    :returns (w type-value-witness-p)
    :parents (uniquify-alpha-relations)
    :short "Witness for the alpha-relatedness of the evaluations of a
            type and its renaming."
    (type-case
     ty
     :var (b* ((wpair (omap::assoc ty.var
                                   (type-var-type-value-witness-map-fix
                                    wmap))))
            (if wpair
                (cdr wpair)
              (type-value-witness-leaf)))
     :base (type-value-witness-leaf)
     :array (type-value-witness-array (eval-type-witness ty.elem r wmap))
     :bracket (type-value-witness-array (eval-type-witness ty.elem r wmap))
     :fun (type-value-witness-fun (eval-type-witness ty.in r wmap)
                                  (eval-type-witness ty.out r wmap))
     :funn (nest-function-type-value-witnesses
            (eval-type-witness-list ty.in r wmap)
            (eval-type-witness ty.out r wmap))
     :forall (type-value-witness-closure r wmap)
     :foralln (type-value-witness-closure r wmap)
     :pi (type-value-witness-closure r wmap)
     :pin (type-value-witness-closure r wmap)
     :sigma (type-value-witness-closure r wmap)
     :sigman (type-value-witness-closure r wmap))
    :measure (type-count ty))
  (define eval-type-witness-list ((tys type-listp)
                                  (r var-renamings-p)
                                  (wmap type-var-type-value-witness-mapp))
    :returns (ws type-value-witness-listp)
    :parents (uniquify-alpha-relations)
    :short "Witnesses for the alpha-relatedness of the evaluations of a
            list of types and its renaming."
    (if (endp tys)
        nil
      (cons (eval-type-witness (car tys) r wmap)
            (eval-type-witness-list (cdr tys) r wmap)))
    :measure (type-list-count tys)
    ///
    (defret len-of-eval-type-witness-list
      (equal (len ws) (len tys))
      :hints (("Goal" :induct (len tys) :in-theory (enable len)))))
  ///
  (fty::deffixequiv-mutual eval-type-witnesses))

; Fix-free variant of the type-variable-map restriction lemma: the
; fix-wrapped conclusion of the original never matches goal terms whose
; fixes have already been rewritten away (the maps there are accessors,
; known to be well-typed).

(defruled type-var-type-value-map-covered-p-of-restrict-mapp
  (implies (and (type-var-type-value-mapp new-map)
                (type-var-type-value-mapp map)
                (type-var-type-value-map-covered-p new-map map r wmap)
                (type-var-setp vars)
                (type-var-setp new-vars)
                (set::subset (type-var-set-rename-type-vars
                              vars
                              (var-renamings->atom r)
                              (var-renamings->array r))
                             new-vars))
           (type-var-type-value-map-covered-p
            (omap::restrict new-vars new-map)
            (omap::restrict vars map)
            r wmap))
  :use type-var-type-value-map-covered-p-of-restrict
  :disable type-var-type-value-map-covered-p-of-restrict)

; The witness-constructing evaluation theorem for types: the renaming of a
; type evaluates in the related environment with the same error behavior
; (equal errors, in fact, since the OK binder propagates errors
; unchanged) as the type does in the original environment; on success the
; two type values are alpha-related via the constructed witness.

(defthm-eval-types-flag
  (defthm eval-type-alpha
    (implies
     (and (type-denv-alpha-related-via-p new-denv denv r wmap)
          (denv-ispace-vars-avoided-p (type-denv->ienv new-denv)
                                      (type-denv->ienv denv)
                                      (var-renamings->dim r)
                                      (var-renamings->shape r)
                                      (type-free-ispace-vars type))
          (type-var-map-avoided-p (type-denv->types new-denv)
                                  (type-denv->types denv)
                                  (var-renamings->atom r)
                                  (var-renamings->array r)
                                  (type-free-type-vars type))
          (type-rename-ispace-vars-no-capture-p type
                                                (var-renamings->dim r)
                                                (var-renamings->shape r))
          (type-rename-type-vars-no-capture-p
           (type-rename-ispace-vars type
                                    (var-renamings->dim r)
                                    (var-renamings->shape r))
           (var-renamings->atom r)
           (var-renamings->array r)))
     (and (equal (reserrp (eval-type (type-rename-all-vars type r)
                                     new-denv))
                 (reserrp (eval-type type denv)))
          (implies (reserrp (eval-type type denv))
                   (equal (eval-type (type-rename-all-vars type r)
                                     new-denv)
                          (eval-type type denv)))
          (implies (not (reserrp (eval-type type denv)))
                   (type-value-alpha-related-via-p
                    (eval-type (type-rename-all-vars type r) new-denv)
                    (eval-type type denv)
                    (eval-type-witness type r wmap)))))
    :flag eval-type)
  (defthm eval-type-list-alpha
    (implies
     (and (type-denv-alpha-related-via-p new-denv denv r wmap)
          (denv-ispace-vars-avoided-p (type-denv->ienv new-denv)
                                      (type-denv->ienv denv)
                                      (var-renamings->dim r)
                                      (var-renamings->shape r)
                                      (type-list-free-ispace-vars types))
          (type-var-map-avoided-p (type-denv->types new-denv)
                                  (type-denv->types denv)
                                  (var-renamings->atom r)
                                  (var-renamings->array r)
                                  (type-list-free-type-vars types))
          (type-list-rename-ispace-vars-no-capture-p
           types
           (var-renamings->dim r)
           (var-renamings->shape r))
          (type-list-rename-type-vars-no-capture-p
           (type-list-rename-ispace-vars types
                                         (var-renamings->dim r)
                                         (var-renamings->shape r))
           (var-renamings->atom r)
           (var-renamings->array r)))
     (and (equal (reserrp (eval-type-list (type-list-rename-all-vars
                                           types r)
                                          new-denv))
                 (reserrp (eval-type-list types denv)))
          (implies (reserrp (eval-type-list types denv))
                   (equal (eval-type-list (type-list-rename-all-vars
                                           types r)
                                          new-denv)
                          (eval-type-list types denv)))
          (implies (not (reserrp (eval-type-list types denv)))
                   (type-value-list-alpha-related-via-p
                    (eval-type-list (type-list-rename-all-vars types r)
                                    new-denv)
                    (eval-type-list types denv)
                    (eval-type-witness-list types r wmap)))))
    :flag eval-type-list)
  :hints
  (("Goal"
    :in-theory
    (e/d (eval-type
          eval-type-list
          type-rename-all-vars
          type-list-rename-all-vars
          type-rename-ispace-vars
          type-list-rename-ispace-vars
          type-rename-type-vars
          type-list-rename-type-vars
          type-rename-ispace-vars-no-capture-p
          type-list-rename-ispace-vars-no-capture-p
          type-rename-type-vars-no-capture-p
          type-list-rename-type-vars-no-capture-p
          rename-type-var
          rename-var-string
          type-denv-lookup-type
          type-denv-restrict
          ispace-denv-restrict
          type-free-ispace-vars
          type-list-free-ispace-vars
          type-free-type-vars
          type-list-free-type-vars
          ispace-var-set-rename-ispace-vars-of-difference
          ispace-var-set-rename-ispace-vars-of-delete
          type-var-set-rename-type-vars-of-difference
          type-var-set-rename-type-vars-of-delete
          denv-ispace-vars-avoided-p-monotone
          type-var-map-avoided-p-monotone
          denv-ispace-vars-covered-p-of-restrict
          type-var-type-value-map-covered-p-of-restrict
          type-var-type-value-map-covered-p-of-restrict-mapp
          type-var-type-value-map-covered-p-when-alpha-related-via-p
          type-var-type-value-map-alpha-related-via-p-when-covered-p
          type-value-alpha-related-via-p-of-nest-function-type-values
          type-denv-alpha-related-via-p
          ; The closure conjuncts of the strengthened value relation: the
          ; no-capture of the parameter, the freshness of the (curried)
          ; body, and the key bound and failure-direction relation of the
          ; restricted captured environments.
          type-fresh-ok
          not-in-image-of-delete-under-param-ispace
          not-in-image-of-delete-under-param-type
          not-in-image-of-difference-under-first-param-ispace
          not-in-image-of-difference-under-first-param-type
          delete-of-type-free-ispace-vars-of-sigma-curried-body
          delete-of-type-free-ispace-vars-of-pi-curried-body
          delete-of-type-free-type-vars-of-forall-curried-body
          type-free-type-vars-of-sigma-curried-body
          type-free-type-vars-of-pi-curried-body
          type-free-ispace-vars-of-forall-curried-body
          type-rename-type-vars-no-capture-p-of-sigma-curried-body
          type-rename-type-vars-no-capture-p-of-pi-curried-body
          type-rename-ispace-vars-no-capture-p-of-forall-curried-body
          type-rename-ispace-vars-no-capture-p-of-sigma-curried-body
          type-rename-ispace-vars-no-capture-p-of-pi-curried-body
          type-rename-type-vars-no-capture-p-of-forall-curried-body
          type-denv-keys-within-p-of-restrict
          type-denv-alpha-avoided-p-of-restrict-layers
          eval-type-witness
          eval-type-witness-list
          not-reserrp-when-type-valuep
          not-reserrp-when-type-value-listp
          type-valuep-when-result-not-error
          type-value-listp-when-result-not-error
          ; Turn the length conditions on the parameters of the n-ary
          ; binder cases into CONSP conditions, without which
          ; (TYPE-VAR-FIX (CAR PARAMS)) does not collapse and the
          ; curried-body commutation rules of RENAMING-EVALUATION do not
          ; match.  For all three n-ary binders the length condition is no
          ; longer tested by EVAL-TYPE (it is implied by the requirement on
          ; the product), so it must come from the accessor's
          ; type-prescription instead.  This mirrors the hint of
          ; EVAL-TYPE-OF-TYPE-RENAME-TYPE-VARS.
          acl2::lt-len-const
          acl2::equal-len-const
          consp-of-cdr-of-type-foralln->params
          consp-of-cdr-of-type-pin->params
          consp-of-cdr-of-type-sigman->params
          ; The base case's leaf witness now requires groundness.
          type-value-groundp-of-type-value-base)
         (set::mergesort-set-identity
          set::delete-nonmember-cancel
          type-value-alpha-related-via-p
          type-value-list-alpha-related-via-p
          type-var-type-value-map-alpha-related-via-p))
    :expand ((type-rename-ispace-vars type
                                      (var-renamings->dim r)
                                      (var-renamings->shape r))
             (type-list-rename-ispace-vars types
                                           (var-renamings->dim r)
                                           (var-renamings->shape r))
             (:free (new-tval w x)
              (type-value-alpha-related-via-p new-tval
                                              (type-value-base x)
                                              w))
             (:free (new-tval w elem dims)
              (type-value-alpha-related-via-p new-tval
                                              (type-value-array elem dims)
                                              w))
             (:free (new-tval w in out)
              (type-value-alpha-related-via-p new-tval
                                              (type-value-fun in out)
                                              w))
             (:free (new-tval w param body cdenv)
              (type-value-alpha-related-via-p new-tval
                                              (type-value-forall param
                                                                 body
                                                                 cdenv)
                                              w))
             (:free (new-tval w param body cdenv)
              (type-value-alpha-related-via-p new-tval
                                              (type-value-pi param
                                                             body
                                                             cdenv)
                                              w))
             (:free (new-tval w param body cdenv)
              (type-value-alpha-related-via-p new-tval
                                              (type-value-sigma param
                                                                body
                                                                cdenv)
                                              w))
             (:free (new-tvals ws)
              (type-value-list-alpha-related-via-p new-tvals nil ws))
             (:free (new-tvals tval tvals ws)
              (type-value-list-alpha-related-via-p new-tvals
                                                   (cons tval tvals)
                                                   ws))))
   (and acl2::stable-under-simplificationp
        '(:use
          ((:instance
            type-var-type-value-map-alpha-related-via-p-implies-check
            (new-map (type-denv->types new-denv))
            (map (type-denv->types denv))
            (var (type-var->var type)))
           (:instance type-var-map-avoided-p-necc
                      (new-map (type-denv->types new-denv))
                      (map (type-denv->types denv))
                      (atom-renam (var-renamings->atom r))
                      (array-renam (var-renamings->array r))
                      (vars (type-free-type-vars type))
                      (var (type-var->var type))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Support layer for the free-variables correspondence: pointwise
; behavior of the renaming functions under single and sequential
; extensions, and preimage witnesses for the image sets (which turn
; image-membership inversion into ordinary rewriting).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Pointwise behavior of the tagged renamings under a single extension
; (the string-level rule RENAME-VAR-STRING-OF-EXTEND-RENAMING already
; exists; these lift it through the kind dispatch).

(defruled rename-type-var-of-atom-extend
  (implies (type-varp w)
           (equal (rename-type-var w
                                   (extend-renaming n n2 atom-renam)
                                   array-renam)
                  (if (and (equal (type-var-kind w) :atom)
                           (equal (type-var-atom->name w) (str-fix n)))
                      (type-var-atom (str-fix n2))
                    (rename-type-var w atom-renam array-renam))))
  :enable (rename-type-var
           rename-var-string-of-extend-renaming))

(defruled rename-type-var-of-array-extend
  (implies (type-varp w)
           (equal (rename-type-var w
                                   atom-renam
                                   (extend-renaming n n2 array-renam))
                  (if (and (equal (type-var-kind w) :array)
                           (equal (type-var-array->name w) (str-fix n)))
                      (type-var-array (str-fix n2))
                    (rename-type-var w atom-renam array-renam))))
  :enable (rename-type-var
           rename-var-string-of-extend-renaming))

(defruled rename-ispace-var-of-dim-extend
  (implies (ispace-varp w)
           (equal (rename-ispace-var w
                                     (extend-renaming n n2 dim-renam)
                                     shape-renam)
                  (if (and (equal (ispace-var-kind w) :dim)
                           (equal (ispace-var-dim->name w) (str-fix n)))
                      (ispace-var-dim (str-fix n2))
                    (rename-ispace-var w dim-renam shape-renam))))
  :enable (rename-ispace-var
           rename-var-string-of-extend-renaming))

(defruled rename-ispace-var-of-shape-extend
  (implies (ispace-varp w)
           (equal (rename-ispace-var w
                                     dim-renam
                                     (extend-renaming n n2 shape-renam))
                  (if (and (equal (ispace-var-kind w) :shape)
                           (equal (ispace-var-shape->name w) (str-fix n)))
                      (ispace-var-shape (str-fix n2))
                    (rename-ispace-var w dim-renam shape-renam))))
  :enable (rename-ispace-var
           rename-var-string-of-extend-renaming))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Preimage witnesses for the image sets: for an element of the image,
; produce an element of the original set that renames to it.  These
; turn the existential inversion of image membership into rewriting
; with an explicit witness term.

(define rename-var-string-set-preimage ((y stringp)
                                        (names string-setp)
                                        (renam string-string-mapp))
  :returns (x stringp)
  :short "Preimage witness for @(tsee rename-var-string-set)."
  (b* (((when (set::emptyp (string-sfix names))) ""))
    (if (equal (rename-var-string (set::head names) renam)
               (str-fix y))
        (str-fix (set::head names))
      (rename-var-string-set-preimage y (set::tail names) renam)))
  :prepwork ((local (in-theory (enable acl2::emptyp-of-string-sfix))))
  :verify-guards :after-returns)

(defruled rename-var-string-set-preimage-witnesses
  (implies (and (string-setp names)
                (set::in y (rename-var-string-set names renam)))
           (b* ((x (rename-var-string-set-preimage y names renam)))
             (and (set::in x names)
                  (equal (rename-var-string x renam) y))))
  :induct (rename-var-string-set-preimage y names renam)
  :enable (rename-var-string-set-preimage
           rename-var-string-set))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Membership in the image of a set under a renaming: a variable outside the
; set whose name is not a value of the maps is not in the image; and the
; image is contained in the map values together with the original set.
; These are the two directions the closure cases of the value relation need
; --- the first to place a fresh binder name outside the image of a scope,
; the second to bound the support set of a closure body.

(defrule not-in-rename-var-string-set-when-fresh
  (implies (and (string-setp names)
                (stringp y)
                (not (set::in y names))
                (not (set::in y (omap::values (string-string-map-fix renam)))))
           (not (set::in y (rename-var-string-set names renam))))
  :use (rename-var-string-set-preimage-witnesses
        (:instance omap::cdr-assoc-in-values
                   (key (rename-var-string-set-preimage y names renam))
                   (map (string-string-map-fix renam))))
  :enable rename-var-string)

(defrule not-in-ispace-var-set-rename-ispace-vars-when-fresh
  (implies (and (ispace-var-setp vars)
                (ispace-varp y)
                (not (set::in y vars))
                (not (set::in (ispace-var->name y)
                              (omap::values
                               (string-string-map-fix dim-renam))))
                (not (set::in (ispace-var->name y)
                              (omap::values
                               (string-string-map-fix shape-renam)))))
           (not (set::in y (ispace-var-set-rename-ispace-vars
                            vars dim-renam shape-renam))))
  :use (ispace-var-set-rename-ispace-vars-preimage-witnesses
        (:instance omap::cdr-assoc-in-values
                   (key (ispace-var-dim->name
                         (ispace-var-set-rename-ispace-vars-preimage
                          y vars dim-renam shape-renam)))
                   (map (string-string-map-fix dim-renam)))
        (:instance omap::cdr-assoc-in-values
                   (key (ispace-var-shape->name
                         (ispace-var-set-rename-ispace-vars-preimage
                          y vars dim-renam shape-renam)))
                   (map (string-string-map-fix shape-renam)))
        (:instance ispace-var-equal-when-same-kind-and-name
                   (a y)
                   (b (ispace-var-set-rename-ispace-vars-preimage
                       y vars dim-renam shape-renam))))
  :enable (rename-ispace-var rename-var-string ispace-var->name))

(defrule not-in-type-var-set-rename-type-vars-when-fresh
  (implies (and (type-var-setp vars)
                (type-varp y)
                (not (set::in y vars))
                (not (set::in (type-var->name y)
                              (omap::values
                               (string-string-map-fix atom-renam))))
                (not (set::in (type-var->name y)
                              (omap::values
                               (string-string-map-fix array-renam)))))
           (not (set::in y (type-var-set-rename-type-vars
                            vars atom-renam array-renam))))
  :use (type-var-set-rename-type-vars-preimage-witnesses
        (:instance omap::cdr-assoc-in-values
                   (key (type-var-atom->name
                         (type-var-set-rename-type-vars-preimage
                          y vars atom-renam array-renam)))
                   (map (string-string-map-fix atom-renam)))
        (:instance omap::cdr-assoc-in-values
                   (key (type-var-array->name
                         (type-var-set-rename-type-vars-preimage
                          y vars atom-renam array-renam)))
                   (map (string-string-map-fix array-renam)))
        (:instance type-var-equal-when-same-kind-and-name
                   (a y)
                   (b (type-var-set-rename-type-vars-preimage
                       y vars atom-renam array-renam))))
  :enable (rename-type-var rename-var-string type-var->name))

(defrule subset-names-of-ispace-var-set-rename-ispace-vars
  (implies (ispace-var-setp vars)
           (set::subset (ispace-var-set-names
                         (ispace-var-set-rename-ispace-vars
                          vars dim-renam shape-renam))
                        (set::union
                         (omap::values (string-string-map-fix dim-renam))
                         (set::union
                          (omap::values (string-string-map-fix shape-renam))
                          (ispace-var-set-names vars)))))
  :induct (ispace-var-set-rename-ispace-vars vars dim-renam shape-renam)
  :enable (ispace-var-set-rename-ispace-vars
           ispace-var-set-names
           rename-ispace-var
           rename-var-string
           ispace-var->name
           subset-lifting-rules
           set::subset-insert-x))

(defrule subset-names-of-type-var-set-rename-type-vars
  (implies (type-var-setp vars)
           (set::subset (type-var-set-names
                         (type-var-set-rename-type-vars
                          vars atom-renam array-renam))
                        (set::union
                         (omap::values (string-string-map-fix atom-renam))
                         (set::union
                          (omap::values (string-string-map-fix array-renam))
                          (type-var-set-names vars)))))
  :induct (type-var-set-rename-type-vars vars atom-renam array-renam)
  :enable (type-var-set-rename-type-vars
           type-var-set-names
           rename-type-var
           rename-var-string
           type-var->name
           subset-lifting-rules
           set::subset-insert-x))

(defrule in-names-when-in-rename-var-string-set-and-not-value
  (implies (and (string-setp names)
                (set::in y (rename-var-string-set names renam))
                (not (set::in y (omap::values (string-string-map-fix renam)))))
           (set::in y names))
  :use (rename-var-string-set-preimage-witnesses
        (:instance omap::cdr-assoc-in-values
                   (key (rename-var-string-set-preimage y names renam))
                   (map (string-string-map-fix renam))))
  :enable rename-var-string
  :disable not-in-rename-var-string-set-when-fresh)

(defrule subset-rename-var-string-set
  (implies (string-setp names)
           (set::subset (rename-var-string-set names renam)
                        (set::union
                         (omap::values (string-string-map-fix renam))
                         names)))
  :enable (set::pick-a-point-subset-strategy set::union-in))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Image-set lemmas for the free-variables correspondence, string
; (expression-variable) namespace.  The tagged namespaces follow the
; same pattern.
;
; The workhorse is the membership characterization of an image under an
; extended renaming (S1); everything else is set algebra over it.

; S1: membership in the image under a single extension.

(defruled in-of-rename-var-string-set-of-extend-renaming
  (implies (and (string-setp s)
                (stringp n)
                (stringp n2))
           (iff (set::in y (rename-var-string-set
                            s (extend-renaming n n2 m)))
                (or (and (set::in n s)
                         (equal y n2))
                    (set::in y (rename-var-string-set
                                (set::delete n s) m)))))
  :enable (rename-var-string-of-extend-renaming)
  :use ((:instance rename-var-string-set-preimage-witnesses
                   (names s)
                   (renam (extend-renaming n n2 m)))
        (:instance rename-var-string-set-preimage-witnesses
                   (names (set::delete n s))
                   (renam m))
        (:instance in-of-rename-var-string-of-rename-var-string-set
                   (x (rename-var-string-set-preimage
                       y s (extend-renaming n n2 m)))
                   (vars (set::delete n s))
                   (renam m))
        (:instance in-of-rename-var-string-of-rename-var-string-set
                   (x (rename-var-string-set-preimage
                       y (set::delete n s) m))
                   (vars s)
                   (renam (extend-renaming n n2 m)))
        (:instance in-of-rename-var-string-of-rename-var-string-set
                   (x n)
                   (vars s)
                   (renam (extend-renaming n n2 m)))))

; Direct setp rule so that SET::DOUBLE-CONTAINMENT's setp hypotheses
; (which carry a backchain limit) discharge in one step.

(defrule setp-of-rename-var-string-set
  (set::setp (rename-var-string-set names renam)))

; S3: the unary binder step: deleting the new name from the image under
; the extension yields the image of the set without the old name,
; provided the new name captures nothing (the fold's F4 conjunct).

(defruled delete-of-rename-var-string-set-of-extend-renaming
  (implies (and (string-setp s)
                (stringp n)
                (stringp n2)
                (not (set::in n2
                              (rename-var-string-set (set::delete n s)
                                                     m))))
           (equal (set::delete
                   n2
                   (rename-var-string-set s (extend-renaming n n2 m)))
                  (rename-var-string-set (set::delete n s) m)))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy
           in-of-rename-var-string-set-of-extend-renaming))

; S5: images distribute over unions.

(defruled in-of-rename-var-string-set-of-union
  (implies (and (string-setp s1)
                (string-setp s2))
           (iff (set::in y (rename-var-string-set (set::union s1 s2) m))
                (or (set::in y (rename-var-string-set s1 m))
                    (set::in y (rename-var-string-set s2 m)))))
  :use ((:instance rename-var-string-set-preimage-witnesses
                   (names (set::union s1 s2))
                   (renam m))
        (:instance rename-var-string-set-preimage-witnesses
                   (names s1)
                   (renam m))
        (:instance rename-var-string-set-preimage-witnesses
                   (names s2)
                   (renam m))
        (:instance in-of-rename-var-string-of-rename-var-string-set
                   (x (rename-var-string-set-preimage
                       y (set::union s1 s2) m))
                   (vars s1)
                   (renam m))
        (:instance in-of-rename-var-string-of-rename-var-string-set
                   (x (rename-var-string-set-preimage
                       y (set::union s1 s2) m))
                   (vars s2)
                   (renam m))
        (:instance in-of-rename-var-string-of-rename-var-string-set
                   (x (rename-var-string-set-preimage y s1 m))
                   (vars (set::union s1 s2))
                   (renam m))
        (:instance in-of-rename-var-string-of-rename-var-string-set
                   (x (rename-var-string-set-preimage y s2 m))
                   (vars (set::union s1 s2))
                   (renam m))))

(defruled rename-var-string-set-of-union
  (implies (and (string-setp s1)
                (string-setp s2))
           (equal (rename-var-string-set (set::union s1 s2) m)
                  (set::union (rename-var-string-set s1 m)
                              (rename-var-string-set s2 m))))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy
           in-of-rename-var-string-set-of-union))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The type-variable namespace: the same lemmas, once per renaming map
; (the extension acts on the atom-kind or the array-kind map, and the
; affected elements are the correspondingly tagged variables).

(defruled in-of-type-var-set-rename-type-vars-of-atom-extend
  (implies (and (type-var-setp s)
                (stringp n)
                (stringp n2))
           (iff (set::in y (type-var-set-rename-type-vars
                            s (extend-renaming n n2 atom-m) array-m))
                (or (and (set::in (type-var-atom n) s)
                         (equal y (type-var-atom n2)))
                    (set::in y (type-var-set-rename-type-vars
                                (set::delete (type-var-atom n) s)
                                atom-m array-m)))))
  :enable (rename-type-var-of-atom-extend)
  :use ((:instance type-var-set-rename-type-vars-preimage-witnesses
                   (vars s)
                   (atom-renam (extend-renaming n n2 atom-m))
                   (array-renam array-m))
        (:instance type-var-set-rename-type-vars-preimage-witnesses
                   (vars (set::delete (type-var-atom n) s))
                   (atom-renam atom-m)
                   (array-renam array-m))
        (:instance in-of-rename-type-var-of-type-var-set-rename-type-vars
                   (var (type-var-set-rename-type-vars-preimage
                         y s (extend-renaming n n2 atom-m) array-m))
                   (vars (set::delete (type-var-atom n) s))
                   (atom-renam atom-m)
                   (array-renam array-m))
        (:instance in-of-rename-type-var-of-type-var-set-rename-type-vars
                   (var (type-var-set-rename-type-vars-preimage
                         y (set::delete (type-var-atom n) s)
                         atom-m array-m))
                   (vars s)
                   (atom-renam (extend-renaming n n2 atom-m))
                   (array-renam array-m))
        (:instance in-of-rename-type-var-of-type-var-set-rename-type-vars
                   (var (type-var-atom n))
                   (vars s)
                   (atom-renam (extend-renaming n n2 atom-m))
                   (array-renam array-m))
        (:instance in-of-type-var-atom-by-kind-name
                   (v (type-var-set-rename-type-vars-preimage
                       y s (extend-renaming n n2 atom-m) array-m)))))

(defruled in-of-type-var-set-rename-type-vars-of-array-extend
  (implies (and (type-var-setp s)
                (stringp n)
                (stringp n2))
           (iff (set::in y (type-var-set-rename-type-vars
                            s atom-m (extend-renaming n n2 array-m)))
                (or (and (set::in (type-var-array n) s)
                         (equal y (type-var-array n2)))
                    (set::in y (type-var-set-rename-type-vars
                                (set::delete (type-var-array n) s)
                                atom-m array-m)))))
  :enable (rename-type-var-of-array-extend)
  :use ((:instance type-var-set-rename-type-vars-preimage-witnesses
                   (vars s)
                   (atom-renam atom-m)
                   (array-renam (extend-renaming n n2 array-m)))
        (:instance type-var-set-rename-type-vars-preimage-witnesses
                   (vars (set::delete (type-var-array n) s))
                   (atom-renam atom-m)
                   (array-renam array-m))
        (:instance in-of-rename-type-var-of-type-var-set-rename-type-vars
                   (var (type-var-set-rename-type-vars-preimage
                         y s atom-m (extend-renaming n n2 array-m)))
                   (vars (set::delete (type-var-array n) s))
                   (atom-renam atom-m)
                   (array-renam array-m))
        (:instance in-of-rename-type-var-of-type-var-set-rename-type-vars
                   (var (type-var-set-rename-type-vars-preimage
                         y (set::delete (type-var-array n) s)
                         atom-m array-m))
                   (vars s)
                   (atom-renam atom-m)
                   (array-renam (extend-renaming n n2 array-m)))
        (:instance in-of-rename-type-var-of-type-var-set-rename-type-vars
                   (var (type-var-array n))
                   (vars s)
                   (atom-renam atom-m)
                   (array-renam (extend-renaming n n2 array-m)))
        (:instance in-of-type-var-array-by-kind-name
                   (v (type-var-set-rename-type-vars-preimage
                       y s atom-m (extend-renaming n n2 array-m))))))

(defruled delete-of-type-var-set-rename-type-vars-of-atom-extend
  (implies (and (type-var-setp s)
                (stringp n)
                (stringp n2)
                (not (set::in (type-var-atom n2)
                              (type-var-set-rename-type-vars
                               (set::delete (type-var-atom n) s)
                               atom-m array-m))))
           (equal (set::delete
                   (type-var-atom n2)
                   (type-var-set-rename-type-vars
                    s (extend-renaming n n2 atom-m) array-m))
                  (type-var-set-rename-type-vars
                   (set::delete (type-var-atom n) s)
                   atom-m array-m)))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy
           in-of-type-var-set-rename-type-vars-of-atom-extend))

(defruled delete-of-type-var-set-rename-type-vars-of-array-extend
  (implies (and (type-var-setp s)
                (stringp n)
                (stringp n2)
                (not (set::in (type-var-array n2)
                              (type-var-set-rename-type-vars
                               (set::delete (type-var-array n) s)
                               atom-m array-m))))
           (equal (set::delete
                   (type-var-array n2)
                   (type-var-set-rename-type-vars
                    s atom-m (extend-renaming n n2 array-m)))
                  (type-var-set-rename-type-vars
                   (set::delete (type-var-array n) s)
                   atom-m array-m)))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy
           in-of-type-var-set-rename-type-vars-of-array-extend))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The ispace-variable namespace.

(defruled in-of-ispace-var-set-rename-ispace-vars-of-dim-extend
  (implies (and (ispace-var-setp s)
                (stringp n)
                (stringp n2))
           (iff (set::in y (ispace-var-set-rename-ispace-vars
                            s (extend-renaming n n2 dim-m) shape-m))
                (or (and (set::in (ispace-var-dim n) s)
                         (equal y (ispace-var-dim n2)))
                    (set::in y (ispace-var-set-rename-ispace-vars
                                (set::delete (ispace-var-dim n) s)
                                dim-m shape-m)))))
  :enable (rename-ispace-var-of-dim-extend)
  :use ((:instance ispace-var-set-rename-ispace-vars-preimage-witnesses
                   (vars s)
                   (dim-renam (extend-renaming n n2 dim-m))
                   (shape-renam shape-m))
        (:instance ispace-var-set-rename-ispace-vars-preimage-witnesses
                   (vars (set::delete (ispace-var-dim n) s))
                   (dim-renam dim-m)
                   (shape-renam shape-m))
        (:instance in-of-rename-ispace-var-of-ispace-var-set-rename-ispace-vars
                   (var (ispace-var-set-rename-ispace-vars-preimage
                         y s (extend-renaming n n2 dim-m) shape-m))
                   (vars (set::delete (ispace-var-dim n) s))
                   (dim-renam dim-m)
                   (shape-renam shape-m))
        (:instance in-of-rename-ispace-var-of-ispace-var-set-rename-ispace-vars
                   (var (ispace-var-set-rename-ispace-vars-preimage
                         y (set::delete (ispace-var-dim n) s)
                         dim-m shape-m))
                   (vars s)
                   (dim-renam (extend-renaming n n2 dim-m))
                   (shape-renam shape-m))
        (:instance in-of-rename-ispace-var-of-ispace-var-set-rename-ispace-vars
                   (var (ispace-var-dim n))
                   (vars s)
                   (dim-renam (extend-renaming n n2 dim-m))
                   (shape-renam shape-m))
        (:instance in-of-ispace-var-dim-by-kind-name
                   (v (ispace-var-set-rename-ispace-vars-preimage
                       y s (extend-renaming n n2 dim-m) shape-m)))))

(defruled in-of-ispace-var-set-rename-ispace-vars-of-shape-extend
  (implies (and (ispace-var-setp s)
                (stringp n)
                (stringp n2))
           (iff (set::in y (ispace-var-set-rename-ispace-vars
                            s dim-m (extend-renaming n n2 shape-m)))
                (or (and (set::in (ispace-var-shape n) s)
                         (equal y (ispace-var-shape n2)))
                    (set::in y (ispace-var-set-rename-ispace-vars
                                (set::delete (ispace-var-shape n) s)
                                dim-m shape-m)))))
  :enable (rename-ispace-var-of-shape-extend)
  :use ((:instance ispace-var-set-rename-ispace-vars-preimage-witnesses
                   (vars s)
                   (dim-renam dim-m)
                   (shape-renam (extend-renaming n n2 shape-m)))
        (:instance ispace-var-set-rename-ispace-vars-preimage-witnesses
                   (vars (set::delete (ispace-var-shape n) s))
                   (dim-renam dim-m)
                   (shape-renam shape-m))
        (:instance in-of-rename-ispace-var-of-ispace-var-set-rename-ispace-vars
                   (var (ispace-var-set-rename-ispace-vars-preimage
                         y s dim-m (extend-renaming n n2 shape-m)))
                   (vars (set::delete (ispace-var-shape n) s))
                   (dim-renam dim-m)
                   (shape-renam shape-m))
        (:instance in-of-rename-ispace-var-of-ispace-var-set-rename-ispace-vars
                   (var (ispace-var-set-rename-ispace-vars-preimage
                         y (set::delete (ispace-var-shape n) s)
                         dim-m shape-m))
                   (vars s)
                   (dim-renam dim-m)
                   (shape-renam (extend-renaming n n2 shape-m)))
        (:instance in-of-rename-ispace-var-of-ispace-var-set-rename-ispace-vars
                   (var (ispace-var-shape n))
                   (vars s)
                   (dim-renam dim-m)
                   (shape-renam (extend-renaming n n2 shape-m)))
        (:instance in-of-ispace-var-shape-by-kind-name
                   (v (ispace-var-set-rename-ispace-vars-preimage
                       y s dim-m (extend-renaming n n2 shape-m))))))

(defruled delete-of-ispace-var-set-rename-ispace-vars-of-dim-extend
  (implies (and (ispace-var-setp s)
                (stringp n)
                (stringp n2)
                (not (set::in (ispace-var-dim n2)
                              (ispace-var-set-rename-ispace-vars
                               (set::delete (ispace-var-dim n) s)
                               dim-m shape-m))))
           (equal (set::delete
                   (ispace-var-dim n2)
                   (ispace-var-set-rename-ispace-vars
                    s (extend-renaming n n2 dim-m) shape-m))
                  (ispace-var-set-rename-ispace-vars
                   (set::delete (ispace-var-dim n) s)
                   dim-m shape-m)))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy
           in-of-ispace-var-set-rename-ispace-vars-of-dim-extend))

(defruled delete-of-ispace-var-set-rename-ispace-vars-of-shape-extend
  (implies (and (ispace-var-setp s)
                (stringp n)
                (stringp n2)
                (not (set::in (ispace-var-shape n2)
                              (ispace-var-set-rename-ispace-vars
                               (set::delete (ispace-var-shape n) s)
                               dim-m shape-m))))
           (equal (set::delete
                   (ispace-var-shape n2)
                   (ispace-var-set-rename-ispace-vars
                    s dim-m (extend-renaming n n2 shape-m)))
                  (ispace-var-set-rename-ispace-vars
                   (set::delete (ispace-var-shape n) s)
                   dim-m shape-m)))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy
           in-of-ispace-var-set-rename-ispace-vars-of-shape-extend))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Singleton images, for the variable cases of the free-variable folds.

(defruled rename-var-string-set-of-singleton
  (implies (stringp x)
           (equal (rename-var-string-set (set::insert x nil) m)
                  (set::insert (rename-var-string x m) nil)))
  :enable (rename-var-string-set))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Set-algebra support for the n-ary binder steps of the free-variables
; correspondence: the map-fixing congruence of the image function, and
; the disjointness facts that discharge the inductive hypotheses when
; parameters are peeled one at a time.

; RENAME-VAR-STRING-SET is congruent in the renaming map: needed because
; EXTEND-RENAMING-LIST's base case returns the FIXED map.

(defrule rename-var-string-set-of-string-string-map-fix-renam
  (equal (rename-var-string-set names (string-string-map-fix renam))
         (rename-var-string-set names renam))
  :induct (rename-var-string-set names renam)
  :enable rename-var-string-set)

; A: a difference by a disjoint set is the identity (the base case).

; B: disjointness transports across one extension, provided the new name
; is not among the names being kept disjoint (the inductive-hypothesis
; bridge).

(defruled disjoint-of-image-of-extend-when-disjoint
  (implies (and (string-setp s)
                (string-setp l)
                (stringp n)
                (stringp n2)
                (not (set::in n2 l))
                (set::emptyp
                 (set::intersect l (rename-var-string-set
                                    (set::delete n s) m))))
           (set::emptyp
            (set::intersect l (rename-var-string-set
                               s (extend-renaming n n2 m)))))
  :enable (in-of-rename-var-string-set-of-extend-renaming
           not-in-when-disjoint)
  :use ((:instance set::in-head
                   (x (set::intersect
                       l (rename-var-string-set
                          s (extend-renaming n n2 m)))))
        (:instance set::never-in-empty
                   (a (set::head
                       (set::intersect
                        l (rename-var-string-set
                           s (extend-renaming n n2 m)))))
                   (x (set::intersect
                       l (rename-var-string-set
                          s (extend-renaming n n2 m)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; C: disjointness is monotone in the first argument, and the mergesort
; of a tail is a subset of the mergesort of the whole list; together
; these shrink the outer capture hypothesis to the one the inductive
; hypothesis needs.

(defruled difference-of-rename-var-string-set-of-extend-renaming-list
  (implies (and (string-setp s)
                (string-listp names)
                (string-listp new-names)
                (equal (len names) (len new-names))
                (no-duplicatesp-equal new-names)
                (set::emptyp
                 (set::intersect
                  (set::mergesort new-names)
                  (rename-var-string-set
                   (set::difference s (set::mergesort names))
                   m))))
           (equal (set::difference
                   (rename-var-string-set
                    s (extend-renaming-list names new-names m))
                   (set::mergesort new-names))
                  (rename-var-string-set
                   (set::difference s (set::mergesort names))
                   m)))
  :induct (extend-renaming-list names new-names m)
  :enable (extend-renaming-list
           mergesort-of-cons
           set::difference-insert-y
           difference-when-disjoint
           disjoint-of-image-of-extend-when-disjoint)
  :hints
  ((and acl2::stable-under-simplificationp
        '(:use ((:instance delete-of-rename-var-string-set-of-extend-renaming
                           (s (set::difference
                               s (set::mergesort (cdr names))))
                           (n (car names))
                           (n2 (car new-names)))
                (:instance disjoint-of-image-of-extend-when-disjoint
                           (l (set::mergesort (cdr new-names)))
                           (s (set::difference
                               s (set::mergesort (cdr names))))
                           (n (car names))
                           (n2 (car new-names)))
                (:instance disjoint-monotone
                           (l (set::mergesort new-names))
                           (l2 (set::mergesort (cdr new-names)))
                           (x (rename-var-string-set
                               (set::difference s (set::mergesort names))
                               m)))
                (:instance subset-of-mergesort-of-cdr
                           (l new-names))
                ;; The branch where the head's no-capture condition
                ;; fails contradicts the overall capture hypothesis,
                ;; since the head's new name is among the new names.
                (:instance not-in-when-disjoint
                           (a (car new-names))
                           (y (set::mergesort new-names))
                           (x (rename-var-string-set
                               (set::delete
                                (car names)
                                (set::difference
                                 s (set::mergesort (cdr names))))
                               m))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The n-ary binder steps for the tagged namespaces.  These mirror the
; string-namespace lemma, with one extra wrinkle: a parameter list mixes
; the two kinds of each namespace, so the induction dispatches on the
; kind of each parameter and uses that kind's extension lemmas.

; The map-fixing congruences (the base cases of the ALPHA-EXTEND
; functions return the FIXED maps).

; Disjointness transports across one extension, per kind.

(defruled disjoint-of-type-var-image-of-atom-extend
  (implies (and (type-var-setp s)
                (set::setp l)
                (stringp n)
                (stringp n2)
                (not (set::in (type-var-atom n2) l))
                (set::emptyp
                 (set::intersect l (type-var-set-rename-type-vars
                                    (set::delete (type-var-atom n) s)
                                    atom-m array-m))))
           (set::emptyp
            (set::intersect l (type-var-set-rename-type-vars s (extend-renaming n n2 atom-m) array-m))))
  :enable (in-of-type-var-set-rename-type-vars-of-atom-extend
           not-in-when-disjoint)
  :use ((:instance set::in-head
                   (x (set::intersect
                       l (type-var-set-rename-type-vars s (extend-renaming n n2 atom-m) array-m))))
        (:instance set::never-in-empty
                   (a (set::head
                       (set::intersect
                        l (type-var-set-rename-type-vars s (extend-renaming n n2 atom-m) array-m))))
                   (x (set::intersect
                       l (type-var-set-rename-type-vars s (extend-renaming n n2 atom-m) array-m))))
        (:instance in-of-type-var-atom-by-kind-name
                   (v (set::head
                       (set::intersect
                        l (type-var-set-rename-type-vars s (extend-renaming n n2 atom-m) array-m))))
                   (n n2)
                   (s l))))

(defruled disjoint-of-type-var-image-of-array-extend
  (implies (and (type-var-setp s)
                (set::setp l)
                (stringp n)
                (stringp n2)
                (not (set::in (type-var-array n2) l))
                (set::emptyp
                 (set::intersect l (type-var-set-rename-type-vars
                                    (set::delete (type-var-array n) s)
                                    atom-m array-m))))
           (set::emptyp
            (set::intersect l (type-var-set-rename-type-vars s atom-m (extend-renaming n n2 array-m)))))
  :enable (in-of-type-var-set-rename-type-vars-of-array-extend
           not-in-when-disjoint)
  :use ((:instance set::in-head
                   (x (set::intersect
                       l (type-var-set-rename-type-vars s atom-m (extend-renaming n n2 array-m)))))
        (:instance set::never-in-empty
                   (a (set::head
                       (set::intersect
                        l (type-var-set-rename-type-vars s atom-m (extend-renaming n n2 array-m)))))
                   (x (set::intersect
                       l (type-var-set-rename-type-vars s atom-m (extend-renaming n n2 array-m)))))
        (:instance in-of-type-var-array-by-kind-name
                   (v (set::head
                       (set::intersect
                        l (type-var-set-rename-type-vars s atom-m (extend-renaming n n2 array-m)))))
                   (n n2)
                   (s l))))

(defruled disjoint-of-ispace-var-image-of-dim-extend
  (implies (and (ispace-var-setp s)
                (set::setp l)
                (stringp n)
                (stringp n2)
                (not (set::in (ispace-var-dim n2) l))
                (set::emptyp
                 (set::intersect l (ispace-var-set-rename-ispace-vars
                                    (set::delete (ispace-var-dim n) s)
                                    dim-m shape-m))))
           (set::emptyp
            (set::intersect l (ispace-var-set-rename-ispace-vars s (extend-renaming n n2 dim-m) shape-m))))
  :enable (in-of-ispace-var-set-rename-ispace-vars-of-dim-extend
           not-in-when-disjoint)
  :use ((:instance set::in-head
                   (x (set::intersect
                       l (ispace-var-set-rename-ispace-vars s (extend-renaming n n2 dim-m) shape-m))))
        (:instance set::never-in-empty
                   (a (set::head
                       (set::intersect
                        l (ispace-var-set-rename-ispace-vars s (extend-renaming n n2 dim-m) shape-m))))
                   (x (set::intersect
                       l (ispace-var-set-rename-ispace-vars s (extend-renaming n n2 dim-m) shape-m))))
        (:instance in-of-ispace-var-dim-by-kind-name
                   (v (set::head
                       (set::intersect
                        l (ispace-var-set-rename-ispace-vars s (extend-renaming n n2 dim-m) shape-m))))
                   (n n2)
                   (s l))))

(defruled disjoint-of-ispace-var-image-of-shape-extend
  (implies (and (ispace-var-setp s)
                (set::setp l)
                (stringp n)
                (stringp n2)
                (not (set::in (ispace-var-shape n2) l))
                (set::emptyp
                 (set::intersect l (ispace-var-set-rename-ispace-vars
                                    (set::delete (ispace-var-shape n) s)
                                    dim-m shape-m))))
           (set::emptyp
            (set::intersect l (ispace-var-set-rename-ispace-vars s dim-m (extend-renaming n n2 shape-m)))))
  :enable (in-of-ispace-var-set-rename-ispace-vars-of-shape-extend
           not-in-when-disjoint)
  :use ((:instance set::in-head
                   (x (set::intersect
                       l (ispace-var-set-rename-ispace-vars s dim-m (extend-renaming n n2 shape-m)))))
        (:instance set::never-in-empty
                   (a (set::head
                       (set::intersect
                        l (ispace-var-set-rename-ispace-vars s dim-m (extend-renaming n n2 shape-m)))))
                   (x (set::intersect
                       l (ispace-var-set-rename-ispace-vars s dim-m (extend-renaming n n2 shape-m)))))
        (:instance in-of-ispace-var-shape-by-kind-name
                   (v (set::head
                       (set::intersect
                        l (ispace-var-set-rename-ispace-vars s dim-m (extend-renaming n n2 shape-m)))))
                   (n n2)
                   (s l))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The type-variable n-ary step.

(defruled difference-of-type-var-set-rename-type-vars-of-alpha-extend
  (implies (and (type-var-setp s)
                (type-var-listp params)
                (type-var-listp new-params)
                (equal (len params) (len new-params))
                (no-duplicatesp-equal new-params)
                (mv-nth 0 (type-var-list-alpha-extend
                           new-params params atom-m array-m))
                (set::emptyp
                 (set::intersect
                  (set::mergesort new-params)
                  (type-var-set-rename-type-vars
                   (set::difference s (set::mergesort params))
                   atom-m array-m))))
           (b* (((mv & new-atom-m new-array-m)
                 (type-var-list-alpha-extend new-params params
                                             atom-m array-m)))
             (equal (set::difference
                     (type-var-set-rename-type-vars s new-atom-m
                                                    new-array-m)
                     (set::mergesort new-params))
                    (type-var-set-rename-type-vars
                     (set::difference s (set::mergesort params))
                     atom-m array-m))))
  :induct (type-var-list-alpha-extend new-params params atom-m array-m)
  :enable (type-var-list-alpha-extend
           mergesort-of-cons
           set::difference-insert-y
           difference-when-disjoint
           disjoint-of-type-var-image-of-atom-extend
           disjoint-of-type-var-image-of-array-extend)
  :hints
  ((and acl2::stable-under-simplificationp
        (let ((fns (acl2::all-fnnames-lst clause)))
          (cond ((and (member-eq 'type-var-atom->name$inline fns)
                      (not (member-eq 'type-var-array->name$inline fns)))
                 '(:use ((:instance delete-of-type-var-set-rename-type-vars-of-atom-extend
                           (s (set::difference
                               s (set::mergesort (cdr params))))
                           (n (type-var-atom->name (car params)))
                           (n2 (type-var-atom->name (car new-params))))
                         (:instance disjoint-of-type-var-image-of-atom-extend
                           (l (set::mergesort (cdr new-params)))
                           (s (set::difference
                               s (set::mergesort (cdr params))))
                           (n (type-var-atom->name (car params)))
                           (n2 (type-var-atom->name (car new-params))))
                         (:instance disjoint-monotone
                           (l (set::mergesort new-params))
                           (l2 (set::mergesort (cdr new-params)))
                           (x (type-var-set-rename-type-vars
                               (set::difference s (set::mergesort params))
                               atom-m array-m)))
                         (:instance subset-of-mergesort-of-cdr
                           (l new-params))
                         (:instance not-in-when-disjoint
                           (a (car new-params))
                           (y (set::mergesort new-params))
                           (x (type-var-set-rename-type-vars
                               (set::delete
                                (car params)
                                (set::difference
                                 s (set::mergesort (cdr params))))
                               atom-m array-m))))))
                ((and (member-eq 'type-var-array->name$inline fns)
                      (not (member-eq 'type-var-atom->name$inline fns)))
                 '(:use ((:instance delete-of-type-var-set-rename-type-vars-of-array-extend
                           (s (set::difference
                               s (set::mergesort (cdr params))))
                           (n (type-var-array->name (car params)))
                           (n2 (type-var-array->name (car new-params))))
                         (:instance disjoint-of-type-var-image-of-array-extend
                           (l (set::mergesort (cdr new-params)))
                           (s (set::difference
                               s (set::mergesort (cdr params))))
                           (n (type-var-array->name (car params)))
                           (n2 (type-var-array->name (car new-params))))
                         (:instance disjoint-monotone
                           (l (set::mergesort new-params))
                           (l2 (set::mergesort (cdr new-params)))
                           (x (type-var-set-rename-type-vars
                               (set::difference s (set::mergesort params))
                               atom-m array-m)))
                         (:instance subset-of-mergesort-of-cdr
                           (l new-params))
                         (:instance not-in-when-disjoint
                           (a (car new-params))
                           (y (set::mergesort new-params))
                           (x (type-var-set-rename-type-vars
                               (set::delete
                                (car params)
                                (set::difference
                                 s (set::mergesort (cdr params))))
                               atom-m array-m))))))
                (t '(:use ((:instance delete-of-type-var-set-rename-type-vars-of-atom-extend
                           (s (set::difference
                               s (set::mergesort (cdr params))))
                           (n (type-var-atom->name (car params)))
                           (n2 (type-var-atom->name (car new-params))))
                         (:instance delete-of-type-var-set-rename-type-vars-of-array-extend
                           (s (set::difference
                               s (set::mergesort (cdr params))))
                           (n (type-var-array->name (car params)))
                           (n2 (type-var-array->name (car new-params))))
                         (:instance disjoint-of-type-var-image-of-atom-extend
                           (l (set::mergesort (cdr new-params)))
                           (s (set::difference
                               s (set::mergesort (cdr params))))
                           (n (type-var-atom->name (car params)))
                           (n2 (type-var-atom->name (car new-params))))
                         (:instance disjoint-of-type-var-image-of-array-extend
                           (l (set::mergesort (cdr new-params)))
                           (s (set::difference
                               s (set::mergesort (cdr params))))
                           (n (type-var-array->name (car params)))
                           (n2 (type-var-array->name (car new-params))))
                         (:instance disjoint-monotone
                           (l (set::mergesort new-params))
                           (l2 (set::mergesort (cdr new-params)))
                           (x (type-var-set-rename-type-vars
                               (set::difference s (set::mergesort params))
                               atom-m array-m)))
                         (:instance subset-of-mergesort-of-cdr
                           (l new-params))
                         (:instance not-in-when-disjoint
                           (a (car new-params))
                           (y (set::mergesort new-params))
                           (x (type-var-set-rename-type-vars
                               (set::delete
                                (car params)
                                (set::difference
                                 s (set::mergesort (cdr params))))
                               atom-m array-m)))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The ispace-variable n-ary step.

(defruled difference-of-ispace-var-set-rename-ispace-vars-of-alpha-extend
  (implies (and (ispace-var-setp s)
                (ispace-var-listp params)
                (ispace-var-listp new-params)
                (equal (len params) (len new-params))
                (no-duplicatesp-equal new-params)
                (mv-nth 0 (ispace-var-list-alpha-extend
                           new-params params dim-m shape-m))
                (set::emptyp
                 (set::intersect
                  (set::mergesort new-params)
                  (ispace-var-set-rename-ispace-vars
                   (set::difference s (set::mergesort params))
                   dim-m shape-m))))
           (b* (((mv & new-dim-m new-shape-m)
                 (ispace-var-list-alpha-extend new-params params
                                               dim-m shape-m)))
             (equal (set::difference
                     (ispace-var-set-rename-ispace-vars s new-dim-m
                                                        new-shape-m)
                     (set::mergesort new-params))
                    (ispace-var-set-rename-ispace-vars
                     (set::difference s (set::mergesort params))
                     dim-m shape-m))))
  :induct (ispace-var-list-alpha-extend new-params params dim-m shape-m)
  :enable (ispace-var-list-alpha-extend
           mergesort-of-cons
           set::difference-insert-y
           difference-when-disjoint
           disjoint-of-ispace-var-image-of-dim-extend
           disjoint-of-ispace-var-image-of-shape-extend)
  :hints
  ((and acl2::stable-under-simplificationp
        (let ((fns (acl2::all-fnnames-lst clause)))
          (cond ((and (member-eq 'ispace-var-dim->name$inline fns)
                      (not (member-eq 'ispace-var-shape->name$inline fns)))
                 '(:use ((:instance delete-of-ispace-var-set-rename-ispace-vars-of-dim-extend
                           (s (set::difference
                               s (set::mergesort (cdr params))))
                           (n (ispace-var-dim->name (car params)))
                           (n2 (ispace-var-dim->name (car new-params))))
                         (:instance disjoint-of-ispace-var-image-of-dim-extend
                           (l (set::mergesort (cdr new-params)))
                           (s (set::difference
                               s (set::mergesort (cdr params))))
                           (n (ispace-var-dim->name (car params)))
                           (n2 (ispace-var-dim->name (car new-params))))
                         (:instance disjoint-monotone
                           (l (set::mergesort new-params))
                           (l2 (set::mergesort (cdr new-params)))
                           (x (ispace-var-set-rename-ispace-vars
                               (set::difference s (set::mergesort params))
                               dim-m shape-m)))
                         (:instance subset-of-mergesort-of-cdr
                           (l new-params))
                         (:instance not-in-when-disjoint
                           (a (car new-params))
                           (y (set::mergesort new-params))
                           (x (ispace-var-set-rename-ispace-vars
                               (set::delete
                                (car params)
                                (set::difference
                                 s (set::mergesort (cdr params))))
                               dim-m shape-m))))))
                ((and (member-eq 'ispace-var-shape->name$inline fns)
                      (not (member-eq 'ispace-var-dim->name$inline fns)))
                 '(:use ((:instance delete-of-ispace-var-set-rename-ispace-vars-of-shape-extend
                           (s (set::difference
                               s (set::mergesort (cdr params))))
                           (n (ispace-var-shape->name (car params)))
                           (n2 (ispace-var-shape->name (car new-params))))
                         (:instance disjoint-of-ispace-var-image-of-shape-extend
                           (l (set::mergesort (cdr new-params)))
                           (s (set::difference
                               s (set::mergesort (cdr params))))
                           (n (ispace-var-shape->name (car params)))
                           (n2 (ispace-var-shape->name (car new-params))))
                         (:instance disjoint-monotone
                           (l (set::mergesort new-params))
                           (l2 (set::mergesort (cdr new-params)))
                           (x (ispace-var-set-rename-ispace-vars
                               (set::difference s (set::mergesort params))
                               dim-m shape-m)))
                         (:instance subset-of-mergesort-of-cdr
                           (l new-params))
                         (:instance not-in-when-disjoint
                           (a (car new-params))
                           (y (set::mergesort new-params))
                           (x (ispace-var-set-rename-ispace-vars
                               (set::delete
                                (car params)
                                (set::difference
                                 s (set::mergesort (cdr params))))
                               dim-m shape-m))))))
                (t '(:use ((:instance delete-of-ispace-var-set-rename-ispace-vars-of-dim-extend
                           (s (set::difference
                               s (set::mergesort (cdr params))))
                           (n (ispace-var-dim->name (car params)))
                           (n2 (ispace-var-dim->name (car new-params))))
                         (:instance delete-of-ispace-var-set-rename-ispace-vars-of-shape-extend
                           (s (set::difference
                               s (set::mergesort (cdr params))))
                           (n (ispace-var-shape->name (car params)))
                           (n2 (ispace-var-shape->name (car new-params))))
                         (:instance disjoint-of-ispace-var-image-of-dim-extend
                           (l (set::mergesort (cdr new-params)))
                           (s (set::difference
                               s (set::mergesort (cdr params))))
                           (n (ispace-var-dim->name (car params)))
                           (n2 (ispace-var-dim->name (car new-params))))
                         (:instance disjoint-of-ispace-var-image-of-shape-extend
                           (l (set::mergesort (cdr new-params)))
                           (s (set::difference
                               s (set::mergesort (cdr params))))
                           (n (ispace-var-shape->name (car params)))
                           (n2 (ispace-var-shape->name (car new-params))))
                         (:instance disjoint-monotone
                           (l (set::mergesort new-params))
                           (l2 (set::mergesort (cdr new-params)))
                           (x (ispace-var-set-rename-ispace-vars
                               (set::difference s (set::mergesort params))
                               dim-m shape-m)))
                         (:instance subset-of-mergesort-of-cdr
                           (l new-params))
                         (:instance not-in-when-disjoint
                           (a (car new-params))
                           (y (set::mergesort new-params))
                           (x (ispace-var-set-rename-ispace-vars
                               (set::delete
                                (car params)
                                (set::difference
                                 s (set::mergesort (cdr params))))
                               dim-m shape-m)))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The let-scope lemma: how a sequence of binds transforms the free
; variables of the let body.  This is the bind-list analogue of the
; n-ary binder steps, and it is what the :let case of the free-variable
; correspondence consumes.
;
; Removing the binds' new bound names from the image of a set under the
; fully extended renamings yields the image, under the incoming
; renamings, of the set minus the binds' old bound names.  Only binds of
; the namespace in question contribute; binds of other namespaces leave
; both the set and that namespace's renaming untouched.

; Non-membership in an image transports to subsets, and hence the
; binder step applies when the no-capture condition is known for a
; LARGER set than the one at hand (which is the situation in the
; induction: each bind's condition is stated against the whole body
; scope, while the goal concerns the scope minus the later binds).

(defruled not-in-rename-var-string-set-when-subset
  (implies (and (set::subset a b)
                (string-setp a)
                (string-setp b)
                (not (set::in elt (rename-var-string-set b m))))
           (not (set::in elt (rename-var-string-set a m))))
  :use ((:instance rename-var-string-set-preimage-witnesses
                   (y elt) (names a) (renam m))
        (:instance in-of-rename-var-string-of-rename-var-string-set
                   (x (rename-var-string-set-preimage elt a m))
                   (vars b)
                   (renam m))
        (:instance set::subset-in
                   (a (rename-var-string-set-preimage elt a m))
                   (x a)
                   (y b))))

(defruled delete-of-rename-var-string-set-of-extend-renaming-subset
  (implies (and (string-setp s)
                (string-setp f)
                (set::subset s f)
                (stringp n)
                (stringp n2)
                (not (set::in n2 (rename-var-string-set
                                  (set::delete n f) m))))
           (equal (set::delete
                   n2 (rename-var-string-set s (extend-renaming n n2 m)))
                  (rename-var-string-set (set::delete n s) m)))
  :enable subset-of-delete-when-subset
  :use ((:instance delete-of-rename-var-string-set-of-extend-renaming)
        (:instance not-in-rename-var-string-set-when-subset
                   (elt n2)
                   (a (set::delete n s))
                   (b (set::delete n f)))))

(defruled difference-of-bind-list-image-expr
  (implies (and (bind-listp binds)
                (bind-listp new-binds)
                (string-setp f)
                (bind-list-alpha-related-p new-binds binds r)
                (bind-list-body-scope-fresh-ok new-binds binds r
                                               f tvars ivars))
           (equal (set::difference
                   (rename-var-string-set
                    f
                    (var-renamings->expr
                     (bind-list-alpha-extended-renamings new-binds
                                                         binds r)))
                   (bind-list-bound-expr-vars new-binds))
                  (rename-var-string-set
                   (set::difference f (bind-list-bound-expr-vars binds))
                   (var-renamings->expr r))))
  :induct (bind-list-alpha-extended-renamings new-binds binds r)
  :enable (bind-list-alpha-extended-renamings
           bind-list-alpha-related-p
           bind-alpha-related-p
           bind-list-body-scope-fresh-ok
           bind-list-bound-expr-vars
           bind-nocapture-ok
           bind-alpha-extended-renamings
           bind-bound-expr-vars
           bind-name
           set::difference-insert-y
           delete-of-rename-var-string-set-of-extend-renaming-subset))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The let-scope lemma for the tagged namespaces.  Only type bindings
; bind type variables and only ispace bindings bind ispace variables, so
; in each namespace all other binding kinds leave both the set and that
; namespace's renamings untouched.

; Image non-membership transports to subsets (tagged versions).

; The binder steps, usable when the no-capture condition is known for a
; larger set (the free variable F is matched against the hypothesis).

(defruled delete-of-type-var-image-of-atom-extend-subset
  (implies (and (type-var-setp s)
                (type-var-setp f)
                (set::subset s f)
                (type-varp v)
                (type-varp v-old)
                (equal (type-var-kind v) :atom)
                (equal (type-var-kind v-old) :atom)
                (not (set::in v (type-var-set-rename-type-vars
                                 (set::delete v-old f) atom-m array-m))))
           (equal (set::delete
                   v
                   (type-var-set-rename-type-vars
                    s (extend-renaming (type-var->name v-old) (type-var->name v) atom-m) array-m))
                  (type-var-set-rename-type-vars
                   (set::delete v-old s) atom-m array-m)))
  :enable (type-var->name
           subset-of-delete-when-subset)
  :use ((:instance delete-of-type-var-set-rename-type-vars-of-atom-extend
                   (n (type-var-atom->name v-old))
                   (n2 (type-var-atom->name v)))
        (:instance not-in-type-var-image-when-subset
                   (elt v)
                   (a (set::delete v-old s))
                   (b (set::delete v-old f)))
        (:instance type-var-fix-when-atom (x v))
        (:instance type-var-fix-when-atom (x v-old))))

(defruled delete-of-type-var-image-of-array-extend-subset
  (implies (and (type-var-setp s)
                (type-var-setp f)
                (set::subset s f)
                (type-varp v)
                (type-varp v-old)
                (equal (type-var-kind v) :array)
                (equal (type-var-kind v-old) :array)
                (not (set::in v (type-var-set-rename-type-vars
                                 (set::delete v-old f) atom-m array-m))))
           (equal (set::delete
                   v
                   (type-var-set-rename-type-vars
                    s atom-m (extend-renaming (type-var->name v-old) (type-var->name v) array-m)))
                  (type-var-set-rename-type-vars
                   (set::delete v-old s) atom-m array-m)))
  :enable (type-var->name
           subset-of-delete-when-subset)
  :use ((:instance delete-of-type-var-set-rename-type-vars-of-array-extend
                   (n (type-var-array->name v-old))
                   (n2 (type-var-array->name v)))
        (:instance not-in-type-var-image-when-subset
                   (elt v)
                   (a (set::delete v-old s))
                   (b (set::delete v-old f)))
        (:instance type-var-fix-when-array (x v))
        (:instance type-var-fix-when-array (x v-old))))

(defruled delete-of-ispace-var-image-of-dim-extend-subset
  (implies (and (ispace-var-setp s)
                (ispace-var-setp f)
                (set::subset s f)
                (ispace-varp v)
                (ispace-varp v-old)
                (equal (ispace-var-kind v) :dim)
                (equal (ispace-var-kind v-old) :dim)
                (not (set::in v (ispace-var-set-rename-ispace-vars
                                 (set::delete v-old f) dim-m shape-m))))
           (equal (set::delete
                   v
                   (ispace-var-set-rename-ispace-vars
                    s (extend-renaming (ispace-var->name v-old) (ispace-var->name v) dim-m) shape-m))
                  (ispace-var-set-rename-ispace-vars
                   (set::delete v-old s) dim-m shape-m)))
  :enable (ispace-var->name
           subset-of-delete-when-subset)
  :use ((:instance delete-of-ispace-var-set-rename-ispace-vars-of-dim-extend
                   (n (ispace-var-dim->name v-old))
                   (n2 (ispace-var-dim->name v)))
        (:instance not-in-ispace-var-image-when-subset
                   (elt v)
                   (a (set::delete v-old s))
                   (b (set::delete v-old f)))
        (:instance ispace-var-fix-when-dim (x v))
        (:instance ispace-var-fix-when-dim (x v-old))))

(defruled delete-of-ispace-var-image-of-shape-extend-subset
  (implies (and (ispace-var-setp s)
                (ispace-var-setp f)
                (set::subset s f)
                (ispace-varp v)
                (ispace-varp v-old)
                (equal (ispace-var-kind v) :shape)
                (equal (ispace-var-kind v-old) :shape)
                (not (set::in v (ispace-var-set-rename-ispace-vars
                                 (set::delete v-old f) dim-m shape-m))))
           (equal (set::delete
                   v
                   (ispace-var-set-rename-ispace-vars
                    s dim-m (extend-renaming (ispace-var->name v-old) (ispace-var->name v) shape-m)))
                  (ispace-var-set-rename-ispace-vars
                   (set::delete v-old s) dim-m shape-m)))
  :enable (ispace-var->name
           subset-of-delete-when-subset)
  :use ((:instance delete-of-ispace-var-set-rename-ispace-vars-of-shape-extend
                   (n (ispace-var-shape->name v-old))
                   (n2 (ispace-var-shape->name v)))
        (:instance not-in-ispace-var-image-when-subset
                   (elt v)
                   (a (set::delete v-old s))
                   (b (set::delete v-old f)))
        (:instance ispace-var-fix-when-shape (x v))
        (:instance ispace-var-fix-when-shape (x v-old))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled difference-of-bind-list-image-type
  (implies (and (bind-listp binds)
                (bind-listp new-binds)
                (type-var-setp f)
                (bind-list-alpha-related-p new-binds binds r)
                (bind-list-body-scope-fresh-ok new-binds binds r
                                               evars f ivars))
           (b* ((r2 (bind-list-alpha-extended-renamings new-binds
                                                        binds r)))
             (equal (set::difference
                     (type-var-set-rename-type-vars
                      f
                      (var-renamings->atom r2)
                      (var-renamings->array r2))
                     (bind-list-bound-type-vars new-binds))
                    (type-var-set-rename-type-vars
                     (set::difference f (bind-list-bound-type-vars binds))
                     (var-renamings->atom r)
                     (var-renamings->array r)))))
  :induct (bind-list-alpha-extended-renamings new-binds binds r)
  :enable (bind-list-alpha-extended-renamings
           bind-list-alpha-related-p
           bind-alpha-related-p
           bind-list-body-scope-fresh-ok
           bind-list-bound-type-vars
           bind-nocapture-ok
           bind-alpha-extended-renamings
           bind-bound-type-vars
           bind-name
           set::difference-insert-y
           delete-of-type-var-image-of-atom-extend-subset
           delete-of-type-var-image-of-array-extend-subset))

(defruled difference-of-bind-list-image-ispace
  (implies (and (bind-listp binds)
                (bind-listp new-binds)
                (ispace-var-setp f)
                (bind-list-alpha-related-p new-binds binds r)
                (bind-list-body-scope-fresh-ok new-binds binds r
                                               evars tvars f))
           (b* ((r2 (bind-list-alpha-extended-renamings new-binds
                                                        binds r)))
             (equal (set::difference
                     (ispace-var-set-rename-ispace-vars
                      f
                      (var-renamings->dim r2)
                      (var-renamings->shape r2))
                     (bind-list-bound-ispace-vars new-binds))
                    (ispace-var-set-rename-ispace-vars
                     (set::difference f
                                      (bind-list-bound-ispace-vars binds))
                     (var-renamings->dim r)
                     (var-renamings->shape r)))))
  :induct (bind-list-alpha-extended-renamings new-binds binds r)
  :enable (bind-list-alpha-extended-renamings
           bind-list-alpha-related-p
           bind-alpha-related-p
           bind-list-body-scope-fresh-ok
           bind-list-bound-ispace-vars
           bind-nocapture-ok
           bind-alpha-extended-renamings
           bind-bound-ispace-vars
           bind-name
           set::difference-insert-y
           delete-of-ispace-var-image-of-dim-extend-subset
           delete-of-ispace-var-image-of-shape-extend-subset))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The free-variable correspondence, expression-variable namespace: the
; free expression variables of a uniquified AST are exactly the renaming
; image of those of the original.
;
; The induction is on the FRESHNESS fold's scheme, not the relation's:
; the fold substitutes the support set in its recursive calls (it is
; reset at closure binders), so its scheme is the one whose inductive
; hypotheses match the subterms as they actually occur.

(defrule rename-var-string-set-of-nil
  (equal (rename-var-string-set nil renam) nil)
  :enable rename-var-string-set)

; The unbox forms delete the bound name from a body free-variable set
; that the inductive hypothesis characterizes only indirectly.  The
; rewriter will not substitute a hypothesis equality whose left-hand
; side is a compound term, so we key the binder step on the DELETE term
; itself and let the free variables of its hypothesis be matched against
; the inductive hypothesis in the context.

(defruled delete-of-free-vars-when-equal-image
  (implies (and (equal fnew (rename-var-string-set
                             fold (extend-renaming n n2 m)))
                (string-setp fold)
                (stringp n)
                (stringp n2)
                (not (set::in n2 (rename-var-string-set
                                  (set::delete n fold) m))))
           (equal (set::delete n2 fnew)
                  (rename-var-string-set (set::delete n fold) m)))
  :enable delete-of-rename-var-string-set-of-extend-renaming)

; The same shape at the n-ary binders and at LET: key the step on the
; DIFFERENCE term and match the inductive hypothesis from the context.

(defruled difference-of-free-vars-when-equal-image-list
  (implies (and (equal fnew (rename-var-string-set
                             fold (extend-renaming-list names new-names m)))
                (string-setp fold)
                (string-listp names)
                (string-listp new-names)
                (equal (len names) (len new-names))
                (no-duplicatesp-equal new-names)
                (set::emptyp
                 (set::intersect
                  (set::mergesort new-names)
                  (rename-var-string-set
                   (set::difference fold (set::mergesort names)) m))))
           (equal (set::difference fnew (set::mergesort new-names))
                  (rename-var-string-set
                   (set::difference fold (set::mergesort names)) m)))
  :enable difference-of-rename-var-string-set-of-extend-renaming-list)

(defruled difference-of-free-vars-when-equal-image-binds
  (implies (and (equal fnew
                       (rename-var-string-set
                        fold
                        (var-renamings->expr
                         (bind-list-alpha-extended-renamings
                          new-binds binds r))))
                (bind-listp binds)
                (bind-listp new-binds)
                (string-setp fold)
                (bind-list-alpha-related-p new-binds binds r)
                (bind-list-body-scope-fresh-ok new-binds binds r
                                               fold tvars ivars))
           (equal (set::difference fnew
                                   (bind-list-bound-expr-vars new-binds))
                  (rename-var-string-set
                   (set::difference fold
                                    (bind-list-bound-expr-vars binds))
                   (var-renamings->expr r))))
  :enable difference-of-bind-list-image-expr)

; Related ASTs have the same kind.

(defruled expr-kind-when-expr-alpha-related-p
  (implies (expr-alpha-related-p new-x x r)
           (equal (expr-kind new-x) (expr-kind x)))
  :expand ((expr-alpha-related-p new-x x r)))

(defruled atom-kind-when-atom-alpha-related-p
  (implies (atom-alpha-related-p new-a a r)
           (equal (atom-kind new-a) (atom-kind a)))
  :expand ((atom-alpha-related-p new-a a r)))

(defruled bind-kind-when-bind-alpha-related-p
  (implies (bind-alpha-related-p new-b b r)
           (equal (bind-kind new-b) (bind-kind b)))
  :expand ((bind-alpha-related-p new-b b r)))

(defthm-exprs-alpha-fresh-p-flag

  (defthm expr-free-expr-vars-of-alpha-related
    (implies (and (expr-alpha-related-p new-x x r)
                  (expr-alpha-fresh-p new-x x r b))
             (equal (expr-free-expr-vars new-x)
                    (rename-var-string-set (expr-free-expr-vars x)
                                           (var-renamings->expr r))))
    :flag expr-alpha-fresh-p)

  (defthm expr-list-free-expr-vars-of-alpha-related
    (implies (and (expr-list-alpha-related-p new-x x r)
                  (expr-list-alpha-fresh-p new-x x r b))
             (equal (expr-list-free-expr-vars new-x)
                    (rename-var-string-set (expr-list-free-expr-vars x)
                                           (var-renamings->expr r))))
    :flag expr-list-alpha-fresh-p)

  (defthm atom-free-expr-vars-of-alpha-related
    (implies (and (atom-alpha-related-p new-a a r)
                  (atom-alpha-fresh-p new-a a r b))
             (equal (atom-free-expr-vars new-a)
                    (rename-var-string-set (atom-free-expr-vars a)
                                           (var-renamings->expr r))))
    :flag atom-alpha-fresh-p)

  (defthm atom-list-free-expr-vars-of-alpha-related
    (implies (and (atom-list-alpha-related-p new-a a r)
                  (atom-list-alpha-fresh-p new-a a r b))
             (equal (atom-list-free-expr-vars new-a)
                    (rename-var-string-set (atom-list-free-expr-vars a)
                                           (var-renamings->expr r))))
    :flag atom-list-alpha-fresh-p)

  (defthm bind-free-expr-vars-of-alpha-related
    (implies (and (bind-alpha-related-p new-b b r)
                  (bind-alpha-fresh-p new-b b r bset))
             (equal (bind-free-expr-vars new-b)
                    (rename-var-string-set (bind-free-expr-vars b)
                                           (var-renamings->expr r))))
    :flag bind-alpha-fresh-p)

  (defthm bind-list-free-expr-vars-of-alpha-related
    (implies (and (bind-list-alpha-related-p new-b b r)
                  (bind-list-alpha-fresh-p new-b b r bset))
             (equal (bind-list-free-expr-vars new-b)
                    (rename-var-string-set (bind-list-free-expr-vars b)
                                           (var-renamings->expr r))))
    :flag bind-list-alpha-fresh-p)

  :hints
  (("Goal"
    :in-theory
    (e/d (expr-kind-when-expr-alpha-related-p
            atom-kind-when-atom-alpha-related-p
            bind-kind-when-bind-alpha-related-p
            bind-alpha-related-p
            bind-alpha-fresh-p
            expr-free-expr-vars
            expr-list-free-expr-vars
            atom-free-expr-vars
            atom-list-free-expr-vars
            bind-free-expr-vars
            bind-list-free-expr-vars
            bind-bound-expr-vars
            bind-list-bound-expr-vars
            bind-alpha-extended-renamings
            bind-name
            name-fresh-ok
            bind-nocapture-ok
            rename-var-string-set-of-union
            rename-var-string-set-of-singleton
            delete-of-rename-var-string-set-of-extend-renaming
            delete-of-free-vars-when-equal-image
            difference-of-free-vars-when-equal-image-list
            difference-of-free-vars-when-equal-image-binds
            delete-of-rename-var-string-set-of-extend-renaming-subset
            difference-of-rename-var-string-set-of-extend-renaming-list
            difference-of-bind-list-image-expr
            set::difference-insert-y)
         (no-duplicatesp-equal-when-no-duplicatesp-equal-of-ispace-var-list->name
          no-duplicatesp-equal-when-no-duplicatesp-equal-of-type-var-list->name
          member-equal
          acl2::consp-when-member-equal-of-cons-listp
          acl2::subsetp-car-member
          set::mergesort-set-identity
          not-in-ispace-var-set-when-name-not-in-names
          not-in-type-var-set-when-name-not-in-names
          set::in-tail))
    :expand ((expr-alpha-related-p new-x x r)
             (expr-list-alpha-related-p new-x x r)
             (atom-alpha-related-p new-a a r)
             (atom-list-alpha-related-p new-a a r)
             (bind-alpha-related-p new-b b r)
             (bind-list-alpha-related-p new-b b r)
             (expr-alpha-fresh-p new-x x r b)
             (expr-list-alpha-fresh-p new-x x r b)
             (atom-alpha-fresh-p new-a a r b)
             (atom-list-alpha-fresh-p new-a a r b)
             (bind-alpha-fresh-p new-b b r bset)
             (bind-list-alpha-fresh-p new-b b r bset)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The free-variable correspondence, type-variable namespace.  Unlike the
; expression namespace, embedded type annotations contribute free type
; variables, so the leaf cases consume the deterministic free-variable
; theorems for renamed types (whose no-capture hypotheses come from the
; fold's TYPE-FRESH-OK conjuncts).

; An alpha-extension over empty parameter lists is the identity: this
; collapses the branches of the combined function binding where the
; optional type or ispace parameter lists are absent.

(defrule type-var-list-alpha-extend-of-nil
  (and (mv-nth 0 (type-var-list-alpha-extend nil nil atom-m array-m))
       (equal (mv-nth 1 (type-var-list-alpha-extend nil nil atom-m array-m))
              (string-string-map-fix atom-m))
       (equal (mv-nth 2 (type-var-list-alpha-extend nil nil atom-m array-m))
              (string-string-map-fix array-m)))
  :enable type-var-list-alpha-extend)

(defrule ispace-var-list-alpha-extend-of-nil
  (and (mv-nth 0 (ispace-var-list-alpha-extend nil nil dim-m shape-m))
       (equal (mv-nth 1 (ispace-var-list-alpha-extend nil nil dim-m shape-m))
              (string-string-map-fix dim-m))
       (equal (mv-nth 2 (ispace-var-list-alpha-extend nil nil dim-m shape-m))
              (string-string-map-fix shape-m)))
  :enable ispace-var-list-alpha-extend)

; An ispace renaming does not touch free TYPE variables.  This is proved
; in renaming-evaluation.lisp for types and lists of types; the combined
; function binding also renames its parameter annotations, so we lift it
; to optional types and to parameter lists.

; Rebinding parameter NAMES keeps the type annotations, hence the free
; type variables; and renaming type variables in the annotations obeys
; the image law (the parameter-list analogue of
; FREE-TYPE-VARS-OF-TYPE-RENAME-TYPE-VARS).

; The bridge rules: keyed on the term surrounding the inductive
; hypothesis's subject, with the hypothesis matched from the context.

; The unary binder bridges are keyed on the DELETE of the (accessor-
; form) tagged variable, since the goals carry accessors like
; (bind-type->var (car new-b)), never constructor forms.  The kept-name
; case (new variable = old variable, extension with equal names) is
; covered by the same rules.

(defruled delete-of-free-type-vars-when-equal-image-atom
  (implies (and (equal fnew (type-var-set-rename-type-vars
                             fold
                             (extend-renaming (type-var-atom->name v-old)
                                              (type-var-atom->name v)
                                              atom-m)
                             array-m))
                (type-var-setp fold)
                (type-varp v)
                (type-varp v-old)
                (equal (type-var-kind v) :atom)
                (equal (type-var-kind v-old) :atom)
                (not (set::in v (type-var-set-rename-type-vars
                                 (set::delete v-old fold)
                                 atom-m array-m))))
           (equal (set::delete v fnew)
                  (type-var-set-rename-type-vars
                   (set::delete v-old fold)
                   atom-m array-m)))
  :enable (type-var->name)
  :use ((:instance delete-of-type-var-set-rename-type-vars-of-atom-extend
                   (s fold)
                   (n (type-var-atom->name v-old))
                   (n2 (type-var-atom->name v)))
        (:instance type-var-fix-when-atom (x v))
        (:instance type-var-fix-when-atom (x v-old))))

(defruled delete-of-free-type-vars-when-equal-image-array
  (implies (and (equal fnew (type-var-set-rename-type-vars
                             fold
                             atom-m
                             (extend-renaming (type-var-array->name v-old)
                                              (type-var-array->name v)
                                              array-m)))
                (type-var-setp fold)
                (type-varp v)
                (type-varp v-old)
                (equal (type-var-kind v) :array)
                (equal (type-var-kind v-old) :array)
                (not (set::in v (type-var-set-rename-type-vars
                                 (set::delete v-old fold)
                                 atom-m array-m))))
           (equal (set::delete v fnew)
                  (type-var-set-rename-type-vars
                   (set::delete v-old fold)
                   atom-m array-m)))
  :enable (type-var->name)
  :use ((:instance delete-of-type-var-set-rename-type-vars-of-array-extend
                   (s fold)
                   (n (type-var-array->name v-old))
                   (n2 (type-var-array->name v)))
        (:instance type-var-fix-when-array (x v))
        (:instance type-var-fix-when-array (x v-old))))

; Kept-name variants: when the binder keeps its name, the goal's
; extension carries the OLD name term twice (the kept-name equality
; rewrites the new side), so the general bridges fail to match
; syntactically.  These are keyed the same way but with a single name
; variable; the old-side variable is bound by matching the no-capture
; literal.

(defruled delete-of-free-type-vars-when-equal-image-atom-kept
  (implies (and (equal fnew (type-var-set-rename-type-vars
                             fold (extend-renaming nm nm atom-m)
                             array-m))
                (not (set::in v (type-var-set-rename-type-vars
                                 (set::delete v-old fold)
                                 atom-m array-m)))
                (type-var-setp fold)
                (type-varp v)
                (type-varp v-old)
                (equal (type-var-kind v) :atom)
                (equal (type-var-kind v-old) :atom)
                (equal (type-var->name v) nm)
                (equal (type-var->name v-old) nm))
           (equal (set::delete v fnew)
                  (type-var-set-rename-type-vars
                   (set::delete v-old fold)
                   atom-m array-m)))
  :enable (type-var->name)
  :disable (type-var-atom-of-fields)
  :cases ((equal v v-old))
  :use ((:instance delete-of-type-var-set-rename-type-vars-of-atom-extend
                   (s fold) (n nm) (n2 nm))
        (:instance type-var-fix-when-atom (x v))
        (:instance type-var-equal-by-atom-name (x v) (y v-old))))

(defruled delete-of-free-type-vars-when-equal-image-array-kept
  (implies (and (equal fnew (type-var-set-rename-type-vars
                             fold atom-m
                             (extend-renaming nm nm array-m)))
                (not (set::in v (type-var-set-rename-type-vars
                                 (set::delete v-old fold)
                                 atom-m array-m)))
                (type-var-setp fold)
                (type-varp v)
                (type-varp v-old)
                (equal (type-var-kind v) :array)
                (equal (type-var-kind v-old) :array)
                (equal (type-var->name v) nm)
                (equal (type-var->name v-old) nm))
           (equal (set::delete v fnew)
                  (type-var-set-rename-type-vars
                   (set::delete v-old fold)
                   atom-m array-m)))
  :enable (type-var->name)
  :disable (type-var-array-of-fields)
  :cases ((equal v v-old))
  :use ((:instance delete-of-type-var-set-rename-type-vars-of-array-extend
                   (s fold) (n nm) (n2 nm))
        (:instance type-var-fix-when-array (x v))
        (:instance type-var-equal-by-array-name (x v) (y v-old))))

; Generic-accessor duplicates: extensions built by
; BIND-ALPHA-EXTENDED-RENAMINGS carry (TYPE-VAR->NAME ...) terms, while
; those built by the ALPHA-EXTEND functions carry the kind-specific
; accessors; both forms occur in the goals.

(defruled delete-of-free-type-vars-when-equal-image-atom-gen
  (implies (and (equal fnew (type-var-set-rename-type-vars
                             fold
                             (extend-renaming (type-var->name v-old)
                                              (type-var->name v)
                                              atom-m)
                             array-m))
                (type-var-setp fold)
                (type-varp v)
                (type-varp v-old)
                (equal (type-var-kind v) :atom)
                (equal (type-var-kind v-old) :atom)
                (not (set::in v (type-var-set-rename-type-vars
                                 (set::delete v-old fold)
                                 atom-m array-m))))
           (equal (set::delete v fnew)
                  (type-var-set-rename-type-vars
                   (set::delete v-old fold)
                   atom-m array-m)))
  :enable (type-var->name)
  :use ((:instance delete-of-free-type-vars-when-equal-image-atom)))

(defruled delete-of-free-type-vars-when-equal-image-array-gen
  (implies (and (equal fnew (type-var-set-rename-type-vars
                             fold
                             atom-m
                             (extend-renaming (type-var->name v-old)
                                              (type-var->name v)
                                              array-m)))
                (type-var-setp fold)
                (type-varp v)
                (type-varp v-old)
                (equal (type-var-kind v) :array)
                (equal (type-var-kind v-old) :array)
                (not (set::in v (type-var-set-rename-type-vars
                                 (set::delete v-old fold)
                                 atom-m array-m))))
           (equal (set::delete v fnew)
                  (type-var-set-rename-type-vars
                   (set::delete v-old fold)
                   atom-m array-m)))
  :enable (type-var->name)
  :use ((:instance delete-of-free-type-vars-when-equal-image-array)))

; Annotation bridge: the goals carry the annotation equality with a
; compound left-hand side and a projection sandwich (the optional-type
; renaming returns a type that is re-projected), so we key on the
; free-variables-of-projection term and match the equality from the
; context.

(defruled difference-of-free-type-vars-when-equal-image-list
  (implies (and (equal fnew
                       (type-var-set-rename-type-vars
                        fold
                        (mv-nth 1 (type-var-list-alpha-extend
                                   new-params params atom-m array-m))
                        (mv-nth 2 (type-var-list-alpha-extend
                                   new-params params atom-m array-m))))
                (type-var-setp fold)
                (type-var-listp params)
                (type-var-listp new-params)
                (equal (len params) (len new-params))
                (no-duplicatesp-equal new-params)
                (mv-nth 0 (type-var-list-alpha-extend new-params params
                                                      atom-m array-m))
                (set::emptyp
                 (set::intersect
                  (set::mergesort new-params)
                  (type-var-set-rename-type-vars
                   (set::difference fold (set::mergesort params))
                   atom-m array-m))))
           (equal (set::difference fnew (set::mergesort new-params))
                  (type-var-set-rename-type-vars
                   (set::difference fold (set::mergesort params))
                   atom-m array-m)))
  :enable difference-of-type-var-set-rename-type-vars-of-alpha-extend)

(defruled difference-of-free-type-vars-when-equal-image-binds
  (implies (and (equal fnew
                       (type-var-set-rename-type-vars
                        fold
                        (var-renamings->atom
                         (bind-list-alpha-extended-renamings new-binds
                                                             binds r))
                        (var-renamings->array
                         (bind-list-alpha-extended-renamings new-binds
                                                             binds r))))
                (bind-listp binds)
                (bind-listp new-binds)
                (type-var-setp fold)
                (bind-list-alpha-related-p new-binds binds r)
                (bind-list-body-scope-fresh-ok new-binds binds r
                                               evars fold ivars))
           (equal (set::difference fnew
                                   (bind-list-bound-type-vars new-binds))
                  (type-var-set-rename-type-vars
                   (set::difference fold
                                    (bind-list-bound-type-vars binds))
                   (var-renamings->atom r)
                   (var-renamings->array r))))
  :enable difference-of-bind-list-image-type)

; Result-type and parameter-list bridges for the function bindings,
; whose conclusions mention the new components opaquely (the equalities
; from the relation have compound left-hand sides).

; The fold's annotation conjuncts imply no-capture of the type-variable
; renaming on the ispace-renamed parameter list; in the goals the
; renamings appear either as a constructed bundle (the extended inner
; renamings of a combined function binding) or as accessors of a plain
; bundle, so both forms are provided.

(defruled var+type?-list-annotations-no-capture-when-types-fresh-ok
  (implies (var+type?-list-types-fresh-ok
            params
            (var-renamings dim-m shape-m atom-m array-m expr-m avoid))
           (var+type?-list-rename-type-vars-no-capture-p
            (var+type?-list-rename-ispace-vars params dim-m shape-m)
            atom-m array-m))
  :induct (len params)
  :enable (type-option-some->val-when-typep
           var+type?-list-types-fresh-ok
           type-option-fresh-ok
           type-fresh-ok
           var+type?-list-rename-ispace-vars
           var+type?-rename-ispace-vars
           type-option-rename-ispace-vars
           var+type?-list-rename-type-vars-no-capture-p
           var+type?-rename-type-vars-no-capture-p
           type-option-rename-type-vars-no-capture-p))

(defruled var+type?-list-annotations-no-capture-when-types-fresh-ok-acc
  (implies (var+type?-list-types-fresh-ok params r)
           (var+type?-list-rename-type-vars-no-capture-p
            (var+type?-list-rename-ispace-vars params
                                               (var-renamings->dim r)
                                               (var-renamings->shape r))
            (var-renamings->atom r)
            (var-renamings->array r)))
  :use ((:instance var+type?-list-annotations-no-capture-when-types-fresh-ok
                   (dim-m (var-renamings->dim r))
                   (shape-m (var-renamings->shape r))
                   (atom-m (var-renamings->atom r))
                   (array-m (var-renamings->array r))
                   (expr-m (var-renamings->expr r))
                   (avoid (var-renamings->avoid r)))))

; A successful parameter-correspondence extension implies equal lengths.

(defrule len-when-type-var-list-alpha-extend-okp
  (implies (mv-nth 0 (type-var-list-alpha-extend new-params params
                                                 atom-m array-m))
           (equal (len new-params) (len params)))
  :induct (type-var-list-alpha-extend new-params params atom-m array-m)
  :enable (type-var-list-alpha-extend len))

; Type-list annotations (n-ary type application, combined application).

(defruled type-list-no-capture-when-type-list-fresh-ok
  (implies (type-list-fresh-ok tys r)
           (and (type-list-rename-ispace-vars-no-capture-p
                 tys
                 (var-renamings->dim r)
                 (var-renamings->shape r))
                (type-list-rename-type-vars-no-capture-p
                 (type-list-rename-ispace-vars tys
                                               (var-renamings->dim r)
                                               (var-renamings->shape r))
                 (var-renamings->atom r)
                 (var-renamings->array r))))
  :induct (len tys)
  :enable (type-list-fresh-ok
           type-fresh-ok
           type-list-rename-ispace-vars
           type-list-rename-ispace-vars-no-capture-p
           type-list-rename-type-vars-no-capture-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm-exprs-alpha-fresh-p-flag

  (defthm expr-free-type-vars-of-alpha-related
    (implies (and (expr-alpha-related-p new-x x r)
                  (expr-alpha-fresh-p new-x x r b))
             (equal (expr-free-type-vars new-x)
                    (type-var-set-rename-type-vars
                     (expr-free-type-vars x)
                     (var-renamings->atom r)
                     (var-renamings->array r))))
    :flag expr-alpha-fresh-p)

  (defthm expr-list-free-type-vars-of-alpha-related
    (implies (and (expr-list-alpha-related-p new-x x r)
                  (expr-list-alpha-fresh-p new-x x r b))
             (equal (expr-list-free-type-vars new-x)
                    (type-var-set-rename-type-vars
                     (expr-list-free-type-vars x)
                     (var-renamings->atom r)
                     (var-renamings->array r))))
    :flag expr-list-alpha-fresh-p)

  (defthm atom-free-type-vars-of-alpha-related
    (implies (and (atom-alpha-related-p new-a a r)
                  (atom-alpha-fresh-p new-a a r b))
             (equal (atom-free-type-vars new-a)
                    (type-var-set-rename-type-vars
                     (atom-free-type-vars a)
                     (var-renamings->atom r)
                     (var-renamings->array r))))
    :flag atom-alpha-fresh-p)

  (defthm atom-list-free-type-vars-of-alpha-related
    (implies (and (atom-list-alpha-related-p new-a a r)
                  (atom-list-alpha-fresh-p new-a a r b))
             (equal (atom-list-free-type-vars new-a)
                    (type-var-set-rename-type-vars
                     (atom-list-free-type-vars a)
                     (var-renamings->atom r)
                     (var-renamings->array r))))
    :flag atom-list-alpha-fresh-p)

  (defthm bind-free-type-vars-of-alpha-related
    (implies (and (bind-alpha-related-p new-b b r)
                  (bind-alpha-fresh-p new-b b r bset))
             (equal (bind-free-type-vars new-b)
                    (type-var-set-rename-type-vars
                     (bind-free-type-vars b)
                     (var-renamings->atom r)
                     (var-renamings->array r))))
    :flag bind-alpha-fresh-p)

  (defthm bind-list-free-type-vars-of-alpha-related
    (implies (and (bind-list-alpha-related-p new-b b r)
                  (bind-list-alpha-fresh-p new-b b r bset))
             (equal (bind-list-free-type-vars new-b)
                    (type-var-set-rename-type-vars
                     (bind-list-free-type-vars b)
                     (var-renamings->atom r)
                     (var-renamings->array r))))
    :flag bind-list-alpha-fresh-p)

  :hints
  (("Goal"
    :in-theory
    (e/d (expr-kind-when-expr-alpha-related-p
            atom-kind-when-atom-alpha-related-p
            bind-kind-when-bind-alpha-related-p
            bind-alpha-related-p
            bind-alpha-fresh-p
            expr-free-type-vars
            expr-list-free-type-vars
            atom-free-type-vars
            atom-list-free-type-vars
            bind-free-type-vars
            bind-list-free-type-vars
            bind-bound-type-vars
            bind-list-bound-type-vars
            ; TYPE-FREE-TYPE-VARS and TYPE-LIST-FREE-TYPE-VARS are
            ; deliberately left disabled: the type annotations are
            ; handled as black boxes by the FREE-TYPE-VARS-OF-RENAMED-
            ; TYPE... rules below, and opening these two recursive
            ; definitions instead re-derives those facts inside every
            ; case of the induction (about a quarter of this proof).
            ; The OPTION wrappers below are still needed, to strip the
            ; SOME/NONE around the annotations.
            type-option-free-type-vars
            type-list-option-free-type-vars
            var+type?-free-type-vars
            var+type?-list-free-type-vars
            type-rename-all-vars
            type-option-rename-all-vars
            type-list-rename-all-vars
            type-list-option-rename-all-vars
            var+type?-list-rename-all-vars
            type-option-rename-type-vars
            type-list-option-rename-type-vars
            type-option-rename-ispace-vars
            type-list-option-rename-ispace-vars
            type-fresh-ok
            type-option-fresh-ok
            type-list-fresh-ok
            type-list-option-fresh-ok
            var+type?-list-types-fresh-ok
            bind-alpha-extended-renamings
            type-var-list-alpha-extend
            ispace-var-list-alpha-extend
            bind-name
            name-fresh-ok
            bind-nocapture-ok
            type-var-set-rename-type-vars-of-union
            delete-of-free-type-vars-when-equal-image-atom
            delete-of-free-type-vars-when-equal-image-array
            delete-of-free-type-vars-when-equal-image-atom-kept
            delete-of-free-type-vars-when-equal-image-array-kept
            delete-of-free-type-vars-when-equal-image-atom-gen
            delete-of-free-type-vars-when-equal-image-array-gen
            difference-of-free-type-vars-when-equal-image-list
            difference-of-free-type-vars-when-equal-image-binds
            free-type-vars-of-projected-renamed-annotation
            free-type-vars-of-renamed-type-when-equal
            free-type-vars-of-renamed-type-list-when-equal
            type-list-no-capture-when-type-list-fresh-ok
            free-type-vars-of-set-vars-renamed-params
            var+type?-list-annotations-no-capture-when-types-fresh-ok
            var+type?-list-annotations-no-capture-when-types-fresh-ok-acc
            set::difference-insert-y)
         (no-duplicatesp-equal-when-no-duplicatesp-equal-of-ispace-var-list->name
          no-duplicatesp-equal-when-no-duplicatesp-equal-of-type-var-list->name
          member-equal
          acl2::consp-when-member-equal-of-cons-listp
          acl2::subsetp-car-member
          set::mergesort-set-identity
          not-in-ispace-var-set-when-name-not-in-names
          not-in-type-var-set-when-name-not-in-names
          set::in-tail))
    :expand ((expr-alpha-related-p new-x x r)
             (expr-list-alpha-related-p new-x x r)
             (atom-alpha-related-p new-a a r)
             (atom-list-alpha-related-p new-a a r)
             (bind-alpha-related-p new-b b r)
             (bind-list-alpha-related-p new-b b r)
             (expr-alpha-fresh-p new-x x r b)
             (expr-list-alpha-fresh-p new-x x r b)
             (atom-alpha-fresh-p new-a a r b)
             (atom-list-alpha-fresh-p new-a a r b)
             (bind-alpha-fresh-p new-b b r bset)
             (bind-list-alpha-fresh-p new-b b r bset)))
   (and acl2::stable-under-simplificationp
        (member-eq 'bind-cfun->params$inline
                   (acl2::all-fnnames-lst clause))
        '(:use ((:instance difference-of-type-var-set-rename-type-vars-of-alpha-extend
                           (s (set::union
                               (var+type?-list-free-type-vars
                                (bind-cfun->params b))
                               (set::union
                                (type-free-type-vars (bind-cfun->type b))
                                (expr-free-type-vars
                                 (bind-cfun->expr b)))))
                           (params (type-var-list-option-some->val
                                    (bind-cfun->tparams? b)))
                           (new-params (type-var-list-option-some->val
                                        (bind-cfun->tparams? new-b)))
                           (atom-m (var-renamings->atom r))
                           (array-m (var-renamings->array r))))))
   (and acl2::stable-under-simplificationp
        (member-eq 'bind-tfun->params$inline
                   (acl2::all-fnnames-lst clause))
        '(:use ((:instance difference-of-type-var-set-rename-type-vars-of-alpha-extend
                           (s (set::union
                               (type-free-type-vars
                                (type-option-some->val
                                 (bind-tfun->type? b)))
                               (expr-free-type-vars
                                (bind-tfun->expr b))))
                           (params (bind-tfun->params b))
                           (new-params (bind-tfun->params new-b))
                           (atom-m (var-renamings->atom r))
                           (array-m (var-renamings->array r))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The free-variable correspondence, ispace-variable namespace.
;
; Structural differences from the type namespace: type binders (tlambda
; etc.) extend only the atom/array maps and so are invariant here; the
; active binders are the ispace ones (ilambda, unbox, ifun, and the
; ispace parameters of cfun).  Embedded types contribute free ispace
; variables through their dimensions, and ispace ARGUMENTS (iapp, box,
; and friends) contribute directly; the image laws for the latter are
; hypothesis-free since ispaces have no binders.

(defrule len-when-ispace-var-list-alpha-extend-okp
  (implies (mv-nth 0 (ispace-var-list-alpha-extend new-params params
                                                   dim-m shape-m))
           (equal (len new-params) (len params)))
  :induct (ispace-var-list-alpha-extend new-params params dim-m shape-m)
  :enable (ispace-var-list-alpha-extend len))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Unary binder bridges, kind-specific accessor forms.

(defruled delete-of-free-ispace-vars-when-equal-image-dim
  (implies (and (equal fnew (ispace-var-set-rename-ispace-vars
                             fold
                             (extend-renaming (ispace-var-dim->name v-old)
                                              (ispace-var-dim->name v)
                                              dim-m)
                             shape-m))
                (ispace-var-setp fold)
                (ispace-varp v)
                (ispace-varp v-old)
                (equal (ispace-var-kind v) :dim)
                (equal (ispace-var-kind v-old) :dim)
                (not (set::in v (ispace-var-set-rename-ispace-vars
                                 (set::delete v-old fold)
                                 dim-m shape-m))))
           (equal (set::delete v fnew)
                  (ispace-var-set-rename-ispace-vars
                   (set::delete v-old fold)
                   dim-m shape-m)))
  :enable (ispace-var->name)
  :use ((:instance delete-of-ispace-var-set-rename-ispace-vars-of-dim-extend
                   (s fold)
                   (n (ispace-var-dim->name v-old))
                   (n2 (ispace-var-dim->name v)))
        (:instance ispace-var-fix-when-dim (x v))
        (:instance ispace-var-fix-when-dim (x v-old))))

(defruled delete-of-free-ispace-vars-when-equal-image-shape
  (implies (and (equal fnew (ispace-var-set-rename-ispace-vars
                             fold
                             dim-m
                             (extend-renaming (ispace-var-shape->name v-old)
                                              (ispace-var-shape->name v)
                                              shape-m)))
                (ispace-var-setp fold)
                (ispace-varp v)
                (ispace-varp v-old)
                (equal (ispace-var-kind v) :shape)
                (equal (ispace-var-kind v-old) :shape)
                (not (set::in v (ispace-var-set-rename-ispace-vars
                                 (set::delete v-old fold)
                                 dim-m shape-m))))
           (equal (set::delete v fnew)
                  (ispace-var-set-rename-ispace-vars
                   (set::delete v-old fold)
                   dim-m shape-m)))
  :enable (ispace-var->name)
  :use ((:instance delete-of-ispace-var-set-rename-ispace-vars-of-shape-extend
                   (s fold)
                   (n (ispace-var-shape->name v-old))
                   (n2 (ispace-var-shape->name v)))
        (:instance ispace-var-fix-when-shape (x v))
        (:instance ispace-var-fix-when-shape (x v-old))))

; Generic-accessor duplicates (extensions built through BIND-NAME).

(defruled delete-of-free-ispace-vars-when-equal-image-dim-gen
  (implies (and (equal fnew (ispace-var-set-rename-ispace-vars
                             fold
                             (extend-renaming (ispace-var->name v-old)
                                              (ispace-var->name v)
                                              dim-m)
                             shape-m))
                (ispace-var-setp fold)
                (ispace-varp v)
                (ispace-varp v-old)
                (equal (ispace-var-kind v) :dim)
                (equal (ispace-var-kind v-old) :dim)
                (not (set::in v (ispace-var-set-rename-ispace-vars
                                 (set::delete v-old fold)
                                 dim-m shape-m))))
           (equal (set::delete v fnew)
                  (ispace-var-set-rename-ispace-vars
                   (set::delete v-old fold)
                   dim-m shape-m)))
  :enable (ispace-var->name)
  :use ((:instance delete-of-free-ispace-vars-when-equal-image-dim)))

(defruled delete-of-free-ispace-vars-when-equal-image-shape-gen
  (implies (and (equal fnew (ispace-var-set-rename-ispace-vars
                             fold
                             dim-m
                             (extend-renaming (ispace-var->name v-old)
                                              (ispace-var->name v)
                                              shape-m)))
                (ispace-var-setp fold)
                (ispace-varp v)
                (ispace-varp v-old)
                (equal (ispace-var-kind v) :shape)
                (equal (ispace-var-kind v-old) :shape)
                (not (set::in v (ispace-var-set-rename-ispace-vars
                                 (set::delete v-old fold)
                                 dim-m shape-m))))
           (equal (set::delete v fnew)
                  (ispace-var-set-rename-ispace-vars
                   (set::delete v-old fold)
                   dim-m shape-m)))
  :enable (ispace-var->name)
  :use ((:instance delete-of-free-ispace-vars-when-equal-image-shape)))

; Kept-name variants.

(defruled delete-of-free-ispace-vars-when-equal-image-dim-kept
  (implies (and (equal fnew (ispace-var-set-rename-ispace-vars
                             fold (extend-renaming nm nm dim-m)
                             shape-m))
                (not (set::in v (ispace-var-set-rename-ispace-vars
                                 (set::delete v-old fold)
                                 dim-m shape-m)))
                (ispace-var-setp fold)
                (ispace-varp v)
                (ispace-varp v-old)
                (equal (ispace-var-kind v) :dim)
                (equal (ispace-var-kind v-old) :dim)
                (equal (ispace-var->name v) nm)
                (equal (ispace-var->name v-old) nm))
           (equal (set::delete v fnew)
                  (ispace-var-set-rename-ispace-vars
                   (set::delete v-old fold)
                   dim-m shape-m)))
  :enable (ispace-var->name)
  :disable (ispace-var-dim-of-fields)
  :cases ((equal v v-old))
  :use ((:instance delete-of-ispace-var-set-rename-ispace-vars-of-dim-extend
                   (s fold) (n nm) (n2 nm))
        (:instance ispace-var-fix-when-dim (x v))
        (:instance ispace-var-equal-by-dim-name (x v) (y v-old))))

(defruled delete-of-free-ispace-vars-when-equal-image-shape-kept
  (implies (and (equal fnew (ispace-var-set-rename-ispace-vars
                             fold dim-m
                             (extend-renaming nm nm shape-m)))
                (not (set::in v (ispace-var-set-rename-ispace-vars
                                 (set::delete v-old fold)
                                 dim-m shape-m)))
                (ispace-var-setp fold)
                (ispace-varp v)
                (ispace-varp v-old)
                (equal (ispace-var-kind v) :shape)
                (equal (ispace-var-kind v-old) :shape)
                (equal (ispace-var->name v) nm)
                (equal (ispace-var->name v-old) nm))
           (equal (set::delete v fnew)
                  (ispace-var-set-rename-ispace-vars
                   (set::delete v-old fold)
                   dim-m shape-m)))
  :enable (ispace-var->name)
  :disable (ispace-var-shape-of-fields)
  :cases ((equal v v-old))
  :use ((:instance delete-of-ispace-var-set-rename-ispace-vars-of-shape-extend
                   (s fold) (n nm) (n2 nm))
        (:instance ispace-var-fix-when-shape (x v))
        (:instance ispace-var-equal-by-shape-name (x v) (y v-old))))

; The n-ary binder bridge (unboxn, ilambdan, ifun parameter lists).

(defruled difference-of-free-ispace-vars-when-equal-image-list
  (implies (and (equal fnew
                       (ispace-var-set-rename-ispace-vars
                        fold
                        (mv-nth 1 (ispace-var-list-alpha-extend
                                   new-params params dim-m shape-m))
                        (mv-nth 2 (ispace-var-list-alpha-extend
                                   new-params params dim-m shape-m))))
                (ispace-var-setp fold)
                (ispace-var-listp params)
                (ispace-var-listp new-params)
                (equal (len params) (len new-params))
                (no-duplicatesp-equal new-params)
                (mv-nth 0 (ispace-var-list-alpha-extend
                           new-params params dim-m shape-m))
                (set::emptyp
                 (set::intersect
                  (set::mergesort new-params)
                  (ispace-var-set-rename-ispace-vars
                   (set::difference fold (set::mergesort params))
                   dim-m shape-m))))
           (equal (set::difference fnew (set::mergesort new-params))
                  (ispace-var-set-rename-ispace-vars
                   (set::difference fold (set::mergesort params))
                   dim-m shape-m)))
  :enable difference-of-ispace-var-set-rename-ispace-vars-of-alpha-extend)

; The let-scope bridge.

(defruled difference-of-free-ispace-vars-when-equal-image-binds
  (implies (and (equal fnew
                       (ispace-var-set-rename-ispace-vars
                        fold
                        (var-renamings->dim
                         (bind-list-alpha-extended-renamings new-binds
                                                             binds r))
                        (var-renamings->shape
                         (bind-list-alpha-extended-renamings new-binds
                                                             binds r))))
                (bind-listp binds)
                (bind-listp new-binds)
                (ispace-var-setp fold)
                (bind-list-alpha-related-p new-binds binds r)
                (bind-list-body-scope-fresh-ok new-binds binds r
                                               evars tvars fold))
           (equal (set::difference fnew
                                   (bind-list-bound-ispace-vars
                                    new-binds))
                  (ispace-var-set-rename-ispace-vars
                   (set::difference fold
                                    (bind-list-bound-ispace-vars binds))
                   (var-renamings->dim r)
                   (var-renamings->shape r))))
  :enable difference-of-bind-list-image-ispace)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Annotation bridges: the type renaming's second stage does not touch
; free ispace variables (RENAMING-EVALUATION's hypothesis-free
; invariance), so only the ispace no-capture hypothesis is needed.

(defruled type-list-ispace-no-capture-when-type-list-fresh-ok
  (implies (type-list-fresh-ok tys r)
           (type-list-rename-ispace-vars-no-capture-p
            tys
            (var-renamings->dim r)
            (var-renamings->shape r)))
  :induct (len tys)
  :enable (type-list-fresh-ok
           type-fresh-ok
           type-list-rename-ispace-vars-no-capture-p))

; Parameter annotations: the name rebinding and the type-variable
; renaming both leave free ispace variables alone; the ispace renaming
; obeys the image law.

(defruled var+type?-list-annotations-ispace-no-capture-when-types-fresh-ok
  (implies (var+type?-list-types-fresh-ok
            params
            (var-renamings dim-m shape-m atom-m array-m expr-m avoid))
           (var+type?-list-rename-ispace-vars-no-capture-p
            params dim-m shape-m))
  :induct (len params)
  :enable (type-option-some->val-when-typep
           var+type?-list-types-fresh-ok
           type-option-fresh-ok
           type-fresh-ok
           var+type?-list-rename-ispace-vars-no-capture-p
           var+type?-rename-ispace-vars-no-capture-p
           type-option-rename-ispace-vars-no-capture-p))

(defruled var+type?-list-annotations-ispace-no-capture-when-types-fresh-ok-acc
  (implies (var+type?-list-types-fresh-ok params r)
           (var+type?-list-rename-ispace-vars-no-capture-p
            params
            (var-renamings->dim r)
            (var-renamings->shape r)))
  :use ((:instance var+type?-list-annotations-ispace-no-capture-when-types-fresh-ok
                   (dim-m (var-renamings->dim r))
                   (shape-m (var-renamings->shape r))
                   (atom-m (var-renamings->atom r))
                   (array-m (var-renamings->array r))
                   (expr-m (var-renamings->expr r))
                   (avoid (var-renamings->avoid r)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Ispace-argument bridges (hypothesis-free image laws; the compound
; left-hand sides come from the relation's equalities).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm-exprs-alpha-fresh-p-flag

  (defthm expr-free-ispace-vars-of-alpha-related
    (implies (and (expr-alpha-related-p new-x x r)
                  (expr-alpha-fresh-p new-x x r b))
             (equal (expr-free-ispace-vars new-x)
                    (ispace-var-set-rename-ispace-vars
                     (expr-free-ispace-vars x)
                     (var-renamings->dim r)
                     (var-renamings->shape r))))
    :flag expr-alpha-fresh-p)

  (defthm expr-list-free-ispace-vars-of-alpha-related
    (implies (and (expr-list-alpha-related-p new-x x r)
                  (expr-list-alpha-fresh-p new-x x r b))
             (equal (expr-list-free-ispace-vars new-x)
                    (ispace-var-set-rename-ispace-vars
                     (expr-list-free-ispace-vars x)
                     (var-renamings->dim r)
                     (var-renamings->shape r))))
    :flag expr-list-alpha-fresh-p)

  (defthm atom-free-ispace-vars-of-alpha-related
    (implies (and (atom-alpha-related-p new-a a r)
                  (atom-alpha-fresh-p new-a a r b))
             (equal (atom-free-ispace-vars new-a)
                    (ispace-var-set-rename-ispace-vars
                     (atom-free-ispace-vars a)
                     (var-renamings->dim r)
                     (var-renamings->shape r))))
    :flag atom-alpha-fresh-p)

  (defthm atom-list-free-ispace-vars-of-alpha-related
    (implies (and (atom-list-alpha-related-p new-a a r)
                  (atom-list-alpha-fresh-p new-a a r b))
             (equal (atom-list-free-ispace-vars new-a)
                    (ispace-var-set-rename-ispace-vars
                     (atom-list-free-ispace-vars a)
                     (var-renamings->dim r)
                     (var-renamings->shape r))))
    :flag atom-list-alpha-fresh-p)

  (defthm bind-free-ispace-vars-of-alpha-related
    (implies (and (bind-alpha-related-p new-b b r)
                  (bind-alpha-fresh-p new-b b r bset))
             (equal (bind-free-ispace-vars new-b)
                    (ispace-var-set-rename-ispace-vars
                     (bind-free-ispace-vars b)
                     (var-renamings->dim r)
                     (var-renamings->shape r))))
    :flag bind-alpha-fresh-p)

  (defthm bind-list-free-ispace-vars-of-alpha-related
    (implies (and (bind-list-alpha-related-p new-b b r)
                  (bind-list-alpha-fresh-p new-b b r bset))
             (equal (bind-list-free-ispace-vars new-b)
                    (ispace-var-set-rename-ispace-vars
                     (bind-list-free-ispace-vars b)
                     (var-renamings->dim r)
                     (var-renamings->shape r))))
    :flag bind-list-alpha-fresh-p)

  :hints
  (("Goal"
    :in-theory
    (e/d (expr-kind-when-expr-alpha-related-p
            atom-kind-when-atom-alpha-related-p
            bind-kind-when-bind-alpha-related-p
            bind-alpha-related-p
            bind-alpha-fresh-p
            expr-free-ispace-vars
            expr-list-free-ispace-vars
            atom-free-ispace-vars
            atom-list-free-ispace-vars
            bind-free-ispace-vars
            bind-list-free-ispace-vars
            bind-bound-ispace-vars
            bind-list-bound-ispace-vars
            ; Left disabled for the same reason as their type-variable
            ; counterparts above: see FREE-ISPACE-VARS-OF-RENAMED-TYPE...
            type-option-free-ispace-vars
            type-list-option-free-ispace-vars
            var+type?-free-ispace-vars
            var+type?-list-free-ispace-vars
            ispace-list-option-free-ispace-vars
            type-rename-all-vars
            type-option-rename-all-vars
            type-list-rename-all-vars
            type-list-option-rename-all-vars
            var+type?-list-rename-all-vars
            type-option-rename-type-vars
            type-list-option-rename-type-vars
            type-option-rename-ispace-vars
            type-list-option-rename-ispace-vars
            ispace-list-option-rename-ispace-vars
            type-fresh-ok
            type-option-fresh-ok
            type-list-fresh-ok
            type-list-option-fresh-ok
            var+type?-list-types-fresh-ok
            bind-alpha-extended-renamings
            type-var-list-alpha-extend
            ispace-var-list-alpha-extend
            bind-name
            name-fresh-ok
            bind-nocapture-ok
            delete-of-free-ispace-vars-when-equal-image-dim
            delete-of-free-ispace-vars-when-equal-image-shape
            delete-of-free-ispace-vars-when-equal-image-dim-gen
            delete-of-free-ispace-vars-when-equal-image-shape-gen
            delete-of-free-ispace-vars-when-equal-image-dim-kept
            delete-of-free-ispace-vars-when-equal-image-shape-kept
            difference-of-free-ispace-vars-when-equal-image-list
            difference-of-free-ispace-vars-when-equal-image-binds
            free-ispace-vars-of-renamed-type-when-equal
            free-ispace-vars-of-projected-renamed-annotation
            free-ispace-vars-of-renamed-type-list-when-equal
            type-list-ispace-no-capture-when-type-list-fresh-ok
            free-ispace-vars-of-set-vars-renamed-params
            var+type?-list-annotations-ispace-no-capture-when-types-fresh-ok
            var+type?-list-annotations-ispace-no-capture-when-types-fresh-ok-acc
            free-ispace-vars-of-renamed-ispace-when-equal
            free-ispace-vars-of-renamed-ispace-list-when-equal
            difference-of-bind-list-image-ispace
            set::difference-insert-y)
         (no-duplicatesp-equal-when-no-duplicatesp-equal-of-ispace-var-list->name
          no-duplicatesp-equal-when-no-duplicatesp-equal-of-type-var-list->name
          member-equal
          acl2::consp-when-member-equal-of-cons-listp
          acl2::subsetp-car-member
          set::mergesort-set-identity
          not-in-ispace-var-set-when-name-not-in-names
          not-in-type-var-set-when-name-not-in-names
          set::in-tail))
    :expand ((expr-alpha-related-p new-x x r)
             (expr-list-alpha-related-p new-x x r)
             (atom-alpha-related-p new-a a r)
             (atom-list-alpha-related-p new-a a r)
             (bind-alpha-related-p new-b b r)
             (bind-list-alpha-related-p new-b b r)
             (expr-alpha-fresh-p new-x x r b)
             (expr-list-alpha-fresh-p new-x x r b)
             (atom-alpha-fresh-p new-a a r b)
             (atom-list-alpha-fresh-p new-a a r b)
             (bind-alpha-fresh-p new-b b r bset)
             (bind-list-alpha-fresh-p new-b b r bset)))
   (and acl2::stable-under-simplificationp
        (member-eq 'bind-cfun->params$inline
                   (acl2::all-fnnames-lst clause))
        '(:use ((:instance difference-of-ispace-var-set-rename-ispace-vars-of-alpha-extend
                           (s (set::union
                               (var+type?-list-free-ispace-vars
                                (bind-cfun->params b))
                               (set::union
                                (type-free-ispace-vars
                                 (bind-cfun->type b))
                                (expr-free-ispace-vars
                                 (bind-cfun->expr b)))))
                           (params (ispace-var-list-option-some->val
                                    (bind-cfun->iparams? b)))
                           (new-params (ispace-var-list-option-some->val
                                        (bind-cfun->iparams? new-b)))
                           (dim-m (var-renamings->dim r))
                           (shape-m (var-renamings->shape r))))))
   (and acl2::stable-under-simplificationp
        (member-eq 'bind-ifun->params$inline
                   (acl2::all-fnnames-lst clause))
        '(:use ((:instance difference-of-ispace-var-set-rename-ispace-vars-of-alpha-extend
                           (s (set::union
                               (type-option-free-ispace-vars
                                (bind-ifun->type? b))
                               (expr-free-ispace-vars
                                (bind-ifun->expr b))))
                           (params (bind-ifun->params b))
                           (new-params (bind-ifun->params new-b))
                           (dim-m (var-renamings->dim r))
                           (shape-m (var-renamings->shape r))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Design notes: the consumers of these relations, and the review findings
; that shaped the value relation.
;
; (1) The bridge to the uniquification traversal --- PROVED above
;     (UNIQ-ALPHA-BRIDGE and EXPR-ALPHA-RELATED-P-OF-EXPR-UNIQUIFY-NAMES),
;     hypothesis-free, by defret-mutual over UNIQUIFY-NAMES-IMPL (each
;     UNIQ-*-PARAMS result extends the renamings exactly as the
;     *-ALPHA-EXTEND functions do on the resulting name lists).
;
; (2) The freshness bridge --- that the traversal's output also satisfies
;     the freshness companion EXPR-ALPHA-FRESH-P --- PROVED in
;     UNIQUIFY-FRESHNESS.LISP from the crux obligation
;     NAME-FRESH-OK-OF-FRESH-BIND-NAME of the next section.
;
; (3) The groundness collapse: on ground values the relation is equality
;     (ground values contain no lambdas, so neither the AST relation nor
;     the environment relations are reached, and the type values are
;     ground, so their renamings are the identity).  PROVED at the end of
;     this book (EXPR-VALUE-ALPHA-RELATED-VIA-P-WHEN-GROUNDP), on the
;     VALUE-GROUNDP development of value-groundness.lisp.
;
; (4) The main induction over EVAL-EXPRS/ATOMS/BINDS --- PROVED in
;     UNIQUIFY-EVALUATION.LISP (flag theorem EVAL-EXPR-OK-HOLDS and
;     companions, with one DEFUN-SK statement EVAL-*-OK per member of the
;     clique): if the ASTs are alpha-related under R and satisfy the
;     freshness companion at a support set B, and the environments are
;     related via a witness (EXPR-DENV-ALPHA-RELATED-VIA-P), supported
;     (EXPR-DENV-KEYS-SUPPORTED-P), and avoided at the free variables of
;     the AST (EXPR-DENV-ALPHA-AVOIDED-P), then the two evaluations err
;     together and produce alpha-equivalent values
;     (EXPR-VALUE-ALPHA-EQUIV-P).  Its top-level instance --- at the
;     initial environments, with the empty renamings and the primop names
;     as the support set --- and the main theorem
;     EVAL-TOP-EXPR-OF-EXPR-UNIQUIFY-NAMES, which the groundness collapse
;     yields from it, are in UNIQUE-NAMES-VALIDATION.LISP.
;
; The value relation was first drafted (as EXPR-VALUE-ALPHA-RELATED-P,
; since removed from this book) under a single shared renaming R, with the
; lambda cases shaped so that
; closure creation preserves the invariant by construction and
; EVAL-APP-CELL's single-parameter addition matches the EXTEND-RENAMING
; extension, and with the freshness/no-capture conditions kept OUT of the
; relations, as hypotheses to be discharged by the traversal's freshness
; facts.  Two review findings replaced it by the witness-indexed form:
;
;     FIRST REVIEW FINDING (2026-08-05): keeping the freshness/no-capture
;     conditions out of the relations does not survive the application
;     cases of the induction as hypotheses on values.  EVAL-APP-CELL
;     receives only VALUES, so its relational theorem can assume no more
;     than EXPR-VALUE-ALPHA-RELATED-P of the function cells; but that
;     relation admits capturing closures, and the theorem is then false.
;     Counterexample: under R = {p -> p'},
;     the closure <(lambda p'. p'), {p' |-> 5}> is alpha-related to
;     <(lambda q. p), {p |-> 5}> (the body var p renames to p' under the
;     extension {p -> p', q -> p'}, and the captured environments agree at
;     the renamed key), yet applying both to 0 yields 0 on the left and 5
;     on the right --- unrelated ground values.  The binder name p'
;     captures the renamed free occurrence of p.  So the no-capture
;     condition on the left-hand binder names (new name not among the
;     values of the renaming reduced at the binder, recursively) must be
;     carried by the relations themselves (or by a companion "alpha-good"
;     invariant threaded through values); the bridge theorem then acquires
;     the freshness discharge (the traversal's fresh names avoid the maps'
;     values, whose names are all in USED), which UNIQ-EXPR's freshness
;     facts support.  This is what the freshness companion
;     EXPR-ALPHA-FRESH-P and the closure conjuncts of the witness-indexed
;     relation now carry.
;
;     SECOND REVIEW FINDING (continued): adding no-capture
;     conditions is necessary but NOT sufficient --- no strengthening of a
;     SHARED-renaming value relation is inductive, because of shadowing.
;     Counterexample: let the original bind p twice, the outer binder
;     keeping its name under uniquification (so the in-scope map is empty
;     at p) and the inner (lambda p ...) freshened to p1.  Let v, a value
;     mentioning the OUTER p in its embedded syntax (resolved by v's own
;     captured environment), sit in the captured environment of the inner
;     closure.  The inner closures are related under the in-scope R, with
;     v' carrying p (the outer occurrence was KEPT); applying them extends
;     R to R' = R + {p -> p1} for the body, and the induction then needs
;     the captured entries related under R' --- but v' ~_{R'} v is FALSE:
;     R' demands p1 where v' has p, and v''s captured environment is keyed
;     p, not p1.  No freshness condition excludes this; the stale entry
;     {p -> p1} is simply wrong for values created under the OUTER scope.
;     So the environment entries must be related each under its own
;     renaming --- the one in scope where the value was created --- i.e.
;     the value relation needs per-closure/per-entry (existential)
;     renamings, while the shared-R form remains right for single ASTs
;     (one AST, one scope discipline) and the type-value side remains
;     deterministic (uniquification freshens no binders inside embedded
;     types).  With per-entry renamings the application step goes through:
;     the argument entry keeps its own renaming, the body's free variables
;     other than the parameter are read through R unchanged (no-capture
;     excludes collisions with the fresh parameter), and the parameter
;     entry uses the argument pair's own renaming.  Since a defun-sk
;     cannot appear inside the recursive clique, the existential must be
;     realized as an explicit witness argument (a witness structure
;     mirroring the value: a renaming bundle per closure and per
;     environment entry), with a defun-sk wrapper outside the clique; the
;     evaluator theorems then construct witnesses alongside results.
;     This design is realized above by EXPR-VALUE-ALPHA-RELATED-VIA-P and
;     TYPE-VALUE-ALPHA-RELATED-VIA-P and companions (witness fixtypes
;     EXPR-VALUE-WITNESS and TYPE-VALUE-WITNESS etc., existential wrappers
;     TYPE-VALUE-ALPHA-EQUIV-P, EXPR-VALUE-ALPHA-EQUIV-P, and
;     EXPR-DENV-ALPHA-EQUIV-P) --- the per-entry indexing extends to type
;     values, since evaluation composes type values from environment
;     entries with different creation scopes, so a single composed
;     renaming cannot describe a composite result --- with the groundness
;     collapses and the kind/length/dimension consequences proved against
;     them; the main induction is carried out over the witness forms in
;     UNIQUIFY-EVALUATION.LISP.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Freshness bridge: the crux binder-name obligation.
;
; The freshness bridge --- that the output of EXPR-UNIQUIFY-NAMES satisfies
; EXPR-ALPHA-FRESH-P and its companions --- is a DEFRET-MUTUAL over
; UNIQUIFY-NAMES-IMPL in the shape of UNIQ-ALPHA-BRIDGE, but, unlike that
; hypothesis-free bridge, under an invariant relating the traversal's USED,
; renaming maps, and AVOID to the relation's renamings R and support set B.
; The invariant, for the current subterm and (USED, R, B), is: every key
; and value of each of R's five maps is in USED, and the values avoid
; R's AVOID (they are freshly generated names); B is contained in USED
; together with R's AVOID; and every variable occurring in the subterm has
; its name in AVOID (so AVOID = EXPR-ALL-VAR-NAMES of the top expression is
; preserved into subterms, the traversal never changing it).
;
; This section proves the atomic obligation on which every binder case of
; the freshness relation rests: under that invariant, the fresh name that
; FRESH-BIND-NAME produces for a binder satisfies NAME-FRESH-OK against the
; relevant namespace's renaming map and the support set.  It is stated over
; the containments the invariant supplies (map keys and values within USED,
; support set within USED union AVOID).  The rest of the bridge ---
; preservation of the invariant across the recursive calls, the sequential
; *-FRESH-OK lifts over parameter lists, the no-capture conjuncts via the
; preimage-witness lemmas above, the embedded-type *-FRESH-OK layer (which
; is where the values-avoid-AVOID part of the invariant is needed), and
; the main induction --- is in the book UNIQUIFY-FRESHNESS.LISP, ending in
; EXPR-ALPHA-FRESH-P-OF-EXPR-UNIQUIFY-NAMES.
;
; The omap facts the obligation rests on (a submap's values are among the
; map's values, hence a deletion's) are general, and are in the OMAPS book
; of the library extensions; the three set facts below are the membership
; contrapositives the obligation chains through.  All but the obligation
; itself are kept disabled and enabled where needed.

(defrule name-fresh-ok-of-fresh-bind-name
  :short "The fresh name for a binder satisfies @(tsee name-fresh-ok),
          under the bridge invariant on its namespace's renaming map and
          the support set."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the atomic obligation at every binder case of the freshness
     relation.  When @(tsee fresh-bind-name) keeps the name (it was not in
     @('used')), the name differs from nothing and only the
     values-of-delete condition applies, discharged because the map's
     values are within @('used') which the kept name is outside.  When it
     generates a fresh variant (avoiding @('used') and @('avoid')), that
     variant is outside the support set (within @('used') union
     @('avoid')), is not a key (keys within @('used')), and is not a
     value of the reduced map (values within @('used'))."))
  (implies (and (set::subset (omap::keys (string-string-map-fix m))
                             (set::mergesort (str::string-list-fix used)))
                (set::subset (omap::values (string-string-map-fix m))
                             (set::mergesort (str::string-list-fix used)))
                (set::subset (string-sfix b)
                             (set::union
                              (set::mergesort (str::string-list-fix used))
                              (string-sfix avoid))))
           (name-fresh-ok name (fresh-bind-name name used avoid) m b))
  :enable (name-fresh-ok fresh-bind-name
           omap::assoc-to-in-of-keys
           set::in-mergesort-under-iff
           not-in-when-subset-and-not-in-super
           not-in-when-subset-of-union
           not-in-values-of-delete-when-subset)
  :use ((:instance fresh-expr-var-is-fresh
                   (prefix name)
                   (used (set::union
                          (set::mergesort (str::string-list-fix used))
                          (string-sfix avoid))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Alpha-relatedness collapses to equality on ground values.
;
; Ground values (see VALUE-GROUNDNESS) contain no lambdas, so neither the
; AST relation nor the environment relations are reached, and the embedded
; type values are ground, so the renamings that the relations require of
; them are the identity.  The collapse
; (EXPR-VALUE-ALPHA-RELATED-VIA-P-WHEN-GROUNDP) discharges the groundness
; proviso of the main theorem in UNIQUE-NAMES-VALIDATION: the
; induction of UNIQUIFY-EVALUATION yields alpha-related results, which on
; ground values collapse to literal equality.
;
; The local lemmas supply the final step of each case: two values of the
; same kind with equal components have equal fixes.  They are stated as
; conditional equalities of fixes (rather than by enabling the generated
; EXPR-VALUE-FIX-WHEN-* rules) because those rules loop with the enabled
; EXPR-VALUE-*-OF-FIELDS rules.

(defruledl equal-of-expr-value-fix-when-both-base
  (implies (and (equal (expr-value-kind x) :base)
                (equal (expr-value-kind y) :base)
                (equal (expr-value-base->val x) (expr-value-base->val y)))
           (equal (equal (expr-value-fix x) (expr-value-fix y)) t))
  :use ((:instance expr-value-fix-when-base (x x))
        (:instance expr-value-fix-when-base (x y))))

(defruledl equal-of-expr-value-fix-when-both-primop
  (implies (and (equal (expr-value-kind x) :primop)
                (equal (expr-value-kind y) :primop)
                (equal (expr-value-primop->val x) (expr-value-primop->val y)))
           (equal (equal (expr-value-fix x) (expr-value-fix y)) t))
  :use ((:instance expr-value-fix-when-primop (x x))
        (:instance expr-value-fix-when-primop (x y))))

(defruledl equal-of-expr-value-fix-when-both-box
  (implies (and (equal (expr-value-kind x) :box)
                (equal (expr-value-kind y) :box)
                (equal (expr-value-box->ispace x) (expr-value-box->ispace y))
                (equal (expr-value-box->array x) (expr-value-box->array y))
                (equal (expr-value-box->type x) (expr-value-box->type y)))
           (equal (equal (expr-value-fix x) (expr-value-fix y)) t))
  :use ((:instance expr-value-fix-when-box (x x))
        (:instance expr-value-fix-when-box (x y))))

(defruledl equal-of-expr-value-fix-when-both-vector
  (implies (and (equal (expr-value-kind x) :vector)
                (equal (expr-value-kind y) :vector)
                (equal (expr-value-vector->elems x) (expr-value-vector->elems y)))
           (equal (equal (expr-value-fix x) (expr-value-fix y)) t))
  :use ((:instance expr-value-fix-when-vector (x x))
        (:instance expr-value-fix-when-vector (x y))))

(defruledl equal-of-expr-value-fix-when-both-vector-empty
  (implies (and (equal (expr-value-kind x) :vector-empty)
                (equal (expr-value-kind y) :vector-empty)
                (equal (expr-value-vector-empty->dims x)
                       (expr-value-vector-empty->dims y))
                (equal (expr-value-vector-empty->elem x)
                       (expr-value-vector-empty->elem y)))
           (equal (equal (expr-value-fix x) (expr-value-fix y)) t))
  :use ((:instance expr-value-fix-when-vector-empty (x x))
        (:instance expr-value-fix-when-vector-empty (x y))))

(defruledl equal-of-type-value-fix-when-both-base
  (implies (and (equal (type-value-kind x) :base)
                (equal (type-value-kind y) :base)
                (equal (type-value-base->type x) (type-value-base->type y)))
           (equal (equal (type-value-fix x) (type-value-fix y)) t))
  :use ((:instance type-value-fix-when-base (x x))
        (:instance type-value-fix-when-base (x y))))

(defruledl equal-of-type-value-fix-when-both-array
  (implies (and (equal (type-value-kind x) :array)
                (equal (type-value-kind y) :array)
                (equal (type-value-array->elem x) (type-value-array->elem y))
                (equal (type-value-array->dims x) (type-value-array->dims y)))
           (equal (equal (type-value-fix x) (type-value-fix y)) t))
  :use ((:instance type-value-fix-when-array (x x))
        (:instance type-value-fix-when-array (x y))))

(defruledl equal-of-type-value-fix-when-both-fun
  (implies (and (equal (type-value-kind x) :fun)
                (equal (type-value-kind y) :fun)
                (equal (type-value-fun->in x) (type-value-fun->in y))
                (equal (type-value-fun->out x) (type-value-fun->out y)))
           (equal (equal (type-value-fix x) (type-value-fix y)) t))
  :use ((:instance type-value-fix-when-fun (x x))
        (:instance type-value-fix-when-fun (x y))))

(defret-mutual type-value-alpha-related-via-p-when-groundp
  (defret type-value-alpha-related-via-p-when-groundp
    (implies (and yes/no
                  (type-value-groundp tval))
             (equal (type-value-fix new-tval) (type-value-fix tval)))
    :fn type-value-alpha-related-via-p)
  (defret type-value-list-alpha-related-via-p-when-groundp
    (implies (and yes/no
                  (type-value-list-groundp tvals))
             (equal (type-value-list-fix new-tvals)
                    (type-value-list-fix tvals)))
    :fn type-value-list-alpha-related-via-p)
  :mutual-recursion type-value-alpha-related-via-p
  ;; The map and environment members of the clique are skipped: they are
  ;; reached only through universal/product/sum type values, which are
  ;; never ground.
  :skip-others t
  :hints (("Goal"
           :expand ((type-value-alpha-related-via-p new-tval tval w)
                    (type-value-list-alpha-related-via-p new-tvals tvals ws)
                    (type-value-groundp tval)
                    (type-value-list-groundp tvals))
           :in-theory (e/d (equal-of-type-value-fix-when-both-base
                            equal-of-type-value-fix-when-both-array
                            equal-of-type-value-fix-when-both-fun
                            type-value-list-fix$inline)
                           (type-value-alpha-related-via-p
                            type-value-list-alpha-related-via-p)))))

(defruled equal-when-type-value-alpha-related-via-p-groundp
  (implies (and (type-value-alpha-related-via-p new-tval tval w)
                (type-valuep new-tval)
                (type-valuep tval)
                (type-value-groundp tval))
           (equal (equal new-tval tval) t))
  :use type-value-alpha-related-via-p-when-groundp
  :disable type-value-alpha-related-via-p-when-groundp)

(defret-mutual expr-value-alpha-related-via-p-when-groundp
  (defret expr-value-alpha-related-via-p-when-groundp
    (implies (and yes/no
                  (expr-value-groundp val))
             (equal (expr-value-fix new-val) (expr-value-fix val)))
    :fn expr-value-alpha-related-via-p)
  (defret expr-value-list-alpha-related-via-p-when-groundp
    (implies (and yes/no
                  (expr-value-list-groundp vals))
             (equal (expr-value-list-fix new-vals)
                    (expr-value-list-fix vals)))
    :fn expr-value-list-alpha-related-via-p)
  (defret primop-value-alpha-related-via-p-when-groundp
    (implies (and yes/no
                  (primop-value-groundp op))
             (equal (primop-value-fix new-op) (primop-value-fix op)))
    :fn primop-value-alpha-related-via-p)
  :mutual-recursion expr-value-alpha-related-via-p
  ;; The map and environment members of the clique are skipped: they are
  ;; reached only through lambda values, which are never ground.
  :skip-others t
  ;; The primitive-operation case reconstructs both values from their
  ;; fields (the FIX-WHEN rules, disabled by default), which the OF-FIELDS
  ;; rules would immediately undo, so those are disabled here.
  :hints (("Goal"
           :expand ((expr-value-alpha-related-via-p new-val val w)
                    (expr-value-list-alpha-related-via-p new-vals vals ws)
                    (primop-value-alpha-related-via-p new-op op tws ws)
                    (expr-value-groundp val)
                    (expr-value-list-groundp vals)
                    (primop-value-groundp op))
           :in-theory (e/d (equal-of-expr-value-fix-when-both-base
                            equal-of-expr-value-fix-when-both-primop
                            equal-of-expr-value-fix-when-both-box
                            equal-of-expr-value-fix-when-both-vector
                            equal-of-expr-value-fix-when-both-vector-empty
                            equal-when-type-value-alpha-related-via-p-groundp
                            expr-value-list-fix$inline
                            primop-value-fix-when-int-unary
                            primop-value-fix-when-int-binary
                            primop-value-fix-when-int-binary-x
                            primop-value-fix-when-int-rel
                            primop-value-fix-when-int-rel-x
                            primop-value-fix-when-int-to-float
                            primop-value-fix-when-int-to-bool
                            primop-value-fix-when-float-unary
                            primop-value-fix-when-float-binary
                            primop-value-fix-when-float-binary-x
                            primop-value-fix-when-float-rel
                            primop-value-fix-when-float-rel-x
                            primop-value-fix-when-float-truncate
                            primop-value-fix-when-float-round
                            primop-value-fix-when-float-ceiling
                            primop-value-fix-when-float-floor
                            primop-value-fix-when-bool-unary
                            primop-value-fix-when-bool-binary
                            primop-value-fix-when-bool-binary-x
                            primop-value-fix-when-bool-rel
                            primop-value-fix-when-bool-rel-x
                            primop-value-fix-when-bool-to-int
                            primop-value-fix-when-bool-to-float
                            primop-value-fix-when-head
                            primop-value-fix-when-head-t
                            primop-value-fix-when-head-t-d
                            primop-value-fix-when-head-t-d-s
                            primop-value-fix-when-tail
                            primop-value-fix-when-tail-t
                            primop-value-fix-when-tail-t-d
                            primop-value-fix-when-tail-t-d-s
                            primop-value-fix-when-length
                            primop-value-fix-when-length-t
                            primop-value-fix-when-length-t-d
                            primop-value-fix-when-length-t-d-s
                            primop-value-fix-when-append
                            primop-value-fix-when-append-t
                            primop-value-fix-when-append-t-m
                            primop-value-fix-when-append-t-m-n
                            primop-value-fix-when-append-t-m-n-s
                            primop-value-fix-when-append-t-m-n-s-x
                            primop-value-fix-when-reverse
                            primop-value-fix-when-reverse-t
                            primop-value-fix-when-reverse-t-d
                            primop-value-fix-when-reverse-t-d-s
                            primop-value-fix-when-index
                            primop-value-fix-when-index-t
                            primop-value-fix-when-index-t-m
                            primop-value-fix-when-index-t-m-x
                            primop-value-fix-when-index2d
                            primop-value-fix-when-index2d-t
                            primop-value-fix-when-index2d-t-m
                            primop-value-fix-when-index2d-t-m-n
                            primop-value-fix-when-index2d-t-m-n-x
                            primop-value-fix-when-sum
                            primop-value-fix-when-sum-s
                            primop-value-fix-when-reshape
                            primop-value-fix-when-reshape-t
                            primop-value-fix-when-reshape-t-s1
                            primop-value-fix-when-reshape-t-s1-s2
                            primop-value-fix-when-flatten
                            primop-value-fix-when-flatten-t
                            primop-value-fix-when-flatten-t-m
                            primop-value-fix-when-flatten-t-m-n
                            primop-value-fix-when-flatten-t-m-n-s
                            primop-value-fix-when-transpose2d
                            primop-value-fix-when-transpose2d-t
                            primop-value-fix-when-transpose2d-t-m
                            primop-value-fix-when-transpose2d-t-m-n
                            primop-value-fix-when-iota/static
                            primop-value-fix-when-reduce
                            primop-value-fix-when-reduce-t
                            primop-value-fix-when-reduce-t-d
                            primop-value-fix-when-reduce-t-d-s
                            primop-value-fix-when-reduce-t-d-s-f
                            primop-value-fix-when-fold
                            primop-value-fix-when-fold-t
                            primop-value-fix-when-fold-t-t2
                            primop-value-fix-when-fold-t-t2-d
                            primop-value-fix-when-fold-t-t2-d-s
                            primop-value-fix-when-fold-t-t2-d-s-s2
                            primop-value-fix-when-fold-t-t2-d-s-s2-f
                            primop-value-fix-when-fold-t-t2-d-s-s2-f-z
                            primop-value-fix-when-reify-dim
                            primop-value-fix-when-reify-shape
                            primop-value-fix-when-iota
                            primop-value-fix-when-iota-d
                            primop-value-fix-when-trace
                            primop-value-fix-when-trace-t
                            primop-value-fix-when-trace-t-r
                            primop-value-fix-when-trace-t-r-s
                            primop-value-fix-when-trace-t-r-s-q
                            primop-value-fix-when-trace-t-r-s-q-x
                            primop-value-fix-when-undefined
                            primop-value-fix-when-undefined-t)
                           (expr-value-alpha-related-via-p
                            expr-value-list-alpha-related-via-p
                            primop-value-alpha-related-via-p
                            primop-value-int-unary-of-fields
                            primop-value-int-binary-of-fields
                            primop-value-int-binary-x-of-fields
                            primop-value-int-rel-of-fields
                            primop-value-int-rel-x-of-fields
                            primop-value-float-unary-of-fields
                            primop-value-float-binary-of-fields
                            primop-value-float-binary-x-of-fields
                            primop-value-float-rel-of-fields
                            primop-value-float-rel-x-of-fields
                            primop-value-bool-unary-of-fields
                            primop-value-bool-binary-of-fields
                            primop-value-bool-binary-x-of-fields
                            primop-value-bool-rel-of-fields
                            primop-value-bool-rel-x-of-fields
                            primop-value-head-t-of-fields
                            primop-value-head-t-d-of-fields
                            primop-value-head-t-d-s-of-fields
                            primop-value-tail-t-of-fields
                            primop-value-tail-t-d-of-fields
                            primop-value-tail-t-d-s-of-fields
                            primop-value-length-t-of-fields
                            primop-value-length-t-d-of-fields
                            primop-value-length-t-d-s-of-fields
                            primop-value-append-t-of-fields
                            primop-value-append-t-m-of-fields
                            primop-value-append-t-m-n-of-fields
                            primop-value-append-t-m-n-s-of-fields
                            primop-value-append-t-m-n-s-x-of-fields
                            primop-value-reverse-t-of-fields
                            primop-value-reverse-t-d-of-fields
                            primop-value-reverse-t-d-s-of-fields
                            primop-value-index-t-of-fields
                            primop-value-index-t-m-of-fields
                            primop-value-index-t-m-x-of-fields
                            primop-value-index2d-t-of-fields
                            primop-value-index2d-t-m-of-fields
                            primop-value-index2d-t-m-n-of-fields
                            primop-value-index2d-t-m-n-x-of-fields
                            primop-value-sum-s-of-fields
                            primop-value-reshape-t-of-fields
                            primop-value-reshape-t-s1-of-fields
                            primop-value-reshape-t-s1-s2-of-fields
                            primop-value-flatten-t-of-fields
                            primop-value-flatten-t-m-of-fields
                            primop-value-flatten-t-m-n-of-fields
                            primop-value-flatten-t-m-n-s-of-fields
                            primop-value-transpose2d-t-of-fields
                            primop-value-transpose2d-t-m-of-fields
                            primop-value-transpose2d-t-m-n-of-fields
                            primop-value-reduce-t-of-fields
                            primop-value-reduce-t-d-of-fields
                            primop-value-reduce-t-d-s-of-fields
                            primop-value-reduce-t-d-s-f-of-fields
                            primop-value-fold-t-of-fields
                            primop-value-fold-t-t2-of-fields
                            primop-value-fold-t-t2-d-of-fields
                            primop-value-fold-t-t2-d-s-of-fields
                            primop-value-fold-t-t2-d-s-s2-of-fields
                            primop-value-fold-t-t2-d-s-s2-f-of-fields
                            primop-value-fold-t-t2-d-s-s2-f-z-of-fields
                            primop-value-iota-d-of-fields
                            primop-value-trace-t-of-fields
                            primop-value-trace-t-r-of-fields
                            primop-value-trace-t-r-s-of-fields
                            primop-value-trace-t-r-s-q-of-fields
                            primop-value-trace-t-r-s-q-x-of-fields
                            primop-value-undefined-t-of-fields)))))

