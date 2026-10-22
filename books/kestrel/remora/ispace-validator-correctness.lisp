; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-validator")
(include-book "ispace-validity-derived-rules")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ispace-validator-correctness
  :parents (static-semantics)
  :short "Correctness of the ispace validator
          with respect to ispace validity."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove that the "
    (xdoc::seetopic "ispace-validator" "ispace validator")
    " is sound and complete with respect to
     the inference rules in @(see ispace-validity):
     the validator succeeds exactly on the valid
     dimensions, shapes, ispaces, and lists thereof.")
   (xdoc::p
    "The inference rules use ispace contexts,
     which are sets of ispace variables,
     while the validator uses ispace static environments,
     which are maps from ispace variables to optional ispaces,
     where a present ispace is the definition of the variable
     from a @('let') binding.
     The validator only checks whether a variable is in the map,
     i.e. it treats defined variables like all the other variables in scope.
     However, the inference rules for @('let') expressions,
     which we plan to add,
     will most likely substitute the definitions directly,
     so that defined variables will not be in the ispace contexts.
     Thus, for now we restrict the correspondence
     between ispace contexts and ispace static environments
     to the environments without definitions,
     i.e. whose maps have no present optional ispaces.
     These environments are isomorphic to the contexts:
     we define the mappings in the two directions,
     and we prove that they are inverses of each other.")
   (xdoc::p
    "We state soundness and completeness in two forms:
     over ispace contexts,
     running the validator on the environment that corresponds to the context;
     and over ispace static environments,
     applying the inference rules to the context
     that corresponds to the environment.
     Soundness over environments holds for all environments,
     because the validator ignores the definitions,
     and soundness over contexts follows from it by instantiation;
     completeness is proved over contexts,
     and completeness over environments without definitions
     follows from it via the isomorphism.
     We also combine soundness and completeness into equivalences,
     in both forms,
     where the one over environments is restricted to
     environments without definitions.")
   (xdoc::p
    "We plan to generalize this correspondence
     to environments with definitions,
     presumably by regarding the defined variables as not in the context,
     and by expanding the ispaces via the definitions
     before applying the inference rules."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-var-ispace-option-map-no-defs-p
  ((map ispace-var-ispace-option-mapp))
  :returns (yes/no booleanp)
  :short "Check if a map from ispace variables to optional ispaces
          has no definitions, i.e. all its optional ispaces are absent."
  (b* (((when (omap::emptyp (ispace-var-ispace-option-map-fix map))) t)
       ((mv & ispace?) (omap::head map)))
    (and (ispace-option-case ispace? :none)
         (ispace-var-ispace-option-map-no-defs-p (omap::tail map))))

  ///

  (defrule ispace-var-ispace-option-map-no-defs-p-of-update
    (implies (and (ispace-varp var)
                  (ispace-var-ispace-option-mapp map)
                  (ispace-var-ispace-option-map-no-defs-p map))
             (ispace-var-ispace-option-map-no-defs-p
              (omap::update var nil map)))
    :induct (ispace-var-ispace-option-map-no-defs-p map)
    :expand ((ispace-var-ispace-option-map-no-defs-p
              (omap::update var nil map)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-senv-no-defs-p ((ienv ispace-senvp))
  :returns (yes/no booleanp)
  :short "Check if an ispace static environment has no definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when no variable in the environment
     is associated to an ispace."))
  (ispace-var-ispace-option-map-no-defs-p (ispace-senv->ispaces ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-ctx-from-senv ((ienv ispace-senvp))
  :guard (ispace-senv-no-defs-p ienv)
  :returns (ivars ispace-var-setp)
  :short "Ispace context that corresponds to an ispace static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the set of variables in the environment,
     i.e. the keys of the map.
     The guard restricts this operation to environments without definitions,
     the only ones for which the correspondence is meaningful."))
  (omap::keys (ispace-senv->ispaces ienv))
  :prepwork
  ((local
    (in-theory
     (enable ispace-var-setp-of-keys-when-ispace-var-ispace-option-mapp))))

  ///

  (defruled assoc-to-in-of-ispace-ctx-from-senv
    (iff (omap::assoc var (ispace-senv->ispaces ienv))
         (set::in var (ispace-ctx-from-senv ienv)))
    :enable omap::assoc-to-in-of-keys))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-senv-from-ctx ((ivars ispace-var-setp))
  :returns (ienv ispace-senvp)
  :short "Ispace static environment that corresponds to an ispace context."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the environment without definitions
     whose variables are the ones in the context:
     we add each variable, without definition,
     to the initial (empty) environment.")
   (xdoc::p
    "This is the inverse of @(tsee ispace-ctx-from-senv),
     when the latter is restricted to environments without definitions:
     we prove that the two compositions are the identity,
     on all contexts and on environments without definitions respectively.
     The proof of the latter is by induction on the map of the environment,
     whose set of keys is obtained by inserting the smallest key
     into the set of keys of the rest of the map;
     thus, we first prove how this function treats insertion."))
  (b* (((when (set::emptyp (ispace-var-set-fix ivars))) (init-ispace-senv)))
    (ispace-senv-add-var (set::head ivars)
                         (ispace-senv-from-ctx (set::tail ivars))))
  :prepwork ((local (in-theory (enable emptyp-of-ispace-var-set-fix))))
  :verify-guards :after-returns

  ///

  (defrule ispace-senv-no-defs-p-of-ispace-senv-from-ctx
    (ispace-senv-no-defs-p (ispace-senv-from-ctx ivars))
    :induct t
    :enable (ispace-senv-no-defs-p
             ispace-senv-add-var
             init-ispace-senv))

  (defrule ispace-ctx-from-senv-of-ispace-senv-from-ctx
    (equal (ispace-ctx-from-senv (ispace-senv-from-ctx ivars))
           (ispace-var-set-fix ivars))
    :induct t
    :enable (ispace-ctx-from-senv
             ispace-senv-add-var
             init-ispace-senv
             ispace-var-set-fix
             set::emptyp))

  (defruled ispace-senv-from-ctx-of-insert
    (implies (and (ispace-var-setp ivars)
                  (ispace-varp var))
             (equal (ispace-senv-from-ctx (set::insert var ivars))
                    (ispace-senv-add-var var (ispace-senv-from-ctx ivars))))
    :induct (ispace-senv-from-ctx ivars)
    :expand ((ispace-senv-from-ctx (set::insert var ivars)))
    :enable (ispace-senv-add-var
             init-ispace-senv
             set::head-insert
             set::tail-insert))

  (defruled ispace-senv-from-ctx-of-keys
    (implies (and (ispace-var-ispace-option-mapp map)
                  (ispace-var-ispace-option-map-no-defs-p map))
             (equal (ispace-senv-from-ctx (omap::keys map))
                    (ispace-senv map)))
    :induct (ispace-var-ispace-option-map-no-defs-p map)
    :enable (ispace-var-ispace-option-map-no-defs-p
             ispace-senv-from-ctx-of-insert
             ispace-senv-add-var
             init-ispace-senv
             omap::keys
             ispace-var-setp-of-keys-when-ispace-var-ispace-option-mapp))

  (defrule ispace-senv-from-ctx-of-ispace-ctx-from-senv
    (implies (ispace-senv-no-defs-p ienv)
             (equal (ispace-senv-from-ctx (ispace-ctx-from-senv ienv))
                    (ispace-senv-fix ienv)))
    :enable (ispace-senv-no-defs-p
             ispace-ctx-from-senv
             ispace-senv-from-ctx-of-keys)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ispace-validator-soundness
  :short "Soundness of the ispace validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the validator succeeds,
     the dimension, shape, ispace, or list thereof is valid
     according to the inference rules.
     We state this in the two forms described in
     @(see ispace-validator-correctness).")
   (xdoc::p
    "The theorems over environments are proved by induction on the validator.
     They hold for all environments,
     not just for the ones without definitions
     (i.e. not necessarily satisfying
     the guard of @(tsee ispace-ctx-from-senv)),
     because the validator ignores the definitions in the environment;
     we state them without the hypothesis that there are no definitions,
     to record what they actually need.
     The hypotheses that the ASTs have the right types are needed
     because the validity predicates do not fix their arguments,
     while the validator does.
     Each case of the induction knows the AST only by its kind,
     so it is closed by the defining rules combined by kind
     (e.g. @(see dim-validity-rules-by-kind)),
     whose hypotheses mirror the validator's checks.
     The theorems over contexts are instances of the ones over environments,
     with the environment that corresponds to the context."))

  ;; dimensions:

  (defthm-check-dims-flag
    (defthmd dim-ok-of-ispace-ctx-from-senv-when-check-dim
      (implies (and (dimp dim)
                    (check-dim dim ienv))
               (dim-ok (ispace-ctx-from-senv ienv) dim))
      :flag check-dim)
    (defthmd dims-ok-of-ispace-ctx-from-senv-when-check-dim-list
      (implies (and (dim-listp dims)
                    (check-dim-list dims ienv))
               (dims-ok (ispace-ctx-from-senv ienv) dims))
      :flag check-dim-list)
    :hints
    (("Goal"
      :in-theory (enable check-dim
                         check-dim-list
                         dim-ok-by-kind
                         dims-ok-nil
                         dims-ok-cons!
                         assoc-to-in-of-ispace-ctx-from-senv))))

  (defruled dim-ok-when-check-dim-of-ispace-senv-from-ctx
    (implies (and (ispace-var-setp ivars)
                  (dimp dim)
                  (check-dim dim (ispace-senv-from-ctx ivars)))
             (dim-ok ivars dim))
    :use (:instance dim-ok-of-ispace-ctx-from-senv-when-check-dim
                    (ienv (ispace-senv-from-ctx ivars))))

  (defruled dims-ok-when-check-dim-list-of-ispace-senv-from-ctx
    (implies (and (ispace-var-setp ivars)
                  (dim-listp dims)
                  (check-dim-list dims (ispace-senv-from-ctx ivars)))
             (dims-ok ivars dims))
    :use (:instance dims-ok-of-ispace-ctx-from-senv-when-check-dim-list
                    (ienv (ispace-senv-from-ctx ivars))))

  ;; shapes and ispaces:

  (defthm-check-shapes/ispaces-flag
    (defthmd shape-ok-of-ispace-ctx-from-senv-when-check-shape
      (implies (and (shapep shape)
                    (check-shape shape ienv))
               (shape-ok (ispace-ctx-from-senv ienv) shape))
      :flag check-shape)
    (defthmd shapes-ok-of-ispace-ctx-from-senv-when-check-shape-list
      (implies (and (shape-listp shapes)
                    (check-shape-list shapes ienv))
               (shapes-ok (ispace-ctx-from-senv ienv) shapes))
      :flag check-shape-list)
    (defthmd ispace-ok-of-ispace-ctx-from-senv-when-check-ispace
      (implies (and (ispacep ispace)
                    (check-ispace ispace ienv))
               (ispace-ok (ispace-ctx-from-senv ienv) ispace))
      :flag check-ispace)
    (defthmd ispaces-ok-of-ispace-ctx-from-senv-when-check-ispace-list
      (implies (and (ispace-listp ispaces)
                    (check-ispace-list ispaces ienv))
               (ispaces-ok (ispace-ctx-from-senv ienv) ispaces))
      :flag check-ispace-list)
    :hints
    (("Goal"
      :in-theory (enable check-shape
                         check-shape-list
                         check-ispace
                         check-ispace-list
                         dim-ok-of-ispace-ctx-from-senv-when-check-dim
                         dims-ok-of-ispace-ctx-from-senv-when-check-dim-list
                         shape-ok-by-kind
                         ispace-ok-by-kind
                         shapes-ok-nil
                         shapes-ok-cons!
                         ispaces-ok-nil
                         ispaces-ok-cons!
                         assoc-to-in-of-ispace-ctx-from-senv))))

  (defruled shape-ok-when-check-shape-of-ispace-senv-from-ctx
    (implies (and (ispace-var-setp ivars)
                  (shapep shape)
                  (check-shape shape (ispace-senv-from-ctx ivars)))
             (shape-ok ivars shape))
    :use (:instance shape-ok-of-ispace-ctx-from-senv-when-check-shape
                    (ienv (ispace-senv-from-ctx ivars))))

  (defruled shapes-ok-when-check-shape-list-of-ispace-senv-from-ctx
    (implies (and (ispace-var-setp ivars)
                  (shape-listp shapes)
                  (check-shape-list shapes (ispace-senv-from-ctx ivars)))
             (shapes-ok ivars shapes))
    :use (:instance shapes-ok-of-ispace-ctx-from-senv-when-check-shape-list
                    (ienv (ispace-senv-from-ctx ivars))))

  (defruled ispace-ok-when-check-ispace-of-ispace-senv-from-ctx
    (implies (and (ispace-var-setp ivars)
                  (ispacep ispace)
                  (check-ispace ispace (ispace-senv-from-ctx ivars)))
             (ispace-ok ivars ispace))
    :use (:instance ispace-ok-of-ispace-ctx-from-senv-when-check-ispace
                    (ienv (ispace-senv-from-ctx ivars))))

  (defruled ispaces-ok-when-check-ispace-list-of-ispace-senv-from-ctx
    (implies (and (ispace-var-setp ivars)
                  (ispace-listp ispaces)
                  (check-ispace-list ispaces (ispace-senv-from-ctx ivars)))
             (ispaces-ok ivars ispaces))
    :use (:instance ispaces-ok-of-ispace-ctx-from-senv-when-check-ispace-list
                    (ienv (ispace-senv-from-ctx ivars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ispace-validator-completeness
  :short "Completeness of the ispace validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "If a dimension, shape, ispace, or list thereof is valid
     according to the inference rules,
     the validator succeeds on it.
     We state this in the two forms described in
     @(see ispace-validator-correctness).")
   (xdoc::p
    "The main lemmas are about valid proof trees,
     and are proved by induction on the proof validity predicates,
     like @(see dim-validity-holds-only-on-dimensions)
     and the other similar theorems in @(see ispace-validity).
     The lemmas are stated over contexts,
     running the validator on the environment
     that corresponds to the context of the proof tree.
     This form is what makes the induction go through:
     the expansion of the proof validity predicates
     equates the context and the AST of the conclusion
     to the fields of the proof tree,
     and ACL2 substitutes those equations away;
     a form over environments would add a second equation on the context,
     which could not be substituted.
     For the same reason, we do not use the rule induction schemes
     generated by @(tsee definductive)
     (e.g. @('defthm-dim-ok-induction')):
     there the fields are those of the witness proof tree,
     which depends on the AST,
     making the equations circular.")
   (xdoc::p
    "The theorems over contexts follow from the lemmas
     by exposing the witness proof trees of the validity predicates,
     and the theorems over environments without definitions
     are obtained from the ones over contexts via the isomorphism."))

  ;; dimensions:

  (local
   (defthm-dim-ok-proof-validp-clique-flag
     (defthmd check-dim-of-ispace-senv-from-ctx-when-dim-ok-proof-validp
       (implies (dim-ok-proof-validp proof _ivars _dim)
                (check-dim _dim (ispace-senv-from-ctx _ivars)))
       :flag dim-ok-proof-validp)
     (defthmd check-dim-list-of-ispace-senv-from-ctx-when-dims-ok-proof-validp
       (implies (dims-ok-proof-validp proof _ivars _dims)
                (check-dim-list _dims (ispace-senv-from-ctx _ivars)))
       :flag dims-ok-proof-validp)
     :hints
     (("Goal"
       :in-theory (enable* dim-validity-definition-validp-defs
                           check-dim
                           check-dim-list
                           assoc-to-in-of-ispace-ctx-from-senv)))))

  (defruled check-dim-of-ispace-senv-from-ctx-when-dim-ok
    (implies (dim-ok ivars dim)
             (check-dim dim (ispace-senv-from-ctx ivars)))
    :enable (dim-ok
             check-dim-of-ispace-senv-from-ctx-when-dim-ok-proof-validp))

  (defruled check-dim-list-of-ispace-senv-from-ctx-when-dims-ok
    (implies (dims-ok ivars dims)
             (check-dim-list dims (ispace-senv-from-ctx ivars)))
    :enable (dims-ok
             check-dim-list-of-ispace-senv-from-ctx-when-dims-ok-proof-validp))

  (defruled check-dim-when-dim-ok-of-ispace-ctx-from-senv
    (implies (and (ispace-senv-no-defs-p ienv)
                  (dim-ok (ispace-ctx-from-senv ienv) dim))
             (check-dim dim ienv))
    :use (:instance check-dim-of-ispace-senv-from-ctx-when-dim-ok
                    (ivars (ispace-ctx-from-senv ienv))))

  (defruled check-dim-list-when-dims-ok-of-ispace-ctx-from-senv
    (implies (and (ispace-senv-no-defs-p ienv)
                  (dims-ok (ispace-ctx-from-senv ienv) dims))
             (check-dim-list dims ienv))
    :use (:instance check-dim-list-of-ispace-senv-from-ctx-when-dims-ok
                    (ivars (ispace-ctx-from-senv ienv))))

  ;; shapes and ispaces:

  (local
   (defthm-shape-ok-proof-validp-clique-flag
     (defthmd check-shape-of-ispace-senv-from-ctx-when-shape-ok-proof-validp
       (implies (shape-ok-proof-validp proof _ivars _shape)
                (check-shape _shape (ispace-senv-from-ctx _ivars)))
       :flag shape-ok-proof-validp)
     (defthmd
       check-shape-list-of-ispace-senv-from-ctx-when-shapes-ok-proof-validp
       (implies (shapes-ok-proof-validp proof _ivars _shapes)
                (check-shape-list _shapes (ispace-senv-from-ctx _ivars)))
       :flag shapes-ok-proof-validp)
     (defthmd check-ispace-of-ispace-senv-from-ctx-when-ispace-ok-proof-validp
       (implies (ispace-ok-proof-validp proof _ivars _ispace)
                (check-ispace _ispace (ispace-senv-from-ctx _ivars)))
       :flag ispace-ok-proof-validp)
     (defthmd
       check-ispace-list-of-ispace-senv-from-ctx-when-ispaces-ok-proof-validp
       (implies (ispaces-ok-proof-validp proof _ivars _ispaces)
                (check-ispace-list _ispaces (ispace-senv-from-ctx _ivars)))
       :flag ispaces-ok-proof-validp)
     :hints
     (("Goal"
       :in-theory
       (enable* shape/ispace-validity-definition-validp-defs
                check-shape
                check-shape-list
                check-ispace
                check-ispace-list
                assoc-to-in-of-ispace-ctx-from-senv
                check-dim-of-ispace-senv-from-ctx-when-dim-ok
                check-dim-list-of-ispace-senv-from-ctx-when-dims-ok)))))

  (defruled check-shape-of-ispace-senv-from-ctx-when-shape-ok
    (implies (shape-ok ivars shape)
             (check-shape shape (ispace-senv-from-ctx ivars)))
    :enable (shape-ok
             check-shape-of-ispace-senv-from-ctx-when-shape-ok-proof-validp))

  (defruled check-shape-list-of-ispace-senv-from-ctx-when-shapes-ok
    (implies (shapes-ok ivars shapes)
             (check-shape-list shapes (ispace-senv-from-ctx ivars)))
    :enable
    (shapes-ok
     check-shape-list-of-ispace-senv-from-ctx-when-shapes-ok-proof-validp))

  (defruled check-ispace-of-ispace-senv-from-ctx-when-ispace-ok
    (implies (ispace-ok ivars ispace)
             (check-ispace ispace (ispace-senv-from-ctx ivars)))
    :enable (ispace-ok
             check-ispace-of-ispace-senv-from-ctx-when-ispace-ok-proof-validp))

  (defruled check-ispace-list-of-ispace-senv-from-ctx-when-ispaces-ok
    (implies (ispaces-ok ivars ispaces)
             (check-ispace-list ispaces (ispace-senv-from-ctx ivars)))
    :enable
    (ispaces-ok
     check-ispace-list-of-ispace-senv-from-ctx-when-ispaces-ok-proof-validp))

  (defruled check-shape-when-shape-ok-of-ispace-ctx-from-senv
    (implies (and (ispace-senv-no-defs-p ienv)
                  (shape-ok (ispace-ctx-from-senv ienv) shape))
             (check-shape shape ienv))
    :use (:instance check-shape-of-ispace-senv-from-ctx-when-shape-ok
                    (ivars (ispace-ctx-from-senv ienv))))

  (defruled check-shape-list-when-shapes-ok-of-ispace-ctx-from-senv
    (implies (and (ispace-senv-no-defs-p ienv)
                  (shapes-ok (ispace-ctx-from-senv ienv) shapes))
             (check-shape-list shapes ienv))
    :use (:instance check-shape-list-of-ispace-senv-from-ctx-when-shapes-ok
                    (ivars (ispace-ctx-from-senv ienv))))

  (defruled check-ispace-when-ispace-ok-of-ispace-ctx-from-senv
    (implies (and (ispace-senv-no-defs-p ienv)
                  (ispace-ok (ispace-ctx-from-senv ienv) ispace))
             (check-ispace ispace ienv))
    :use (:instance check-ispace-of-ispace-senv-from-ctx-when-ispace-ok
                    (ivars (ispace-ctx-from-senv ienv))))

  (defruled check-ispace-list-when-ispaces-ok-of-ispace-ctx-from-senv
    (implies (and (ispace-senv-no-defs-p ienv)
                  (ispaces-ok (ispace-ctx-from-senv ienv) ispaces))
             (check-ispace-list ispaces ienv))
    :use (:instance check-ispace-list-of-ispace-senv-from-ctx-when-ispaces-ok
                    (ivars (ispace-ctx-from-senv ienv)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ispace-validator-equivalence
  :short "Equivalence of the ispace validator and ispace validity."
  :long
  (xdoc::topstring
   (xdoc::p
    "These combine
     @(see ispace-validator-soundness) and
     @(see ispace-validator-completeness),
     in the two forms described in @(see ispace-validator-correctness).
     The equalities hold because
     both the validator and the validity predicates are boolean-valued."))

  ;; dimensions:

  (defruled check-dim-of-ispace-senv-from-ctx-to-dim-ok
    (implies (and (ispace-var-setp ivars)
                  (dimp dim))
             (equal (check-dim dim (ispace-senv-from-ctx ivars))
                    (dim-ok ivars dim)))
    :use (dim-ok-when-check-dim-of-ispace-senv-from-ctx
          check-dim-of-ispace-senv-from-ctx-when-dim-ok))

  (defruled check-dim-list-of-ispace-senv-from-ctx-to-dims-ok
    (implies (and (ispace-var-setp ivars)
                  (dim-listp dims))
             (equal (check-dim-list dims (ispace-senv-from-ctx ivars))
                    (dims-ok ivars dims)))
    :use (dims-ok-when-check-dim-list-of-ispace-senv-from-ctx
          check-dim-list-of-ispace-senv-from-ctx-when-dims-ok))

  (defruled check-dim-to-dim-ok-of-ispace-ctx-from-senv
    (implies (and (ispace-senv-no-defs-p ienv)
                  (dimp dim))
             (equal (check-dim dim ienv)
                    (dim-ok (ispace-ctx-from-senv ienv) dim)))
    :use (dim-ok-of-ispace-ctx-from-senv-when-check-dim
          check-dim-when-dim-ok-of-ispace-ctx-from-senv))

  (defruled check-dim-list-to-dims-ok-of-ispace-ctx-from-senv
    (implies (and (ispace-senv-no-defs-p ienv)
                  (dim-listp dims))
             (equal (check-dim-list dims ienv)
                    (dims-ok (ispace-ctx-from-senv ienv) dims)))
    :use (dims-ok-of-ispace-ctx-from-senv-when-check-dim-list
          check-dim-list-when-dims-ok-of-ispace-ctx-from-senv))

  ;; shapes and ispaces:

  (defruled check-shape-of-ispace-senv-from-ctx-to-shape-ok
    (implies (and (ispace-var-setp ivars)
                  (shapep shape))
             (equal (check-shape shape (ispace-senv-from-ctx ivars))
                    (shape-ok ivars shape)))
    :use (shape-ok-when-check-shape-of-ispace-senv-from-ctx
          check-shape-of-ispace-senv-from-ctx-when-shape-ok))

  (defruled check-shape-list-of-ispace-senv-from-ctx-to-shapes-ok
    (implies (and (ispace-var-setp ivars)
                  (shape-listp shapes))
             (equal (check-shape-list shapes (ispace-senv-from-ctx ivars))
                    (shapes-ok ivars shapes)))
    :use (shapes-ok-when-check-shape-list-of-ispace-senv-from-ctx
          check-shape-list-of-ispace-senv-from-ctx-when-shapes-ok))

  (defruled check-ispace-of-ispace-senv-from-ctx-to-ispace-ok
    (implies (and (ispace-var-setp ivars)
                  (ispacep ispace))
             (equal (check-ispace ispace (ispace-senv-from-ctx ivars))
                    (ispace-ok ivars ispace)))
    :use (ispace-ok-when-check-ispace-of-ispace-senv-from-ctx
          check-ispace-of-ispace-senv-from-ctx-when-ispace-ok))

  (defruled check-ispace-list-of-ispace-senv-from-ctx-to-ispaces-ok
    (implies (and (ispace-var-setp ivars)
                  (ispace-listp ispaces))
             (equal (check-ispace-list ispaces (ispace-senv-from-ctx ivars))
                    (ispaces-ok ivars ispaces)))
    :use (ispaces-ok-when-check-ispace-list-of-ispace-senv-from-ctx
          check-ispace-list-of-ispace-senv-from-ctx-when-ispaces-ok))

  (defruled check-shape-to-shape-ok-of-ispace-ctx-from-senv
    (implies (and (ispace-senv-no-defs-p ienv)
                  (shapep shape))
             (equal (check-shape shape ienv)
                    (shape-ok (ispace-ctx-from-senv ienv) shape)))
    :use (shape-ok-of-ispace-ctx-from-senv-when-check-shape
          check-shape-when-shape-ok-of-ispace-ctx-from-senv))

  (defruled check-shape-list-to-shapes-ok-of-ispace-ctx-from-senv
    (implies (and (ispace-senv-no-defs-p ienv)
                  (shape-listp shapes))
             (equal (check-shape-list shapes ienv)
                    (shapes-ok (ispace-ctx-from-senv ienv) shapes)))
    :use (shapes-ok-of-ispace-ctx-from-senv-when-check-shape-list
          check-shape-list-when-shapes-ok-of-ispace-ctx-from-senv))

  (defruled check-ispace-to-ispace-ok-of-ispace-ctx-from-senv
    (implies (and (ispace-senv-no-defs-p ienv)
                  (ispacep ispace))
             (equal (check-ispace ispace ienv)
                    (ispace-ok (ispace-ctx-from-senv ienv) ispace)))
    :use (ispace-ok-of-ispace-ctx-from-senv-when-check-ispace
          check-ispace-when-ispace-ok-of-ispace-ctx-from-senv))

  (defruled check-ispace-list-to-ispaces-ok-of-ispace-ctx-from-senv
    (implies (and (ispace-senv-no-defs-p ienv)
                  (ispace-listp ispaces))
             (equal (check-ispace-list ispaces ienv)
                    (ispaces-ok (ispace-ctx-from-senv ienv) ispaces)))
    :use (ispaces-ok-of-ispace-ctx-from-senv-when-check-ispace-list
          check-ispace-list-when-ispaces-ok-of-ispace-ctx-from-senv)))
