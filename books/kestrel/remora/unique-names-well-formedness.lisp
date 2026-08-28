; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "unique-names")
(include-book "abstract-syntax-well-formedness")

(include-book "std/util/define-sk" :dir :system)

(include-book "portcullis")

(local (include-book "std/omaps/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unique-names-well-formedness
  :parents (unique-names)
  :short "Well-formedness of the uniquification of binder names."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we prove that @(tsee expr-uniquify-names) preserves @(tsee
     expr-wfp): the uniquification of a well-formed expression is well
     formed.  This is @(tsee expr-wfp-of-expr-uniquify-names).")
   (xdoc::p
    "Unlike the core-subset property of @(see unique-names-properties),
     well-formedness is not preserved for structural reasons.  @(tsee
     ast-wfp) constrains ASTs in two ways: certain lists must have one or
     two or more elements, and every identifier stored in a node must
     satisfy @(tsee valid-identifier-string-p).  The length constraints
     are structural --- uniquification maps the lists in question
     pointwise --- but the identifiers are not: uniquification
     @('invents') names.  A binder whose name has been seen already is
     renamed by @(tsee fresh-bind-name) to a fresh variant, and that
     variant is then substituted for the variable's occurrences
     throughout its scope.")
   (xdoc::p
    "So the property rests on a fact about name generation: that
     appending an index to a legal Remora identifier yields a legal
     Remora identifier.  That is @(tsee
     valid-identifier-string-p-of-expr-var-with-index), proved with
     @(see fresh-variable-operations), next to the function it is about;
     the first section below only lifts it to @(tsee fresh-bind-name),
     which lives in @(see unique-names).")
   (xdoc::p
    "The second section introduces @(tsee renaming-wfp), the invariant
     that a renaming map only ever maps names to valid identifiers, and
     shows that it holds of the maps the uniquification builds and that
     it is what makes the renaming operations preserve well-formedness.
     The third section is the induction over the uniquification itself,
     which threads that invariant, in the bundled form @(tsee
     var-renamings-wfp), through the traversal, and consumes the length
     facts wherever it builds a node whose well-formedness constrains the
     length of a list."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generated names are valid identifiers.
;
; The heart of this is VALID-IDENTIFIER-STRING-P-OF-EXPR-VAR-WITH-INDEX,
; proved with FRESH-VARIABLE-OPERATIONS next to the function it is about;
; FRESH-BIND-NAME, which lives in UNIQUE-NAMES, is lifted to it here.

(defrule valid-identifier-string-p-of-fresh-bind-name
  :short "A freshened binder name is a valid identifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "Either the name is kept, or it is a generated variant of it."))
  (implies (and (stringp name)
                (valid-identifier-string-p name))
           (valid-identifier-string-p (fresh-bind-name name used avoid)))
  :enable (fresh-bind-name fresh-expr-var))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The renaming-map invariant.
;
; A renaming operation substitutes the values of a renaming map for
; variable occurrences, so it preserves well-formedness exactly when
; those values are valid identifiers.  That is RENAMING-WFP.  It is
; stated as a quantified predicate rather than a recursion over the omap
; because every operation that the uniquification performs on these maps
; --- update, delete, and the bulk delete of the bound variables at a
; binder --- has a rule about ASSOC, which is what the quantifier
; instantiates.

(define-sk renaming-wfp ((renam acl2::string-string-mapp))
  :returns (yes/no booleanp)
  :short "Check that every name a renaming map may introduce
          is a valid Remora identifier."
  (forall (key)
          (b* ((renam (acl2::string-string-map-fix renam))
               (pair (omap::assoc key renam)))
            (implies pair
                     (valid-identifier-string-p (cdr pair))))))

(defrule valid-identifier-string-p-of-cdr-of-assoc-when-renaming-wfp
  :short "The name a renaming map maps a variable to is a valid identifier."
  (implies (and (renaming-wfp renam)
                (acl2::string-string-mapp renam)
                (omap::assoc key renam))
           (valid-identifier-string-p (cdr (omap::assoc key renam))))
  :use renaming-wfp-necc)

(defrule renaming-wfp-of-string-string-map-fix
  :short "@(tsee renaming-wfp) ignores the fixing of its argument."
  (equal (renaming-wfp (acl2::string-string-map-fix renam))
         (renaming-wfp renam))
  :expand ((renaming-wfp (acl2::string-string-map-fix renam))
           (renaming-wfp renam))
  :use ((:instance renaming-wfp-necc
                   (key (renaming-wfp-witness (acl2::string-string-map-fix renam))))
        (:instance renaming-wfp-necc
                   (renam (acl2::string-string-map-fix renam))
                   (key (renaming-wfp-witness renam)))))

(defrule valid-identifier-string-p-of-rename-var-string
  :short "Renaming a valid identifier under a well-formed renaming
          yields a valid identifier."
  (implies (and (renaming-wfp renam)
                (valid-identifier-string-p (str-fix name)))
           (valid-identifier-string-p (rename-var-string name renam)))
  :enable rename-var-string
  :use ((:instance renaming-wfp-necc (key (str-fix name)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The invariant is preserved by every way the uniquification builds a
; renaming map: recording a binder's new name (which either adds an entry
; or clears a stale one), and reducing a map by the variables bound at a
; binder.

(defrule renaming-wfp-of-delete
  :short "Deleting an entry preserves @(tsee renaming-wfp)."
  (implies (renaming-wfp renam)
           (renaming-wfp (omap::delete key (acl2::string-string-map-fix renam))))
  :expand ((renaming-wfp (omap::delete key (acl2::string-string-map-fix renam))))
  :use ((:instance renaming-wfp-necc
                   (key (renaming-wfp-witness
                         (omap::delete key (acl2::string-string-map-fix renam)))))))

(defrule renaming-wfp-of-update
  :short "Adding an entry with a valid name preserves @(tsee renaming-wfp)."
  (implies (and (renaming-wfp renam)
                (stringp key)
                (stringp val)
                (valid-identifier-string-p val))
           (renaming-wfp (omap::update key val (acl2::string-string-map-fix renam))))
  :expand ((renaming-wfp (omap::update key val (acl2::string-string-map-fix renam))))
  :use ((:instance renaming-wfp-necc
                   (key (renaming-wfp-witness
                         (omap::update key val (acl2::string-string-map-fix renam)))))))

(defrule renaming-wfp-of-extend-renaming
  :short "Recording a binder's new name preserves @(tsee renaming-wfp)."
  (implies (and (renaming-wfp renam)
                (valid-identifier-string-p (str-fix new-name)))
           (renaming-wfp (extend-renaming name new-name renam)))
  :enable extend-renaming)

(defrule renaming-wfp-of-delete*
  :short "Deleting a set of entries preserves @(tsee renaming-wfp)."
  (implies (renaming-wfp renam)
           (renaming-wfp (omap::delete* keys (acl2::string-string-map-fix renam))))
  :expand ((renaming-wfp (omap::delete* keys (acl2::string-string-map-fix renam))))
  :use ((:instance renaming-wfp-necc
                   (key (renaming-wfp-witness
                         (omap::delete* keys (acl2::string-string-map-fix renam)))))))

(defrule renaming-wfp-of-dim/shape-rename-remove-bound
  :short "Reducing the ispace renamings at a binder preserves
          @(tsee renaming-wfp)."
  (implies (and (renaming-wfp dim-renam)
                (renaming-wfp shape-renam))
           (b* (((mv & & new-dim new-shape)
                 (dim/shape-rename-remove-bound vars dim-renam shape-renam)))
             (and (renaming-wfp new-dim)
                  (renaming-wfp new-shape))))
  :enable dim/shape-rename-remove-bound)

(defrule renaming-wfp-of-atom/array-rename-remove-bound
  :short "Reducing the type renamings at a binder preserves
          @(tsee renaming-wfp)."
  (implies (and (renaming-wfp atom-renam)
                (renaming-wfp array-renam))
           (b* (((mv & & new-atom new-array)
                 (atom/array-rename-remove-bound vars atom-renam array-renam)))
             (and (renaming-wfp new-atom)
                  (renaming-wfp new-array))))
  :enable atom/array-rename-remove-bound)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The renaming operations preserve well-formedness under the invariant.
; Dimensions first: they are the only ASTs that a renaming reaches
; through a map of their own.

(defret-mutual dim-wfp-of-dim-rename-dim-vars
  (defret dim-wfp-of-dim-rename-dim-vars
    (implies (and (dim-wfp dim) (renaming-wfp renam))
             (dim-wfp result))
    :fn dim-rename-dim-vars)
  (defret dim-list-wfp-of-dim-list-rename-dim-vars
    (implies (and (dim-list-wfp dim-list) (renaming-wfp renam))
             (dim-list-wfp result))
    :fn dim-list-rename-dim-vars)
  :mutual-recursion dims-rename-dim-vars
  :hints (("Goal" :in-theory (enable dim-rename-dim-vars
                                     dim-list-rename-dim-vars
                                     dim-wfp
                                     dim-list-wfp))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The remaining renaming cliques, and the option, parameter, and bundled
; forms built on them.  Every case rebuilds its node with the same
; constructor, so nothing here needs the length facts: those are needed
; only where the uniquification itself builds an n-ary node, below.

(defret-mutual ispace-wfp-of-ispace-rename-ispace-vars
  (defret shape-wfp-of-shape-rename-ispace-vars
    (implies (and (shape-wfp shape)
                  (renaming-wfp dim-renam) (renaming-wfp shape-renam))
             (shape-wfp result))
    :fn shape-rename-ispace-vars)
  (defret shape-list-wfp-of-shape-list-rename-ispace-vars
    (implies (and (shape-list-wfp shape-list)
                  (renaming-wfp dim-renam) (renaming-wfp shape-renam))
             (shape-list-wfp result))
    :fn shape-list-rename-ispace-vars)
  (defret ispace-wfp-of-ispace-rename-ispace-vars
    (implies (and (ispace-wfp ispace)
                  (renaming-wfp dim-renam) (renaming-wfp shape-renam))
             (ispace-wfp result))
    :fn ispace-rename-ispace-vars)
  (defret ispace-list-wfp-of-ispace-list-rename-ispace-vars
    (implies (and (ispace-list-wfp ispace-list)
                  (renaming-wfp dim-renam) (renaming-wfp shape-renam))
             (ispace-list-wfp result))
    :fn ispace-list-rename-ispace-vars)
  :mutual-recursion shapes/ispaces-rename-ispace-vars
  :hints (("Goal" :in-theory (enable shape-rename-ispace-vars
                                     shape-list-rename-ispace-vars
                                     ispace-rename-ispace-vars
                                     ispace-list-rename-ispace-vars
                                     shape-wfp shape-list-wfp
                                     ispace-wfp ispace-list-wfp))))

(defret-mutual type-wfp-of-type-rename-ispace-vars
  (defret type-wfp-of-type-rename-ispace-vars
    (implies (and (type-wfp type)
                  (renaming-wfp dim-renam) (renaming-wfp shape-renam))
             (type-wfp result))
    :fn type-rename-ispace-vars)
  (defret type-list-wfp-of-type-list-rename-ispace-vars
    (implies (and (type-list-wfp type-list)
                  (renaming-wfp dim-renam) (renaming-wfp shape-renam))
             (type-list-wfp result))
    :fn type-list-rename-ispace-vars)
  :mutual-recursion types-rename-ispace-vars
  :hints (("Goal" :in-theory (enable type-rename-ispace-vars
                                     type-list-rename-ispace-vars
                                     type-wfp type-list-wfp))))

(defret-mutual type-wfp-of-type-rename-type-vars
  (defret type-wfp-of-type-rename-type-vars
    (implies (and (type-wfp type)
                  (renaming-wfp atom-renam) (renaming-wfp array-renam))
             (type-wfp result))
    :fn type-rename-type-vars)
  (defret type-list-wfp-of-type-list-rename-type-vars
    (implies (and (type-list-wfp type-list)
                  (renaming-wfp atom-renam) (renaming-wfp array-renam))
             (type-list-wfp result))
    :fn type-list-rename-type-vars)
  :mutual-recursion types-rename-type-vars
  :hints (("Goal" :in-theory (enable type-rename-type-vars
                                     type-list-rename-type-vars
                                     type-wfp type-list-wfp
                                     type-var-wfp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule type-option-wfp-of-type-option-rename-ispace-vars
  (implies (and (type-option-wfp ty?) (renaming-wfp dim-renam) (renaming-wfp shape-renam))
           (type-option-wfp (type-option-rename-ispace-vars ty? dim-renam shape-renam)))
  :enable (type-option-rename-ispace-vars type-option-wfp))

(defrule type-option-wfp-of-type-option-rename-type-vars
  (implies (and (type-option-wfp ty?) (renaming-wfp atom-renam) (renaming-wfp array-renam))
           (type-option-wfp (type-option-rename-type-vars ty? atom-renam array-renam)))
  :enable (type-option-rename-type-vars type-option-wfp))

(defrule type-list-option-wfp-of-type-list-option-rename-ispace-vars
  (implies (and (type-list-option-wfp tys?) (renaming-wfp dim-renam) (renaming-wfp shape-renam))
           (type-list-option-wfp (type-list-option-rename-ispace-vars tys? dim-renam shape-renam)))
  :enable (type-list-option-rename-ispace-vars type-list-option-wfp))

(defrule type-list-option-wfp-of-type-list-option-rename-type-vars
  (implies (and (type-list-option-wfp tys?) (renaming-wfp atom-renam) (renaming-wfp array-renam))
           (type-list-option-wfp (type-list-option-rename-type-vars tys? atom-renam array-renam)))
  :enable (type-list-option-rename-type-vars type-list-option-wfp))

(defrule ispace-list-option-wfp-of-ispace-list-option-rename-ispace-vars
  (implies (and (ispace-list-option-wfp isps?) (renaming-wfp dim-renam) (renaming-wfp shape-renam))
           (ispace-list-option-wfp
            (ispace-list-option-rename-ispace-vars isps? dim-renam shape-renam)))
  :enable (ispace-list-option-rename-ispace-vars ispace-list-option-wfp))

(defrule var+type?-wfp-of-var+type?-rename-ispace-vars
  (implies (and (var+type?-wfp p) (renaming-wfp dim-renam) (renaming-wfp shape-renam))
           (var+type?-wfp (var+type?-rename-ispace-vars p dim-renam shape-renam)))
  :enable (var+type?-rename-ispace-vars var+type?-wfp))

(defrule var+type?-wfp-of-var+type?-rename-type-vars
  (implies (and (var+type?-wfp p) (renaming-wfp atom-renam) (renaming-wfp array-renam))
           (var+type?-wfp (var+type?-rename-type-vars p atom-renam array-renam)))
  :enable (var+type?-rename-type-vars var+type?-wfp))

(defrule var+type?-list-wfp-of-var+type?-list-rename-ispace-vars
  (implies (and (var+type?-list-wfp ps) (renaming-wfp dim-renam) (renaming-wfp shape-renam))
           (var+type?-list-wfp (var+type?-list-rename-ispace-vars ps dim-renam shape-renam)))
  :induct (len ps)
  :enable (var+type?-list-rename-ispace-vars var+type?-list-wfp))

(defrule var+type?-list-wfp-of-var+type?-list-rename-type-vars
  (implies (and (var+type?-list-wfp ps) (renaming-wfp atom-renam) (renaming-wfp array-renam))
           (var+type?-list-wfp (var+type?-list-rename-type-vars ps atom-renam array-renam)))
  :induct (len ps)
  :enable (var+type?-list-rename-type-vars var+type?-list-wfp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The bundle of five renamings that the uniquification threads, and the
; operations that apply all of them at once.

(define var-renamings-wfp ((r var-renamings-p))
  :returns (yes/no booleanp)
  :short "Check that all five renaming maps of a bundle are well formed."
  (b* (((var-renamings r) r))
    (and (renaming-wfp r.dim)
         (renaming-wfp r.shape)
         (renaming-wfp r.atom)
         (renaming-wfp r.array)
         (renaming-wfp r.expr))))

(defrule type-wfp-of-type-rename-all-vars
  (implies (and (type-wfp ty) (var-renamings-wfp r))
           (type-wfp (type-rename-all-vars ty r)))
  :enable (type-rename-all-vars var-renamings-wfp))

(defrule type-option-wfp-of-type-option-rename-all-vars
  (implies (and (type-option-wfp ty?) (var-renamings-wfp r))
           (type-option-wfp (type-option-rename-all-vars ty? r)))
  :enable (type-option-rename-all-vars var-renamings-wfp))

(defrule type-list-wfp-of-type-list-rename-all-vars
  (implies (and (type-list-wfp tys) (var-renamings-wfp r))
           (type-list-wfp (type-list-rename-all-vars tys r)))
  :enable (type-list-rename-all-vars var-renamings-wfp))

(defrule type-list-option-wfp-of-type-list-option-rename-all-vars
  (implies (and (type-list-option-wfp tys?) (var-renamings-wfp r))
           (type-list-option-wfp (type-list-option-rename-all-vars tys? r)))
  :enable (type-list-option-rename-all-vars var-renamings-wfp))

(defrule var+type?-list-wfp-of-var+type?-list-rename-all-vars
  (implies (and (var+type?-list-wfp ps) (var-renamings-wfp r))
           (var+type?-list-wfp (var+type?-list-rename-all-vars ps r)))
  :enable (var+type?-list-rename-all-vars var-renamings-wfp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The uniquification itself.
;
; Two things are needed at each binder beyond the induction hypotheses:
; the freshened names are valid identifiers and the extended renamings
; stay well formed (the parameter helpers below), and the lists that
; AST-WFP constrains the length of keep their length (the LEN facts).

(defrule len-of-uniq-name-list-new-names
  :short "Freshening a list of names preserves its length."
  (equal (len (mv-nth 1 (uniq-name-list names used avoid)))
         (len names))
  :induct (uniq-name-list names used avoid)
  :enable (uniq-name-list len))

; LEN-OF-UNIQ-EXPR-PARAMS, LEN-OF-UNIQ-TYPE-VAR-PARAMS,
; LEN-OF-VAR+TYPE?-LIST-RENAME-ALL-VARS, and LEN-OF-TYPE-LIST-RENAME-ALL-VARS
; are now proved in UNIQUE-NAMES (in the respective functions' ///), since
; the :LAMBDAN, :TLAMBDAN, and :TAPPN guards there need them.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule uniq-expr-params-wfp
  :short "Freshening expression parameters preserves well-formedness."
  (implies (and (var+type?-list-wfp params)
                (renaming-wfp renam))
           (b* (((mv & new-params new-renam)
                 (uniq-expr-params params used avoid renam)))
             (and (var+type?-list-wfp new-params)
                  (renaming-wfp new-renam))))
  :induct (uniq-expr-params params used avoid renam)
  :enable (uniq-expr-params var+type?-list-wfp var+type?-wfp))

(defrule uniq-type-var-params-wfp
  :short "Freshening type parameters preserves well-formedness."
  (implies (and (type-var-list-wfp params)
                (renaming-wfp atom-renam)
                (renaming-wfp array-renam))
           (b* (((mv & new-params new-atom new-array)
                 (uniq-type-var-params params used avoid atom-renam array-renam)))
             (and (type-var-list-wfp new-params)
                  (renaming-wfp new-atom)
                  (renaming-wfp new-array))))
  :induct (uniq-type-var-params params used avoid atom-renam array-renam)
  :enable (uniq-type-var-params type-var-list-wfp type-var-wfp type-var->name))

(defrule uniq-ispace-var-params-wfp
  :short "Freshening ispace parameters preserves well-formedness."
  (implies (and (ispace-var-list-wfp params)
                (renaming-wfp dim-renam)
                (renaming-wfp shape-renam))
           (b* (((mv & new-params new-dim new-shape)
                 (uniq-ispace-var-params params used avoid dim-renam shape-renam)))
             (and (ispace-var-list-wfp new-params)
                  (renaming-wfp new-dim)
                  (renaming-wfp new-shape))))
  :induct (uniq-ispace-var-params params used avoid dim-renam shape-renam)
  :enable (uniq-ispace-var-params ispace-var-list-wfp ispace-var-wfp ispace-var->name))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Bridges for the two binders that the traversal handles specially: the
; :UNBOX, which runs the list-based ispace helper on a singleton, and the
; unary :TLAMBDA and :ILAMBDA, which build a variable directly.

(defrule ispace-var-list-wfp-of-singleton
  (equal (ispace-var-list-wfp (list v))
         (ispace-var-wfp v))
  :enable ispace-var-list-wfp)

(defrule consp-of-uniq-ispace-var-params-new-params
  (equal (consp (mv-nth 1 (uniq-ispace-var-params params used avoid dim-renam shape-renam)))
         (consp params))
  :enable uniq-ispace-var-params)

(defrule valid-identifier-string-p-of-fresh-bind-name-of-type-var->name
  (implies (type-var-wfp v)
           (valid-identifier-string-p
            (fresh-bind-name (type-var->name v) used avoid)))
  :enable (type-var-wfp type-var->name))

(defrule valid-identifier-string-p-of-fresh-bind-name-of-ispace-var->name
  (implies (ispace-var-wfp v)
           (valid-identifier-string-p
            (fresh-bind-name (ispace-var->name v) used avoid)))
  :enable (ispace-var-wfp ispace-var->name))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defret-mutual len-of-uniquify-names-impl
  (defret len-of-uniq-expr-list
    (equal (len new-x) (len x))
    :fn uniq-expr-list)
  (defret len-of-uniq-atom-list
    (equal (len new-x) (len x))
    :fn uniq-atom-list)
  (defret len-of-uniq-bind-list
    (equal (len new-x) (len x))
    :fn uniq-bind-list)
  :mutual-recursion uniquify-names-impl
  :skip-others t
  :hints (("Goal" :in-theory (enable uniq-expr-list uniq-atom-list uniq-bind-list len))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The main induction.  The :EXPAND hints are for the nodes whose
; well-formedness constrains the length of a list argument: ACL2 declines
; to open AST-WFP on those constructors, since the list component of the
; result is a fixed copy of the argument rather than a subterm of it.

(defret-mutual uniquify-names-impl-wfp
  (defret expr-wfp-of-uniq-expr
    (implies (and (expr-wfp x) (var-renamings-wfp r))
             (expr-wfp new-x))
    :fn uniq-expr)
  (defret expr-list-wfp-of-uniq-expr-list
    (implies (and (expr-list-wfp x) (var-renamings-wfp r))
             (expr-list-wfp new-x))
    :fn uniq-expr-list)
  (defret atom-wfp-of-uniq-atom
    (implies (and (atom-wfp x) (var-renamings-wfp r))
             (atom-wfp new-x))
    :fn uniq-atom)
  (defret atom-list-wfp-of-uniq-atom-list
    (implies (and (atom-list-wfp x) (var-renamings-wfp r))
             (atom-list-wfp new-x))
    :fn uniq-atom-list)
  (defret bind-wfp-of-uniq-bind
    (implies (and (bind-wfp x) (var-renamings-wfp r))
             (and (bind-wfp new-x) (var-renamings-wfp new-r)))
    :fn uniq-bind)
  (defret bind-list-wfp-of-uniq-bind-list
    (implies (and (bind-list-wfp x) (var-renamings-wfp r))
             (and (bind-list-wfp new-x) (var-renamings-wfp new-r)))
    :fn uniq-bind-list)
  :mutual-recursion uniquify-names-impl
  :hints (("Goal" :in-theory (enable uniq-expr uniq-expr-list
                                     uniq-atom uniq-atom-list
                                     uniq-bind uniq-bind-list
                                     expr-wfp expr-list-wfp
                                     atom-wfp atom-list-wfp
                                     bind-wfp bind-list-wfp
                                     var+type?-wfp
                                     var-renamings-wfp
                                     type-var-list-option-wfp
                                     ispace-var-list-option-wfp
                                     type-option-wfp
                                     type-list-option-wfp
                                     ispace-list-option-wfp
                                     len-of-var+type?-list-rename-ispace-vars
                                     len-of-var+type?-list-rename-type-vars
                                     ispace-var-wfp-of-car-when-ispace-var-list-wfp
                                     len-of-ispace-list-rename-ispace-vars
                                     len-of-type-list-rename-ispace-vars
                                     len-of-type-list-rename-type-vars)
           :expand ((:free (es) (expr-wfp (expr-bracket es)))
                    (:free (ds as) (expr-wfp (expr-array ds as)))
                    (:free (ds es) (expr-wfp (expr-frame ds es)))
                    (:free (f as) (expr-wfp (expr-appn f as)))
                    (:free (bs b) (expr-wfp (expr-let bs b)))
                    (:free (n) (type-var-wfp (type-var-atom n)))
                    (:free (n) (type-var-wfp (type-var-array n)))
                    (:free (n) (ispace-var-wfp (ispace-var-dim n)))
                    (:free (n) (ispace-var-wfp (ispace-var-shape n)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule renaming-wfp-of-nil
  :short "The empty renaming is well formed."
  (renaming-wfp nil)
  :expand ((renaming-wfp nil)))

(defrule expr-wfp-of-expr-uniquify-names
  :short "Uniquifying the binder names of a well-formed expression
          yields a well-formed expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the promised property.  @(tsee expr-uniquify-names) starts
     from the bundle whose five renaming maps are all empty, which
     satisfies the invariant vacuously."))
  (implies (expr-wfp expr)
           (expr-wfp (expr-uniquify-names expr)))
  :enable (expr-uniquify-names var-renamings-wfp))
