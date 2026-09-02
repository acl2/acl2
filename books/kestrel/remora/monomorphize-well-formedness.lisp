; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "monomorphize")
(include-book "unique-names-well-formedness")
(include-book "well-formedness-support")
(include-book "abstract-syntax-well-formedness")

(include-book "std/util/deflist" :dir :system)

(include-book "portcullis")

(local (include-book "std/omaps/top" :dir :system))

; Disable the tau system, which costs more on this book's proofs than it saves.
; (The sibling books go further and call (acl2::controlled-configuration), which
; also disables the built-in defuns and implicit induction; that does not pay
; off here --- the main induction below needs substantial extra hints under it.)
(local (in-theory (disable (:e tau-system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The rules that DEFFOLD-REDUCE and DEFFOLD-MAP generate for the constructors
; and accessors of each node, which is how the goals about a rebuilt node's
; well-formedness are decomposed.  (Same idiom as in the sibling book
; WELL-FORMEDNESS-UNDER-DESUGARING.)

(local (in-theory (enable* ast-wfp-rules ast-partial-eval-dims-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ monomorphize-well-formedness
  :parents (monomorphize)
  :short "Well-formedness of monomorphization."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we prove that monomorphization preserves @(tsee expr-wfp): the
     monomorphization of a well-formed expression is well formed.  This is
     @(tsee expr-wfp-of-monomorphize-top-expr), and the corresponding
     property of the traversal itself is @(tsee expr-wfp-of-mono-expr).")
   (xdoc::p
    (xdoc::b "What has to be shown."))
   (xdoc::p
    "@(tsee ast-wfp) constrains ASTs in two ways: certain lists must have
     one or two or more elements, and every identifier stored in a node
     must satisfy @(tsee valid-identifier-string-p).  Most cases of @(tsee
     mono-expr) and its companions rebuild their node with the same
     constructor, mapping any list component pointwise, so for them both
     kinds of constraint are immediate from the induction hypotheses and
     the length theorems of the first section below.")
   (xdoc::p
    "The interesting cases are the ones that instantiate a polymorphic
     definition.  A @(':capp') or @(':iapp')/@(':iappn') of a known
     definition becomes a call of a generated instance name, so that name
     must be a legal identifier: that is @(tsee
     valid-identifier-string-p-of-cfun-inst-name), proved with @(see
     monomorphize) next to the function it is about, whose condition on
     the type names is discharged here once and for all --- @(tsee
     short-name-for-type) returns one of @('\"b\"'), @('\"i\"'),
     @('\"f\"'), @('\"unbound\"'), @('\"nyi\"'), all of which are made of
     ASCII identifier characters.  (The arity constraint on @(':appn') is
     met by the @(':capp') case itself, which emits an @(':app') for one
     argument and the instance name alone for none.)")
   (xdoc::p
    "The instance is then created from the definition's own body, which
     is first run through @(tsee expr-partial-eval-dims) and @(tsee
     expr-subst-type-vars).  Those two operations therefore need
     well-formedness preservation of their own.  Dimension partial
     evaluation needs no invariant --- the values in the environment are
     naturals, so it only ever replaces a @(':var') dim by a @(':const')
     one, and a @(':var') shape by a @(':dims') shape over @(':const')
     dims --- and is the second section below.  Type
     substitution does need one: it replaces a type variable by whatever
     the substitution maps it to, so it preserves well-formedness exactly
     when the types in that map are well formed.  That is @(tsee
     type-map-wfp), the analogue of @(tsee renaming-wfp) in @(see
     unique-names-well-formedness); since it mentions nothing of
     monomorphization, it and its preservation lemmas are in @(see
     well-formedness-support), and only @(tsee
     type-map-wfp-of-extend-type-var-map), about the one map operation
     that monomorphization itself performs, is here.")
   (xdoc::p
    "The last invariant is on the registration map that the traversal
     threads: an instance is created from a request recorded earlier, so
     the recorded instance names must be legal identifiers and the
     recorded type arguments well formed.  That is @(tsee
     fn-info-map-wfp), which the main induction establishes of the map it
     returns as well as assuming of the map it is given.")
   (xdoc::p
    "No invariant is needed on @('defs'): the traversal only tests
     membership in it, and the definition an instance is created from is
     the one bound by the @(':let') being exited, which is well formed by
     the hypothesis on that @(':let').  None is needed on @('denv')
     either, since it maps ispace variables to naturals and lists of
     naturals.")
   (xdoc::p
    "The @(':let') normalizations that @(tsee monomorphize-top-expr)
     applies around the traversal, @(tsee expr-singletonize-let) and
     @(tsee expr-flatten-let), are also independent of monomorphization,
     so they too are covered in @(see well-formedness-support); together
     with @(tsee expr-wfp-of-expr-uniquify-names) (see @(see
     unique-names-well-formedness)) they compose with the main induction
     into the top-level property."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generated instance names are valid identifiers, and lengths are preserved.

(defrule ascii-id-continue-string-p-of-short-name-for-type
  :short "A short type name is made of ASCII identifier characters."
  (ascii-id-continue-string-p (short-name-for-type ty type-map))
  :induct t
  :enable short-name-for-type)

(defrule ascii-id-continue-string-list-p-of-name-for-type-list
  :short "Short type names are made of ASCII identifier characters."
  (ascii-id-continue-string-list-p (name-for-type-list tys type-map))
  :induct t
  :enable (name-for-type-list ascii-id-continue-string-list-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; AST-WFP constrains the length of the list component of several nodes;
; the monomorphization of a list maps it pointwise.  The CONSP forms are
; the ones the goals arise in, at the nodes whose constraint is on a
; length that the traversal does not have in hand as a LEN.  CONSP of the
; list itself is proved with the functions, in MONOMORPHIZE; only CONSP of
; its CDR, which the two-or-more-element nodes need, is left to prove here.

(defret-mutual len-of-monomorphize-impl
  (defret len-of-mono-expr-list
    (equal (len new-exprs) (len x))
    :fn mono-expr-list)
  (defret len-of-mono-atom-list
    (equal (len new-atoms) (len x))
    :fn mono-atom-list)
  :skip-others t
  :mutual-recursion monomorphize-impl
  :hints (("Goal" :in-theory (enable mono-expr-list mono-atom-list len))))

(defret-mutual consp-of-cdr-of-monomorphize-impl
  (defret consp-of-cdr-of-mono-expr-list
    (equal (consp (cdr new-exprs)) (consp (cdr x)))
    :fn mono-expr-list)
  (defret consp-of-cdr-of-mono-atom-list
    (equal (consp (cdr new-atoms)) (consp (cdr x)))
    :fn mono-atom-list)
  :skip-others t
  :mutual-recursion monomorphize-impl
  :hints (("Goal" :in-theory (enable mono-expr-list mono-atom-list))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The type-substitution invariant, at the one operation on these maps that
; monomorphization itself performs.  The invariant and its preservation by
; the generic map operations are in WELL-FORMEDNESS-SUPPORT.

(defrule type-map-wfp-of-extend-type-var-map
  :short "Binding the type parameters of an instantiated definition
          preserves the invariant."
  (implies (and (type-list-wfp tys)
                (type-map-wfp type-map))
           (type-map-wfp (extend-type-var-map tvars tys type-map)))
  :induct t
  :enable (extend-type-var-map type-list-wfp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Dimension partial evaluation preserves well-formedness.  No invariant on
; the environment is needed: its values are naturals, so a dim :VAR is
; either kept, with its name, or replaced by a :CONST, and a shape :VAR is
; either kept or replaced by a :DIMS over :CONSTs; AST-WFP constrains
; neither.

(defsection wfp-of-partial-eval-dims
  :short "Partially evaluating dimensions preserves well-formedness."

  (defrule dim-list-wfp-of-nats-to-dims
    :short "The dims a substituted shape is built from are well formed."
    (dim-list-wfp (nats-to-dims nats))
    :induct (nats-to-dims nats)
    :enable (nats-to-dims dim-wfp dim-list-wfp))

  (defret-mutual dims-wfp-of-dims-partial-eval-dims
    (defret dim-wfp-of-dim-partial-eval-dims
      (implies (dim-wfp dim) (dim-wfp result))
      :fn dim-partial-eval-dims)
    (defret dim-list-wfp-of-dim-list-partial-eval-dims
      (implies (dim-list-wfp dim-list) (dim-list-wfp result))
      :fn dim-list-partial-eval-dims)
    :mutual-recursion dims-partial-eval-dims
    :hints (("Goal" :in-theory (enable dim-partial-eval-dims
                                       dim-list-partial-eval-dims
                                       dim-wfp dim-list-wfp))))

  (defret-mutual shapes/ispaces-wfp-of-shapes/ispaces-partial-eval-dims
    (defret shape-wfp-of-shape-partial-eval-dims
      (implies (shape-wfp shape) (shape-wfp result))
      :fn shape-partial-eval-dims)
    (defret shape-list-wfp-of-shape-list-partial-eval-dims
      (implies (shape-list-wfp shape-list) (shape-list-wfp result))
      :fn shape-list-partial-eval-dims)
    (defret ispace-wfp-of-ispace-partial-eval-dims
      (implies (ispace-wfp ispace) (ispace-wfp result))
      :fn ispace-partial-eval-dims)
    (defret ispace-list-wfp-of-ispace-list-partial-eval-dims
      (implies (ispace-list-wfp ispace-list) (ispace-list-wfp result))
      :fn ispace-list-partial-eval-dims)
    :mutual-recursion shapes/ispaces-partial-eval-dims
    :hints (("Goal" :in-theory (enable shape-partial-eval-dims
                                       shape-list-partial-eval-dims
                                       ispace-partial-eval-dims
                                       ispace-list-partial-eval-dims
                                       shape-wfp shape-list-wfp
                                       ispace-wfp ispace-list-wfp))))

  (defrule ispace-list-option-wfp-of-ispace-list-option-partial-eval-dims
    (implies (ispace-list-option-wfp isps?)
             (ispace-list-option-wfp
              (ispace-list-option-partial-eval-dims isps? denv)))
    :enable ispace-list-option-partial-eval-dims)

  (defret-mutual types-wfp-of-types-partial-eval-dims
    (defret type-wfp-of-type-partial-eval-dims
      (implies (type-wfp type) (type-wfp result))
      :fn type-partial-eval-dims)
    (defret type-list-wfp-of-type-list-partial-eval-dims
      (implies (type-list-wfp type-list) (type-list-wfp result))
      :fn type-list-partial-eval-dims)
    :mutual-recursion types-partial-eval-dims
    :hints (("Goal" :in-theory (enable type-partial-eval-dims
                                       type-list-partial-eval-dims
                                       type-wfp type-list-wfp
                                       len-of-type-list-partial-eval-dims))))

  (defrule type-option-wfp-of-type-option-partial-eval-dims
    (implies (type-option-wfp ty?)
             (type-option-wfp (type-option-partial-eval-dims ty? denv)))
    :enable type-option-partial-eval-dims)

  (defrule type-list-option-wfp-of-type-list-option-partial-eval-dims
    (implies (type-list-option-wfp tys?)
             (type-list-option-wfp
              (type-list-option-partial-eval-dims tys? denv)))
    :enable type-list-option-partial-eval-dims)

  (defrule var+type?-wfp-of-var+type?-partial-eval-dims
    (implies (var+type?-wfp vt)
             (var+type?-wfp (var+type?-partial-eval-dims vt denv)))
    :enable (var+type?-partial-eval-dims var+type?-wfp))

  (defrule var+type?-list-wfp-of-var+type?-list-partial-eval-dims
    (implies (var+type?-list-wfp vts)
             (var+type?-list-wfp (var+type?-list-partial-eval-dims vts denv)))
    :induct t
    :enable (var+type?-list-partial-eval-dims var+type?-list-wfp))

  (defret-mutual exprs/atoms/binds-wfp-of-exprs/atoms/binds-partial-eval-dims
    (defret expr-wfp-of-expr-partial-eval-dims
      (implies (expr-wfp expr) (expr-wfp result))
      :fn expr-partial-eval-dims)
    (defret expr-list-wfp-of-expr-list-partial-eval-dims
      (implies (expr-list-wfp expr-list) (expr-list-wfp result))
      :fn expr-list-partial-eval-dims)
    (defret atom-wfp-of-atom-partial-eval-dims
      (implies (atom-wfp atom) (atom-wfp result))
      :fn atom-partial-eval-dims)
    (defret atom-list-wfp-of-atom-list-partial-eval-dims
      (implies (atom-list-wfp atom-list) (atom-list-wfp result))
      :fn atom-list-partial-eval-dims)
    (defret bind-wfp-of-bind-partial-eval-dims
      (implies (bind-wfp bind) (bind-wfp result))
      :fn bind-partial-eval-dims)
    (defret bind-list-wfp-of-bind-list-partial-eval-dims
      (implies (bind-list-wfp bind-list) (bind-list-wfp result))
      :fn bind-list-partial-eval-dims)
    :mutual-recursion exprs/atoms/binds-partial-eval-dims
    :hints (("Goal" :in-theory (enable expr-partial-eval-dims
                                       expr-list-partial-eval-dims
                                       atom-partial-eval-dims
                                       atom-list-partial-eval-dims
                                       bind-partial-eval-dims
                                       bind-list-partial-eval-dims
                                       expr-wfp expr-list-wfp
                                       atom-wfp atom-list-wfp
                                       bind-wfp bind-list-wfp
                                       var+type?-wfp
                                       len-of-expr-list-partial-eval-dims
                                       len-of-atom-list-partial-eval-dims
                                       len-of-bind-list-partial-eval-dims
                                       len-of-type-list-partial-eval-dims
                                       len-of-ispace-list-partial-eval-dims
                                       len-of-var+type?-list-partial-eval-dims)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The registration-map invariant.
;
; An instance is created from a request recorded at a call site, and the
; request supplies the instance's name and its type arguments; both must
; be well formed for the generated bind to be.  Unlike the type
; substitutions, this map is an alist, so the invariant is a recursion.

(define inst-request-wfp ((req inst-requestp))
  :returns (yes/no booleanp)
  :short "Check that a recorded instantiation request is well formed:
          its instance name is a valid identifier and its type arguments
          are well-formed types."
  (b* (((inst-request req) req))
    (and (valid-identifier-string-p req.inst-name)
         (type-list-wfp req.targ-tys))))

(std::deflist inst-request-list-wfp (x)
  :short "Check that every recorded request in a list is well formed."
  (inst-request-wfp x)
  :guard (inst-request-listp x))

(in-theory (disable inst-request-list-wfp))

(define fn-info-map-wfp ((fn-info-map fn-info-mapp))
  :returns (yes/no booleanp)
  :short "Check that every request recorded in a registration map
          is well formed."
  (or (endp fn-info-map)
      (and (consp (car fn-info-map))
           (inst-request-list-wfp (cdar fn-info-map))
           (fn-info-map-wfp (cdr fn-info-map)))))

(defsection fn-info-map-wfp-lemmas
  :short "The registration-map invariant is preserved by the operations
          on these maps."

  (defrule inst-request-wfp-of-inst-request-fix
    (equal (inst-request-wfp (inst-request-fix req))
           (inst-request-wfp req))
    :enable inst-request-wfp)

  (defrule inst-request-list-wfp-of-cdr-of-assoc-when-fn-info-map-wfp
    :short "The requests recorded for a definition are well formed."
    (implies (fn-info-map-wfp fn-info-map)
             (inst-request-list-wfp (cdr (assoc-equal name fn-info-map))))
    :induct t
    :enable (fn-info-map-wfp inst-request-list-wfp))

  (defrule fn-info-map-wfp-of-remove1-assoc-equal
    :short "Dropping a registration preserves the invariant."
    (implies (fn-info-map-wfp fn-info-map)
             (fn-info-map-wfp (remove1-assoc-equal name fn-info-map)))
    :induct t
    :enable fn-info-map-wfp)

  (defrule fn-info-map-wfp-of-cons-of-cons-nil
    :short "Registering a definition, with no requests yet,
            preserves the invariant."
    (implies (fn-info-map-wfp fn-info-map)
             (fn-info-map-wfp (cons (cons name nil) fn-info-map)))
    :enable (fn-info-map-wfp inst-request-list-wfp))

  (defrule fn-info-map-wfp-of-put-assoc-equal
    (implies (and (fn-info-map-wfp fn-info-map)
                  (inst-request-list-wfp requests))
             (fn-info-map-wfp (put-assoc-equal name requests fn-info-map)))
    :induct t
    :enable fn-info-map-wfp)

  (defrule fn-info-map-wfp-of-fn-info-map-add-request
    :short "Recording a well-formed request preserves the invariant."
    (implies (and (fn-info-map-wfp fn-info-map)
                  (inst-request-wfp request))
             (fn-info-map-wfp
              (fn-info-map-add-request fn-info-map fun-name request)))
    :enable (fn-info-map-add-request inst-request-list-wfp)
    :disable put-assoc-equal)

  (defrule fn-info-map-wfp-of-nil
    :short "The empty registration map satisfies the invariant."
    (fn-info-map-wfp nil)
    :enable fn-info-map-wfp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The monomorphization traversal itself.
;
; One small bridge is needed beyond the layers above: reading the name of
; a :VAR node off its well-formedness (the traversal tests the kind of the
; monomorphized function and then takes its name).  AST-WFP-RULES supplies
; the corresponding facts for the other accessors.  The :APPN and :ARRAY
; goals also arise in CONSP form, consuming the LEN/CONSP bridges of the
; first section.

(defruled valid-identifier-string-p-of-expr-var->name-when-expr-wfp
  :short "Bridge between the shape of a goal and the facts above:
          the name of a well-formed @(':var') node is a valid identifier."
  (implies (and (expr-wfp e)
                (equal (expr-kind e) :var))
           (valid-identifier-string-p (expr-var->name e)))
  :enable expr-wfp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The main induction.  The :EXPAND hints are for the functions and
; predicates whose case analysis the prover does not open on its own, and
; for the constructors whose well-formedness constrains the length of a
; list argument.

(defret-mutual monomorphize-impl-wfp
  (defret expr-wfp-of-mono-expr
    (implies (and (expr-wfp x)
                  (type-map-wfp type-map)
                  (fn-info-map-wfp fn-info-map))
             (and (expr-wfp new-expr)
                  (fn-info-map-wfp new-fn-info-map)))
    :fn mono-expr)
  (defret expr-list-wfp-of-mono-expr-list
    (implies (and (expr-list-wfp x)
                  (type-map-wfp type-map)
                  (fn-info-map-wfp fn-info-map))
             (and (expr-list-wfp new-exprs)
                  (fn-info-map-wfp new-fn-info-map)))
    :fn mono-expr-list)
  (defret atom-wfp-of-mono-atom
    (implies (and (atom-wfp x)
                  (type-map-wfp type-map)
                  (fn-info-map-wfp fn-info-map))
             (and (atom-wfp new-atom)
                  (fn-info-map-wfp new-fn-info-map)))
    :fn mono-atom)
  (defret atom-list-wfp-of-mono-atom-list
    (implies (and (atom-list-wfp x)
                  (type-map-wfp type-map)
                  (fn-info-map-wfp fn-info-map))
             (and (atom-list-wfp new-atoms)
                  (fn-info-map-wfp new-fn-info-map)))
    :fn mono-atom-list)
  (defret bind-wfp-of-mono-bind
    (implies (and (bind-wfp x)
                  (type-map-wfp type-map)
                  (fn-info-map-wfp fn-info-map))
             (and (bind-wfp new-bind)
                  (fn-info-map-wfp new-fn-info-map)))
    :fn mono-bind)
  (defret bind-list-wfp-of-mono-fun-instances
    (implies (and (bind-wfp fun-bind)
                  (inst-request-list-wfp requests)
                  (type-map-wfp type-map)
                  (fn-info-map-wfp fn-info-map))
             (and (bind-list-wfp insts)
                  (fn-info-map-wfp new-fn-info-map)))
    :fn mono-fun-instances)
  (defret bind-wfp-of-mono-cfun-instance
    (implies (and (stringp inst-name)
                  (valid-identifier-string-p inst-name)
                  (type-list-wfp targ-tys)
                  (bind-wfp cfun-bind)
                  (type-map-wfp type-map)
                  (fn-info-map-wfp fn-info-map))
             (and (bind-wfp inst-bind)
                  (fn-info-map-wfp new-fn-info-map)))
    :fn mono-cfun-instance)
  (defret bind-wfp-of-mono-ifun-instance
    (implies (and (stringp inst-name)
                  (valid-identifier-string-p inst-name)
                  (bind-wfp ifun-bind)
                  (type-map-wfp type-map)
                  (fn-info-map-wfp fn-info-map))
             (and (bind-wfp inst-bind)
                  (fn-info-map-wfp new-fn-info-map)))
    :fn mono-ifun-instance)
  :mutual-recursion monomorphize-impl
  :hints (("Goal" :in-theory (enable* mono-expr
                                      mono-expr-list
                                      mono-atom
                                      mono-atom-list
                                      mono-bind
                                      mono-fun-instances
                                      mono-cfun-instance
                                      mono-ifun-instance
                                      expr-wfp expr-list-wfp
                                      atom-wfp atom-list-wfp
                                      bind-wfp bind-list-wfp
                                      var+type?-wfp
                                      inst-request-wfp
                                      inst-request-list-wfp
                                      type-var-list-option-wfp
                                      ispace-var-list-option-wfp
                                      type-list-option-wfp
                                      ispace-list-option-wfp
                                      type-option-wfp
                                      valid-identifier-string-p-of-expr-var->name-when-expr-wfp
                                      positive-len-when-consp
                                      len->=-2-when-consp-of-cdr
                                      consp-of-mono-expr-list
                                      consp-of-mono-atom-list
                                      consp-of-cdr-of-mono-expr-list
                                      consp-of-cdr-of-mono-atom-list
                                      len-of-mono-expr-list
                                      len-of-mono-atom-list)
           :expand ((mono-expr x defs fn-info-map denv type-map)
                    (mono-bind x defs fn-info-map denv type-map)
                    (expr-wfp x)
                    (bind-wfp x)
                    (:free (n) (expr-wfp (expr-var n)))
                    (:free (f a) (expr-wfp (expr-app f a)))
                    (:free (bs b) (expr-wfp (expr-let bs b)))
                    (:free (ds as) (expr-wfp (expr-array ds as)))
                    (:free (ds es) (expr-wfp (expr-frame ds es)))
                    (:free (f as) (expr-wfp (expr-appn f as)))
                    (:free (es) (expr-wfp (expr-bracket es)))
                    (:free (f as) (expr-wfp (expr-tappn f as)))
                    (:free (f as) (expr-wfp (expr-iappn f as)))
                    (:free (i v tg b ty) (expr-wfp (expr-unbox i v tg b ty)))
                    (:free (is v tg b ty) (expr-wfp (expr-unboxn is v tg b ty)))
                    (:free (ps b ty) (atom-wfp (atom-lambdan ps b ty)))
                    (:free (ps b) (atom-wfp (atom-tlambdan ps b)))
                    (:free (ps b) (atom-wfp (atom-ilambdan ps b)))
                    (:free (is a ty) (atom-wfp (atom-boxn is a ty)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule expr-wfp-of-monomorphize-top-expr
  :short "Monomorphizing a well-formed expression
          yields a well-formed expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the promised property.  The entry point starts from the
     empty type substitution and the empty registration map, which
     satisfy the two invariants vacuously, and applies the two
     @(':let') normalizations and the name uniquification around
     the traversal."))
  (implies (expr-wfp expr)
           (expr-wfp (mv-nth 2 (monomorphize-top-expr expr))))
  :enable monomorphize-top-expr)
