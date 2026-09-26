; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "type-validity")
(include-book "type-equivalence")
(include-book "shape-ordering")
(include-book "variable-substitution-operations")

(include-book "nat-lists")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ expression-validity
  :parents (static-semantics)
  :short "Validity of expressions, including atoms."
  :long
  (xdoc::topstring
   (xdoc::p
    "The typing rules for expressions and atoms in [thesis] [arxiv] [esop]
     prove judgements of the form
     @($\\Theta; \\Delta; \\Gamma \\vdash t : \\tau$),
     where
     @($\\Theta$) is a sort environment that assigns sorts to variables,
     @($\\Delta$) is a kind environment that assigns kinds to variables,
     @($\\Gamma$) is a type environment that assigns types to variables,
     @($t$) is an expression or atom, and
     @($\\tau$) is a type.")
   (xdoc::p
    "Our inference rules prove judgements (i.e. define predicates) of that form,
     which say that an expression or atom
     satisfies all the static validity conditions and has a certain type.
     We have separate predicates for expressions and atoms.")
   (xdoc::p
    "Sort and kind environments are modeled
     as sets of ispace and type variables,
     as in @(see ispace-validity) and @(see type-validity).")
   (xdoc::p
    "Type environments are modeled as maps from names to types,
     similarly to @($\\Gamma$) in [thesis] [arxiv] [esop].
     Variables are always for expressions, never for atoms;
     so the types in the map should all have the array kind.
     Currently the inference rules enforce that not on the maps themselves,
     but on the types looked up in the maps."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definductive expression/atom-validity-definition
  :short "Inference rules that define expression and atom validity."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides the predicates for individual expressions and atoms,
     we define predicates for lists of expressions and atoms,
     with associated lists of types of the same length.
     This corresponds to @($\\cdots$) in [thesis] [arxiv] [esop].")
   (xdoc::p
    "The rules follow [thesis] [arxiv] [esop],
     with the necessary adaptations to the richer forms of our ASTs.")
   (xdoc::p
    "The rule for non-empty arrays
     omit the premise from [thesis] [arxiv] saying that
     the type of the elements is valid and has atom kind,
     because it should be a consequence of the fact that
     there is at least one atom that has that type;
     we plan to prove this formally.
     The rule for empty arrays, in contrast,
     needs the requirement on the type, which is part of the expression.
     The rules for non-empty and empty frames
     follow a similar pattern in that respect.")
   (xdoc::p
    "For expression application,
     we use @(tsee shape-lubp) to say that the principal shape is
     the least upper bound of the function shape and argument frame.
     While [thesis] and [arxiv] use
     an equality to the least upper bound operator,
     that least upper bound may not exist,
     so our use of a predicate is more clear
     (the intention of that equality in [thesis] and [arxiv]
     is to imply that the least upper bound exists).
     The rule has a premise requiring the principal shape to be valid
     because that does not follow from the least upper bound predicate
     (e.g. it could include a variable not in @('ivars')).")
   (xdoc::p
    "For type application,
     the type argument must have the same kind as
     the parameter of the universal type,
     as in [thesis] [arxiv].
     We do not lift an atom-kinded argument to a scalar array type
     when the parameter is array-kinded.
     This differs from [impl],
     where an array-kinded type parameter stands for
     an atom type variable and a shape variable,
     so that an atom-kinded argument instantiates just the former,
     leaving the latter abstracted;
     we plan to conform to [impl] at some point.
     The two substitution maps are set up
     as in the @('forall') rule of @(see type-equivalence-definition).
     The substitution is @(tsee type-subst-type-vars),
     guarded by @(tsee type-subst-type-vars-no-capture-p):
     when the substitution would capture variables,
     the rule does not apply directly,
     but the binders in the type of the function
     can be alpha-renamed via the @('eqv') rule first,
     so no generality is lost.")
   (xdoc::p
    "Ispace application is similar to type application,
     but the function must have a product type instead of a universal one,
     and we apply an ispace substitution instead of a type substitution.
     Furthermore, there is an additional application of the ispace substitution,
     namely to the shape of the body type of the product type.")
   (xdoc::p
    "The rule for unboxing includes the requirement that
     the bound ispace variable is not already in the sort environment,
     otherwise the bound variable is confused with the one already in scope,
     in the types of the type environment and in the type of the expression,
     which breaks type safety;
     this is implicit in [thesis] [arxiv],
     via the usual convention that
     bound variables differ from the variables in scope,
     which alpha equivalence makes possible.
     The renaming of the bound variable of the sum type
     to the bound variable of the unboxing expression
     is @(tsee type-rename-ispace-vars),
     with the two renaming maps set up as in the application rules,
     guarded by @(tsee type-rename-ispace-vars-no-capture-p);
     when the renaming would capture variables,
     the binders in the type of the target
     can be alpha-renamed via the @('eqv') rule first.
     The rule requires the type annotation to be present,
     and to be equivalent to the type that the rule in [thesis] [arxiv]
     assigns to the unboxing expression.
     The requirement in [thesis] [arxiv] that
     the resulting type is valid in the enclosing environments,
     which prevents the bound ispace variable from escaping,
     is applied to the annotation,
     because that is the type assigned to the expression,
     and validity is not preserved by type equivalence.")
   (xdoc::p
    "The rule for expression lambda abstractions requires the presence of
     both the type of the parameter and the type of the body,
     which form the input and output types of the function type.
     The input type must be valid and array-kinded.
     The body must be valid, and have the output type,
     in the environment augmented with the parameter.")
   (xdoc::p
    "For a type lambda abstraction,
     the body must be valid in the environment augmented with the parameter,
     and the abstraction has the universal type
     consisting of the parameter and the body type.
     The parameter must not occur in the kind environment already
     (an implicit requirement in [thesis] [arxiv]).")
   (xdoc::p
    "The rule for an ispace lambda abstraction
     is similar to the one for a type lambda abstraction."))

  :preds ((expr-ok ivars tvars evars expr type)
          (atom-ok ivars tvars evars atom type)
          (exprs-ok ivars tvars evars exprs types)
          (atoms-ok ivars tvars evars atoms types))

  :irules

  (;; equivalence:

   (eqv ((ispace-var-setp ivars)
         (type-var-setp tvars)
         (string-type-mapp evars)
         (exprp expr)
         (typep type1)
         (typep type2)
         (expr-ok ivars tvars evars expr type1)
         (type-eq type1 type2))
        (expr-ok ivars tvars evars expr type2))

   (eqv ((ispace-var-setp ivars)
         (type-var-setp tvars)
         (string-type-mapp evars)
         (atomp atom)
         (typep type1)
         (typep type2)
         (atom-ok ivars tvars evars atom type1)
         (type-eq type1 type2))
        (atom-ok ivars tvars evars atom type2))

   ;; expression variables:

   (var ((ispace-var-setp ivars)
         (type-var-setp tvars)
         (string-type-mapp evars)
         (stringp name)
         (set::in name (omap::keys evars))
         (equal type (omap::lookup name evars))
         (type-array-kindp type))
        (expr-ok ivars tvars evars (expr-var name) type))

   ;; atom expressions:

   (atom ((ispace-var-setp ivars)
          (type-var-setp tvars)
          (string-type-mapp evars)
          (atomp atom)
          (typep type)
          (atom-ok ivars tvars evars atom type))
         (expr-ok ivars tvars evars (expr-atom atom) (tarr type (shp))))

   ;; array expressions:

   (array-nonempty ((ispace-var-setp ivars)
                    (type-var-setp tvars)
                    (string-type-mapp evars)
                    (nat-listp dims)
                    (not (member-equal 0 dims))
                    (atom-listp atoms)
                    (equal (len atoms) (nat-list-product dims))
                    (typep type)
                    (atoms-ok ivars tvars evars
                              atoms
                              (repeat (len atoms) type)))
                   (expr-ok ivars tvars evars
                            (expr-array dims atoms)
                            (type-array type
                                        (ispace-shape
                                         (shape-dims (dim-const-list dims))))))

   (array-empty ((ispace-var-setp ivars)
                 (type-var-setp tvars)
                 (string-type-mapp evars)
                 (nat-listp dims)
                 (member-equal 0 dims)
                 (typep type)
                 (type-ok ivars tvars type)
                 (type-atom-kindp type))
                (expr-ok ivars tvars evars
                         (expr-array-empty dims type)
                         (type-array type
                                     (ispace-shape
                                      (shape-dims (dim-const-list dims))))))

   ;; frame expressions:

   (frame-nonempty ((ispace-var-setp ivars)
                    (type-var-setp tvars)
                    (string-type-mapp evars)
                    (nat-listp dims)
                    (not (member-equal 0 dims))
                    (expr-listp exprs)
                    (equal (len exprs) (nat-list-product dims))
                    (typep type)
                    (shapep shape)
                    (exprs-ok ivars tvars evars
                              exprs
                              (repeat (len exprs)
                                      (type-array type
                                                  (ispace-shape shape)))))
                   (expr-ok ivars tvars evars
                            (expr-frame dims exprs)
                            (type-array type
                                        (ispace-shape
                                         (shp++ (shape-dims
                                                 (dim-const-list dims))
                                                shape)))))

   (frame-empty ((ispace-var-setp ivars)
                 (type-var-setp tvars)
                 (string-type-mapp evars)
                 (nat-listp dims)
                 (member-equal 0 dims)
                 (typep cell-type)
                 (typep type)
                 (shapep shape)
                 (type-ok ivars tvars cell-type)
                 (type-ok ivars tvars type)
                 (type-atom-kindp type)
                 (shape-ok ivars shape)
                 (type-eq cell-type (type-array type (ispace-shape shape))))
                (expr-ok ivars tvars evars
                         (expr-frame-empty dims cell-type)
                         (type-array type
                                     (ispace-shape
                                      (shp++ (shape-dims
                                              (dim-const-list dims))
                                             shape)))))

   ;; string literals:

   (string ((ispace-var-setp ivars)
            (type-var-setp tvars)
            (string-type-mapp evars)
            (char-lit-listp chars))
           (expr-ok ivars tvars evars
                    (expr-string chars)
                    (type-array (type-base (base-type-int))
                                (ispace-dim (dim-const (len chars))))))

   ;; application expressions:

   (eapp ((ispace-var-setp ivars)
          (type-var-setp tvars)
          (string-type-mapp evars)
          (exprp fun)
          (exprp arg)
          (typep type-in)
          (typep type-out)
          (shapep shape-in)
          (shapep shape-out)
          (shapep shape-fun)
          (shapep shape-arg)
          (shapep shape-princ)
          (expr-ok ivars tvars evars
                   fun
                   (type-array (type-fun (type-array type-in
                                                     (ispace-shape shape-in))
                                         (type-array type-out
                                                     (ispace-shape shape-out)))
                               (ispace-shape shape-fun)))
          (expr-ok ivars tvars evars
                   arg
                   (type-array type-in
                               (ispace-shape (shp++ shape-arg shape-in))))
          (shape-ok ivars shape-princ)
          (shape-lubp shape-princ shape-fun shape-arg))
         (expr-ok ivars tvars evars
                  (expr-app fun arg)
                  (type-array type-out
                              (ispace-shape (shp++ shape-princ shape-out)))))

   ;; TODO: eappn

   (tapp ((ispace-var-setp ivars)
          (type-var-setp tvars)
          (string-type-mapp evars)
          (exprp fun)
          (type-varp param)
          (typep type-arg)
          (typep type-body)
          (shapep shape-body)
          (shapep shape-fun)
          (expr-ok ivars tvars evars
                   fun
                   (type-array (type-forall param
                                            (type-array type-body
                                                        (ispace-shape
                                                         shape-body)))
                               (ispace-shape shape-fun)))
          (type-ok ivars tvars type-arg)
          (type-var-case
           param
           :atom
           (and (type-atom-kindp type-arg)
                (equal atom-subst
                       (omap::update (type-var-atom->name param)
                                     type-arg
                                     nil))
                (equal array-subst nil))
           :array
           (and (type-array-kindp type-arg)
                (equal atom-subst nil)
                (equal array-subst
                       (omap::update (type-var-array->name param)
                                     type-arg
                                     nil))))
          (type-subst-type-vars-no-capture-p type-body atom-subst array-subst))
         (expr-ok ivars tvars evars
                  (expr-tapp fun type-arg)
                  (type-array (type-subst-type-vars type-body
                                                    atom-subst
                                                    array-subst)
                              (ispace-shape (shp++ shape-fun shape-body)))))

   ;; TODO: tappn

   (iapp ((ispace-var-setp ivars)
          (type-var-setp tvars)
          (string-type-mapp evars)
          (exprp fun)
          (ispace-varp param)
          (ispacep ispace-arg)
          (typep type-body)
          (shapep shape-body)
          (shapep shape-fun)
          (expr-ok ivars tvars evars
                   fun
                   (type-array (type-pi param
                                        (type-array type-body
                                                    (ispace-shape
                                                     shape-body)))
                               (ispace-shape shape-fun)))
          (ispace-ok ivars ispace-arg)
          (ispace-var-case
           param
           :dim
           (and (ispace-case ispace-arg :dim)
                (equal dim-subst
                       (omap::update (ispace-var-dim->name param)
                                     (ispace-dim->dim ispace-arg)
                                     nil))
                (equal shape-subst nil))
           :shape
           (and (ispace-case ispace-arg :shape)
                (equal dim-subst nil)
                (equal shape-subst
                       (omap::update (ispace-var-shape->name param)
                                     (ispace-shape->shape ispace-arg)
                                     nil))))
          (type-subst-ispace-vars-no-capture-p type-body
                                               dim-subst
                                               shape-subst))
         (expr-ok ivars tvars evars
                  (expr-iapp fun ispace-arg)
                  (type-array (type-subst-ispace-vars type-body
                                                      dim-subst
                                                      shape-subst)
                              (ispace-shape (shp++ shape-fun
                                                   (shape-subst-ispace-vars
                                                    shape-body
                                                    dim-subst
                                                    shape-subst))))))

   ;; TODO: iappn

   ;; TODO: capp

   ;; unboxing expressions:

   (unbox ((ispace-var-setp ivars)
           (type-var-setp tvars)
           (string-type-mapp evars)
           (ispace-varp ivar)
           (ispace-varp param)
           (stringp evar)
           (exprp target)
           (exprp body)
           (typep type)
           (typep type-target)
           (typep type-body)
           (shapep shape-target)
           (shapep shape-body)
           (expr-ok ivars tvars evars
                    target
                    (type-array (type-sigma param type-target)
                                (ispace-shape shape-target)))
           (ispace-var-case
            param
            :dim
            (and (ispace-var-case ivar :dim)
                 (equal dim-ren
                        (omap::update (ispace-var-dim->name param)
                                      (ispace-var-dim->name ivar)
                                      nil))
                 (equal shape-ren nil))
            :shape
            (and (ispace-var-case ivar :shape)
                 (equal dim-ren nil)
                 (equal shape-ren
                        (omap::update (ispace-var-shape->name param)
                                      (ispace-var-shape->name ivar)
                                      nil))))
           (type-rename-ispace-vars-no-capture-p type-target
                                                 dim-ren
                                                 shape-ren)
           (not (set::in ivar ivars))
           (equal ivars1 (set::insert ivar ivars))
           (equal evars1 (omap::update evar
                                       (type-rename-ispace-vars type-target
                                                                dim-ren
                                                                shape-ren)
                                       evars))
           (expr-ok ivars1 tvars evars1
                    body
                    (type-array type-body
                                (ispace-shape shape-body)))
           (type-ok ivars tvars type)
           (type-eq type
                    (type-array type-body
                                (ispace-shape (shp++ shape-target
                                                     shape-body)))))
          (expr-ok ivars tvars evars
                   (expr-unbox ivar evar target body type)
                   type))

   ;; TODO: unboxn

   ;; splice expressions:

   ;; TODO

   ;; let expressions:

   ;; TODO

   ;; base literals:

   (bool ((ispace-var-setp ivars)
          (type-var-setp tvars)
          (string-type-mapp evars)
          (booleanp lit))
         (atom-ok ivars tvars evars
                  (atom-base (base-lit-bool lit))
                  (type-base (base-type-bool))))

   (int ((ispace-var-setp ivars)
         (type-var-setp tvars)
         (string-type-mapp evars)
         (int-litp lit))
        (atom-ok ivars tvars evars
                 (atom-base (base-lit-int lit))
                 (type-base (base-type-int))))

   (float ((ispace-var-setp ivars)
           (type-var-setp tvars)
           (string-type-mapp evars)
           (float-litp lit))
          (atom-ok ivars tvars evars
                   (atom-base (base-lit-float lit))
                   (type-base (base-type-float))))

   ;; abstraction atoms:

   (elambda ((ispace-var-setp ivars)
             (type-var-setp tvars)
             (string-type-mapp evars)
             (stringp evar)
             (exprp body)
             (typep type-in)
             (typep type-out)
             (type-ok ivars tvars type-in)
             (type-array-kindp type-in)
             (equal evars1 (omap::update evar type-in evars))
             (expr-ok ivars tvars evars1 body type-out))
            (atom-ok ivars tvars evars
                     (atom-lambda (var+type? evar type-in)
                                  body
                                  type-out)
                     (type-fun type-in type-out)))

   ;; TODO: elambdan

   (tlambda ((ispace-var-setp ivars)
             (type-var-setp tvars)
             (string-type-mapp evars)
             (type-varp param)
             (exprp body)
             (typep type)
             (not (set::in param tvars))
             (equal tvars1 (set::insert param tvars))
             (expr-ok ivars tvars1 evars body type))
            (atom-ok ivars tvars evars
                     (atom-tlambda param body)
                     (type-forall param type)))

   ;; TODO: tlambdan

   (ilambda ((ispace-var-setp ivars)
             (type-var-setp tvars)
             (string-type-mapp evars)
             (ispace-varp param)
             (exprp body)
             (typep type)
             (not (set::in param ivars))
             (equal ivars1 (set::insert param ivars))
             (expr-ok ivars1 tvars evars body type))
            (atom-ok ivars tvars evars
                     (atom-ilambda param body)
                     (type-pi param type)))

   ;; TODO: ilambdan

   ;; boxing atoms:

   ;; TODO

   ;; lists of expressions:

   (nil ((ispace-var-setp ivars)
         (type-var-setp tvars)
         (string-type-mapp evars))
        (exprs-ok ivars tvars evars nil nil))

   (cons ((ispace-var-setp ivars)
          (type-var-setp tvars)
          (string-type-mapp evars)
          (exprp expr)
          (expr-listp exprs)
          (typep type)
          (type-listp types)
          (expr-ok ivars tvars evars expr type)
          (exprs-ok ivars tvars evars exprs types))
         (exprs-ok ivars tvars evars (cons expr exprs) (cons type types)))

   ;; lists of atoms:

   (nil ((ispace-var-setp ivars)
         (type-var-setp tvars)
         (string-type-mapp evars))
        (atoms-ok ivars tvars evars nil nil))

   (cons ((ispace-var-setp ivars)
          (type-var-setp tvars)
          (string-type-mapp evars)
          (atomp atom)
          (atom-listp atoms)
          (typep type)
          (type-listp types)
          (atom-ok ivars tvars evars atom type)
          (atoms-ok ivars tvars evars atoms types))
         (atoms-ok ivars tvars evars (cons atom atoms) (cons type types)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection expression/atom-validity-guard-verification
  :short "Guard verification of the functions generated by
          @(see expression/atom-validity-definition)."

  ;; rule validity functions:

  (verify-guards expr-ok-eqv-validp)
  (verify-guards atom-ok-eqv-validp)
  (verify-guards expr-ok-var-validp)
  (verify-guards expr-ok-atom-validp)
  (verify-guards expr-ok-array-nonempty-validp)
  (verify-guards expr-ok-array-empty-validp)
  (verify-guards expr-ok-frame-nonempty-validp)
  (verify-guards expr-ok-frame-empty-validp)
  (verify-guards expr-ok-string-validp)
  (verify-guards expr-ok-eapp-validp)
  (verify-guards expr-ok-tapp-validp)
  (verify-guards expr-ok-iapp-validp)
  (verify-guards expr-ok-unbox-validp)
  (verify-guards atom-ok-bool-validp)
  (verify-guards atom-ok-int-validp)
  (verify-guards atom-ok-float-validp)
  (verify-guards atom-ok-elambda-validp)
  (verify-guards atom-ok-tlambda-validp)
  (verify-guards atom-ok-ilambda-validp)
  (verify-guards exprs-ok-nil-validp)
  (verify-guards exprs-ok-cons-validp)
  (verify-guards atoms-ok-nil-validp)
  (verify-guards atoms-ok-cons-validp)

  ;; proof validity functions:

  (verify-guards expr-ok-proof-validp
    :hints
    (("Goal"
      :in-theory (enable* expression/atom-validity-definition-validp-defs))))

  ;; minimality predicates:

  (verify-guards expr-ok-proof-minimalp)
  (verify-guards atom-ok-proof-minimalp)
  (verify-guards exprs-ok-proof-minimalp)
  (verify-guards atoms-ok-proof-minimalp)

  ;; validity predicates:

  (verify-guards expr-ok)
  (verify-guards atom-ok)
  (verify-guards exprs-ok)
  (verify-guards atoms-ok))
