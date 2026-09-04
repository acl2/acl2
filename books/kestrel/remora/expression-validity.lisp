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
     needs the requirement on the type, which is part of the expression."))

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
                    (atom-listp atoms)
                    (typep type)
                    (not (member-equal 0 dims))
                    (equal (len atoms) (nat-list-product dims))
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
                 (typep type)
                 (type-ok ivars tvars type)
                 (type-atom-kindp type)
                 (member-equal 0 dims))
                (expr-ok ivars tvars evars
                         (expr-array-empty dims type)
                         (type-array type
                                     (ispace-shape
                                      (shape-dims (dim-const-list dims))))))

   ;; frame expressions:

   ;; TODO

   ;; string literals:

   ;; TODO

   ;; application expressions:

   ;; TODO

   ;; unboxing expressions:

   ;; TODO

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

   ;; TODO

   ;; boxing atoms:

   ;; TODO

   ;; lists of expressions:

   (empty ((ispace-var-setp ivars)
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

   (empty ((ispace-var-setp ivars)
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
