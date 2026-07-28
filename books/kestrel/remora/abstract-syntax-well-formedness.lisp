; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Eric McCarthy (bendyarm on GitHub)
;          Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-trees")
(include-book "identifier-syntax")

(include-book "kestrel/fty/deffold-reduce" :dir :system)
(include-book "kestrel/utilities/ordinals" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-well-formedness
  :parents (abstract-syntax)
  :short "Well-formedness of ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The fixtypes of ASTs in @(see abstract-syntax-trees)
     do not capture all the constraints on ASTs,
     as stated in the documentation there.
     We capture these additional constraints
     via the well-formedness predicates on ASTs defined here.")
   (xdoc::p
    "Two classes of constraints are enforced:")
   (xdoc::ul
    (xdoc::li
     "Identifier strings stored inside AST nodes
      pass @(tsee valid-identifier-string-p):
      they decode as well-formed UTF-8,
      start with an @(tsee id-startp) code point,
      continue with @(tsee id-continuep) code points,
      and are not in @(tsee *remora-keywords-as-natlists*).")
    (xdoc::li
     "Certain lists contain one or more elements,
      and certain lists two or more elements.
      For instance, the fact that
      @(':bracket') expression lists
      (grammar: @('\"[\" ws exp *( ws exp ) ws \"]\"')
      contain at least one expression)."))
   (xdoc::p
    "All these well-formedness constraints on ASTs
     are established by the syntax abstraction mapping,
     and are preserved by all the transformations of the ASTs,
     including type checking/inference.
     We plan to prove these properties.")
   (xdoc::p
    "Although the well-formedness constraints come from the grammar,
     they are actually slightly weaker than the grammar,
     because ASTs allow type annotations that the grammar does not have.
     Those type annotations are subject to
     the same well-formedness constraints as other similar ASTs,
     but the annotations themselves have no grammar counterpart.
     We plan to define slightly stronger predicates on ASTs
     that say when ASTs are grammatical,
     i.e. correspond to the grammar exactly.
     These stronger predicates are
     ensured by the syntax abstraction mapping after parsing,
     and required by the printer
     (or, more in general, by a syntax concretization mapping
     that is inverse of the syntax abstract mapping,
     although we have not defined this concretization mapping yet),
     but may be violated in between,
     particularly by type checking/inference."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce wfp
  :short "Well-formedness predicate over ASTs."
  :types (dims
          shapes/ispaces
          ispace-list-option
          ispace-var
          ispace-var-list
          ispace-var-list-option
          type-var
          type-var-list
          type-var-list-option
          base-type
          types
          type-option
          type-list-option
          var+type?
          var+type?-list
          exprs/atoms/binds)
  :result booleanp
  :default t
  :combine and
  :override
  (;; Identifier strings inside variables and binders.
   (dim :var (valid-identifier-string-p (dim-var->name dim)))
   (shape :var (valid-identifier-string-p (shape-var->name shape)))
   (ispace-var :dim (valid-identifier-string-p
                     (ispace-var-dim->name ispace-var)))
   (ispace-var :shape (valid-identifier-string-p
                       (ispace-var-shape->name ispace-var)))
   (type-var :atom (valid-identifier-string-p
                    (type-var-atom->name type-var)))
   (type-var :array (valid-identifier-string-p
                     (type-var-array->name type-var)))
   (var+type? (and (valid-identifier-string-p (var+type?->var var+type?))
                   (type-option-wfp (var+type?->type? var+type?))))
   (expr :var (valid-identifier-string-p (expr-var->name expr)))
   (bind :val (and (valid-identifier-string-p (bind-val->var bind))
                   (type-option-wfp (bind-val->type? bind))
                   (expr-wfp (bind-val->expr bind))))
   (bind :fun (and (valid-identifier-string-p (bind-fun->var bind))
                   (var+type?-list-wfp (bind-fun->params bind))
                   (type-option-wfp (bind-fun->type? bind))
                   (expr-wfp (bind-fun->expr bind))))
   (bind :tfun (and (valid-identifier-string-p (bind-tfun->var bind))
                    (type-var-list-wfp (bind-tfun->params bind))
                    (type-option-wfp (bind-tfun->type? bind))
                    (expr-wfp (bind-tfun->expr bind))))
   (bind :ifun (and (valid-identifier-string-p (bind-ifun->var bind))
                    (ispace-var-list-wfp (bind-ifun->params bind))
                    (type-option-wfp (bind-ifun->type? bind))
                    (expr-wfp (bind-ifun->expr bind))))
   (bind :cfun (and (valid-identifier-string-p (bind-cfun->var bind))
                    (type-var-list-option-wfp
                     (bind-cfun->tparams? bind))
                    (ispace-var-list-option-wfp
                     (bind-cfun->iparams? bind))
                    (var+type?-list-wfp (bind-cfun->params bind))
                    (type-wfp (bind-cfun->type bind))
                    (expr-wfp (bind-cfun->expr bind))))
   ;; Unbox binds a string variable; check it.
   (expr :unbox (and (ispace-var-wfp (expr-unbox->ispace expr))
                     (valid-identifier-string-p (expr-unbox->var expr))
                     (expr-wfp (expr-unbox->target expr))
                     (expr-wfp (expr-unbox->body expr))))
   (expr :unboxn (and (ispace-var-list-wfp (expr-unboxn->ispaces expr))
                      (valid-identifier-string-p (expr-unboxn->var expr))
                      (expr-wfp (expr-unboxn->target expr))
                      (expr-wfp (expr-unboxn->body expr))))
   ;; Grammar non-emptiness requirement (bracket-frame = "[" ws exp *( ws exp ) ws "]").
   (expr :bracket (and (consp (expr-bracket->exprs expr))
                       (expr-list-wfp (expr-bracket->exprs expr)))))
  :name abstract-syntax-wfp)
