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
          types
          type-option
          type-list-option
          var+type?
          var+type?-list
          exprs/atoms/binds
          decl
          decl-list
          file)
  :result booleanp
  :default t
  :combine and
  :override
  ((dim :var (valid-identifier-string-p dim.name))
   (shape :var (valid-identifier-string-p shape.name))
   (ispace-var :dim (valid-identifier-string-p ispace-var.name))
   (ispace-var :shape (valid-identifier-string-p ispace-var.name))
   (type-var :atom (valid-identifier-string-p type-var.name))
   (type-var :array (valid-identifier-string-p type-var.name))
   (type :funn (and (type-list-wfp type.in)
                    (type-wfp type.out)
                    (>= (len type.in) 1)))
   (type :foralln (and (type-var-list-wfp type.params)
                       (type-wfp type.body)
                       (>= (len type.params) 2)))
   (type :pin (and (ispace-var-list-wfp type.params)
                   (type-wfp type.body)
                   (>= (len type.params) 2)))
   (type :sigman (and (ispace-var-list-wfp type.params)
                      (type-wfp type.body)
                      (>= (len type.params) 2)))
   (var+type? (b* (((var+type? var+type?)))
                (and (valid-identifier-string-p var+type?.var)
                     (type-option-wfp var+type?.type?))))
   (expr :var (valid-identifier-string-p expr.name))
   (expr :array (and (atom-list-wfp expr.atoms)
                     (>= (len expr.atoms) 1)))
   (expr :frame (and (expr-list-wfp expr.exprs)
                     (>= (len expr.exprs) 1)))
   (expr :appn (and (expr-wfp expr.fun)
                    (expr-list-wfp expr.args)
                    (>= (len expr.args) 2)))
   (expr :tappn (and (expr-wfp expr.fun)
                     (type-list-wfp expr.args)
                     (>= (len expr.args) 2)))
   (expr :iappn (and (expr-wfp expr.fun)
                     (ispace-list-wfp expr.args)
                     (>= (len expr.args) 2)))
   (expr :unbox (and (ispace-var-wfp expr.ispace)
                     (valid-identifier-string-p expr.var)
                     (expr-wfp expr.target)
                     (expr-wfp expr.body)))
   (expr :unboxn (and (ispace-var-list-wfp expr.ispaces)
                      (valid-identifier-string-p expr.var)
                      (expr-wfp expr.target)
                      (expr-wfp expr.body)
                      (>= (len expr.ispaces) 2)))
   (expr :bracket (and (expr-list-wfp expr.exprs)
                       (>= (len expr.exprs) 1)))
   (expr :let (and (bind-list-wfp expr.binds)
                   (expr-wfp expr.body)
                   (>= (len expr.binds) 1)))
   (atom :lambdan (and (var+type?-list-wfp atom.params)
                       (expr-wfp atom.body)
                       (>= (len atom.params) 2)))
   (atom :tlambdan (and (type-var-list-wfp atom.params)
                        (expr-wfp atom.body)
                        (>= (len atom.params) 2)))
   (atom :ilambdan (and (ispace-var-list-wfp atom.params)
                        (expr-wfp atom.body)
                        (>= (len atom.params) 2)))
   (atom :boxn (and (ispace-list-wfp atom.ispaces)
                    (expr-wfp atom.array)
                    (type-wfp atom.type)
                    (>= (len atom.ispaces) 2)))
   (bind :val (and (valid-identifier-string-p bind.var)
                   (type-option-wfp bind.type?)
                   (expr-wfp bind.expr)))
   (bind :fun (and (valid-identifier-string-p bind.var)
                   (var+type?-list-wfp bind.params)
                   (type-option-wfp bind.type?)
                   (expr-wfp bind.expr)))
   (bind :tfun (and (valid-identifier-string-p bind.var)
                    (type-var-list-wfp bind.params)
                    (type-option-wfp bind.type?)
                    (expr-wfp bind.expr)))
   (bind :ifun (and (valid-identifier-string-p bind.var)
                    (ispace-var-list-wfp bind.params)
                    (type-option-wfp bind.type?)
                    (expr-wfp bind.expr)))
   (bind :cfun (and (valid-identifier-string-p bind.var)
                    (type-var-list-option-wfp bind.tparams?)
                    (ispace-var-list-option-wfp bind.iparams?)
                    (var+type?-list-wfp bind.params)
                    (type-wfp bind.type)
                    (expr-wfp bind.expr)))
   (decl :entry (and (valid-identifier-string-p decl.var)
                     (var+type?-list-wfp decl.params)
                     (type-option-wfp decl.type?)
                     (expr-wfp decl.expr))))
  :name abstract-syntax-wfp)
