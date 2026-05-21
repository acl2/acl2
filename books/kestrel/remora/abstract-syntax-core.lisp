; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-trees")

(include-book "kestrel/fty/deffold-reduce" :dir :system)
(include-book "kestrel/utilities/ordinals" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-core
  :parents (abstract-syntax)
  :short "Core abstract syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "We characterize the subset of the ASTs
     that form the core of the language.
     This is mostly based on [thesis],
     but some choices are discussed in the documentation below."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce corep
  :short "Predicates on ASTs that characterize the core subset."
  :long
  (xdoc::topstring
   (xdoc::p
    "We exclude:")
   (xdoc::ul
    (xdoc::li
     "Shapes with zero or more dimensions,
      because they are expressible as concatenations of
      shapes with single dimensions.")
    (xdoc::li
     "Shape splices,
      because they are expressible as concatenations.")
    (xdoc::li
     "Bracket types,
      because they are expressible as array types.")
    (xdoc::li
     "String literals,
      because they are expressible as array expressions.")
    (xdoc::li
     "Combined applications,
      because they are expressible as simpler applications.")
    (xdoc::li
     "Bracket expressions,
      because they are expressible as array expressions.")
    (xdoc::li
     "Function bindings,
      because they are expressible as value bindings
      (to lambda abstractions)."))
   (xdoc::p
    "Perhaps surprisingly, we do not exclude @('let') expressions,
     although it seems that they should be reducible to
     applications of lambda abstractions.
     Abstractly, @($(\\mathbf{let}\\ x = a\\ \\mathbf{in}\\ b)$)
     is equivalent to @($((\\lambda x.\\ b)\\ a)$).
     However, if we attempt to perform that transformation
     on Remora's @('let') expressions,
     we run into the issue that,
     for the function bindings @(':fun'), @(':tfun'), and @(':ifun'),
     the result type is optional (see @(tsee bind)).
     This means that, if we attempt to turn those bindings
     into associations of lambda expressions to expression variables,
     we may not know the type of those expression variables,
     which is required in the outer lambda expression
     that we are trying to generate by desugaring.")
   (xdoc::p
    "For example, given")
   (xdoc::codeblock
    "(let ((fun (f (x Int)) <f-body>)) <let-body>)")
   (xdoc::p
    "which omits the optional result type of @('f'),
     first we turn the function binding into a value binding
     (which is part of our current desugaring)")
   (xdoc::codeblock
    "(let ((val f (fn ((x Int)) <f-body>))) <let-body>)")
   (xdoc::p
    "and then we can attempt to produce the application")
   (xdoc::codeblock
    "((fn ((f ?)) <let-body>) (fn ((x Int)) <f-body>))")
   (xdoc::p
    "but, as signified by the @('?'), which is a required type,
     we do not know which function type to use:
     we have its (only) input type @('Int'), but not its output type.
     This can be known via type checking,
     but the desugaring transformation is just a syntactic one.")
   (xdoc::p
    "The issue could be avoided by doing beta reduction as part of desugaring.
     That is, abstractly,
     instead of turning @($(\\mathbf{let}\\ x = a\\ \\mathbf{in}\\ b)$)
     into @($((\\lambda x.\\ b)\\ a)$),
     we could turn that directly into @($b[x/a]$),
     where that notation means that we substitute
     each free occurrence of @($x$) in @($b$) with @($a$).
     However, substitution may need to rename bound variables to avoid capture,
     and our current "
    (xdoc::seetopic "abstract-syntax-variable-operations"
                    "substitution operations")
    " do not do that yet.
     We plan to extend them to rename bound variables to avoid capture,
     but the fact remains that beta reduction adds conceptual complexity,
     partly due to the fact that there are many ways
     to rename bound variables to avoid capture;
     It is much simpler to generate an application of a lambda abstraction.")
   (xdoc::p
    "For now we keep @('let')s in the core.
     Note that the Remora syntax is likely to evolve
     towards requiring fewer type annotations,
     e.g. in lambda expressions,
     which could resolve the issue described above,
     i.e. it may allow us to produce applications of lambda expressions."))
  :types (shapes
          ispace
          ispace-list
          ispace-list-option
          types
          type-option
          var+type
          var+type-list
          exprs/atoms/binds
          expr-list-list
          atom-list-list
          prog)
  :result booleanp
  :default t
  :combine and
  :override
  ((shape :dims nil)
   (shape :splice nil)
   (type :bracket nil)
   (expr :string nil)
   (expr :capp nil)
   (expr :bracket nil)
   (bind :fun nil)
   (bind :tfun nil)
   (bind :ifun nil)
   (bind :cfun nil))
  :name ast-corep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ast-corep-additional-theorems
  :short "Additional theorems about the core AST predicates."

  (defruled shape-corep-when-var
    (implies (shape-case shape :var)
             (shape-corep shape))
    :enable shape-corep)

  (defruled shape-corep-when-dim
    (implies (shape-case shape :dim)
             (shape-corep shape))
    :enable shape-corep)

  (defruled ispace-corep-when-dim
    (implies (ispace-case ispace :dim)
             (ispace-corep ispace))
    :enable ispace-corep)

  (defruled type-corep-when-var
    (implies (type-case type :var)
             (type-corep type))
    :enable type-corep)

  (defruled type-corep-when-base
    (implies (type-case type :base)
             (type-corep type))
    :enable type-corep)

  (defruled expr-corep-when-var
    (implies (expr-case expr :var)
             (expr-corep expr))
    :enable expr-corep)

  (defruled atom-corep-when-base
    (implies (atom-case atom :base)
             (atom-corep atom))
    :enable atom-corep)

  (defruled not-bind-corep-when-fun
    (implies (equal (bind-kind bind) :fun)
             (not (bind-corep bind)))
    :enable bind-corep)

  (defruled not-bind-corep-when-tfun
    (implies (equal (bind-kind bind) :tfun)
             (not (bind-corep bind)))
    :enable bind-corep)

  (defruled not-bind-corep-when-ifun
    (implies (equal (bind-kind bind) :ifun)
             (not (bind-corep bind)))
    :enable bind-corep)

  (defruled not-bind-corep-when-cfun
    (implies (equal (bind-kind bind) :cfun)
             (not (bind-corep bind)))
    :enable bind-corep)

  (add-to-ruleset ast-corep-rules
                  '(shape-corep-when-var
                    shape-corep-when-dim
                    ispace-corep-when-dim
                    type-corep-when-var
                    type-corep-when-base
                    expr-corep-when-var
                    atom-corep-when-base
                    not-bind-corep-when-fun
                    not-bind-corep-when-tfun
                    not-bind-corep-when-ifun
                    not-bind-corep-when-cfun)))
