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
(include-book "unique-names-properties")
(include-book "corep-over-utility-transforms")
(include-book "abstract-syntax-core")

(include-book "portcullis")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ monomorphize-properties
  :parents (monomorphize)
  :short "Properties of monomorphization."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we prove that monomorphization preserves membership in the core
     subset of the abstract syntax (see @(see abstract-syntax-core)): if an
     expression satisfies @(tsee expr-corep), so does its monomorphization.
     This is @(tsee expr-corep-of-monomorphize-top-expr), and the
     corresponding property of the traversal itself is @(tsee
     expr-corep-of-mono-expr).")
   (xdoc::p
    "The reason the property holds is that monomorphization is
     kind-preserving on core ASTs: every case of @(tsee mono-expr) and its
     companions rebuilds the AST node with the same constructor it took
     apart.  The cases that build a node of a different kind are exactly
     the ones that instantiate a polymorphic function --- a @(':capp')
     becomes an @(':appn') of a @(':var'), and a @(':cfun')/@(':ifun')
     bind is replaced by @(':fun')/@(':val') instance binds --- and those
     cases are unreachable from a core AST, because @(':capp'),
     @(':cfun'), and @(':ifun') are not in the core.  The @(':iapp') and
     @(':iappn') cases do rewrite a node to a @(':var'), which is in the
     core, so they need no such argument.")
   (xdoc::p
    "This is why the instance generators need no attention: instances are
     created only for recorded requests, requests are recorded only for
     registered @(':cfun')/@(':ifun') binds, and a core AST binds
     neither.  So the only fact needed about @(tsee mono-fun-instances)
     is the one for the empty request list, which is what the @(':let')
     case of @(tsee mono-expr) hands it when its bind is in the core; the
     three generators are skipped by the induction below.  In particular
     no property is needed of the dimension partial evaluation and type
     substitution that the generators apply to a definition body.")
   (xdoc::p
    "The other two layers are the @(':let') normalizations that @(tsee
     monomorphize-top-expr) applies around the traversal, @(tsee
     expr-singletonize-let) and @(tsee expr-flatten-let) (see @(see
     utility-transforms)).  They rewrite @(':let') nodes to @(':let')
     nodes, so they preserve the core predicates too; since they mention
     nothing of monomorphization, they are covered in @(see
     corep-over-utility-transforms).  Together with @(tsee
     expr-corep-of-expr-uniquify-names) (see @(see
     unique-names-properties)), which covers the third normalization,
     these compose into the top-level property.")
   (xdoc::p
    "There is no file-level counterpart of these theorems, since the core
     predicates are defined on expressions, not on declarations or files."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The monomorphization traversal itself.
;
; Each case rebuilds its node with the same constructor, so the core
; predicate of the result unfolds to the core predicates of the
; recursively monomorphized components, which the induction hypotheses
; supply.  The cases that build a node of a different kind --- the
; instantiation of a :CAPP, and the instance binds spliced into a :LET
; over a :CFUN/:IFUN bind --- are unreachable, since those kinds are not
; in the core; the goals for them are closed by the false hypothesis.
;
; The instance generators MONO-CFUN-INSTANCE and MONO-IFUN-INSTANCE are
; therefore skipped by the induction, and MONO-FUN-INSTANCES only needs
; the case of an empty request list, which is the one the :LET case of
; MONO-EXPR reaches with a core bind.  The :EXPAND hints are for the two
; functions whose case analysis the prover does not open on its own.

(defret-mutual monomorphize-impl-corep
  ; The main property: monomorphizing a core expression yields a core
  ; expression.
  (defret expr-corep-of-mono-expr
    (implies (expr-corep x)
             (expr-corep new-expr))
    :fn mono-expr)
  (defret expr-list-corep-of-mono-expr-list
    (implies (expr-list-corep x)
             (expr-list-corep new-exprs))
    :fn mono-expr-list)
  (defret atom-corep-of-mono-atom
    (implies (atom-corep x)
             (atom-corep new-atom))
    :fn mono-atom)
  (defret atom-list-corep-of-mono-atom-list
    (implies (atom-list-corep x)
             (atom-list-corep new-atoms))
    :fn mono-atom-list)
  (defret bind-corep-of-mono-bind
    (implies (bind-corep x)
             (bind-corep new-bind))
    :fn mono-bind)
  ; No instances are created for an empty list of requests, which is what
  ; the :LET case of MONO-EXPR asks for when its bind is in the core.
  (defret bind-list-corep-of-mono-fun-instances
    (implies (not (consp requests))
             (bind-list-corep insts))
    :fn mono-fun-instances)
  :skip-others t
  :mutual-recursion monomorphize-impl
  :hints (("Goal" :in-theory (enable* mono-expr
                                      mono-expr-list
                                      mono-atom
                                      mono-atom-list
                                      mono-bind
                                      mono-fun-instances
                                      expr-corep
                                      expr-list-corep
                                      atom-corep
                                      atom-list-corep
                                      bind-corep
                                      bind-list-corep
                                      var+type?-corep
                                      ast-corep-rules)
           :expand ((mono-expr x defs fn-info-map denv type-map)
                    (mono-bind x defs fn-info-map denv type-map)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule expr-corep-of-monomorphize-top-expr
  :short "Monomorphizing a core expression yields a core expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the promised property: @(tsee monomorphize-top-expr) can be
     applied to a program in the core subset of the abstract syntax
     without leaving that subset.  It composes the three normalizations
     that the entry point applies around the traversal with the
     traversal itself."))
  (implies (expr-corep expr)
           (expr-corep (mv-nth 2 (monomorphize-top-expr expr))))
  :enable monomorphize-top-expr)
