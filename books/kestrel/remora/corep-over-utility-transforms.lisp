; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-core")
(include-book "utility-transforms")

(include-book "portcullis")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The rules that DEFFOLD-REDUCE and DEFFOLD-MAP generate for the constructors
; and accessors of each node, which is how the goals about a rebuilt node's
; core membership are decomposed.  (Same idiom as in @(see
; monomorphize-properties), whose main induction enables AST-COREP-RULES.)

(local (in-theory (enable* ast-corep-rules
                           ast-singletonize-let-rules
                           ast-flatten-let-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ corep-over-utility-transforms
  :parents (abstract-syntax-core)
  :short "Core-subset preservation for the AST operations
          that monomorphization builds on."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the parts of @(see monomorphize-properties) that do not
     mention monomorphization itself, collected here so that they can be
     certified without @(see monomorphize).")
   (xdoc::p
    "They cover the @(':let') normalizations @(tsee expr-singletonize-let)
     and @(tsee expr-flatten-let) (see @(see utility-transforms)), which
     monomorphization applies around its traversal."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The :LET normalizations preserve the core predicates.
;
; Each of SINGLETONIZE-LET and FLATTEN-LET is a DEFFOLD-MAP whose only
; override is the :LET case, which rebuilds the node with the helper
; below; every other case rebuilds its node with the same constructor, so
; the inductions need nothing but the helper lemmas and each other.

(defrule expr-corep-of-nest-let-binds
  :short "Nesting core binds around a core body yields a core expression."
  (implies (and (bind-list-corep binds)
                (expr-corep body))
           (expr-corep (nest-let-binds binds body)))
  :induct t
  :enable (nest-let-binds expr-corep bind-list-corep))

(defrule expr-corep-of-coalesce-let
  :short "Merging core binds into a core body yields a core expression."
  (implies (and (bind-list-corep binds)
                (expr-corep body))
           (expr-corep (coalesce-let binds body)))
  :enable (coalesce-let expr-corep bind-list-corep-of-append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection corep-of-singletonize-let
  :short "Rewriting multi-bind @(':let')s as nested single-bind @(':let')s
          preserves the core predicates."

  (defret-mutual shapes/ispaces-corep-of-shapes/ispaces-singletonize-let
    (defret shape-corep-of-shape-singletonize-let
      (implies (shape-corep shape)
               (shape-corep result))
      :fn shape-singletonize-let)
    (defret shape-list-corep-of-shape-list-singletonize-let
      (implies (shape-list-corep shape-list)
               (shape-list-corep result))
      :fn shape-list-singletonize-let)
    (defret ispace-corep-of-ispace-singletonize-let
      (implies (ispace-corep ispace)
               (ispace-corep result))
      :fn ispace-singletonize-let)
    (defret ispace-list-corep-of-ispace-list-singletonize-let
      (implies (ispace-list-corep ispace-list)
               (ispace-list-corep result))
      :fn ispace-list-singletonize-let)
    :mutual-recursion shapes/ispaces-singletonize-let
    :hints (("Goal" :in-theory (enable shape-singletonize-let
                                       shape-list-singletonize-let
                                       ispace-singletonize-let
                                       ispace-list-singletonize-let
                                       shape-corep
                                       shape-list-corep
                                       ispace-corep
                                       ispace-list-corep))))

  (defret-mutual types-corep-of-types-singletonize-let
    (defret type-corep-of-type-singletonize-let
      (implies (type-corep type)
               (type-corep result))
      :fn type-singletonize-let)
    (defret type-list-corep-of-type-list-singletonize-let
      (implies (type-list-corep type-list)
               (type-list-corep result))
      :fn type-list-singletonize-let)
    :mutual-recursion types-singletonize-let
    :hints (("Goal" :in-theory (enable type-singletonize-let
                                       type-list-singletonize-let
                                       type-corep
                                       type-list-corep))))

  (defrule type-option-corep-of-type-option-singletonize-let
    (implies (type-option-corep ty?)
             (type-option-corep (type-option-singletonize-let ty?)))
    :enable type-option-singletonize-let)

  (defrule var+type?-corep-of-var+type?-singletonize-let
    (implies (var+type?-corep vt)
             (var+type?-corep (var+type?-singletonize-let vt)))
    :enable (var+type?-singletonize-let var+type?-corep))

  (defrule var+type?-list-corep-of-var+type?-list-singletonize-let
    (implies (var+type?-list-corep vts)
             (var+type?-list-corep (var+type?-list-singletonize-let vts)))
    :induct t
    :enable (var+type?-list-singletonize-let var+type?-list-corep))

  (defret-mutual exprs/atoms/binds-corep-of-exprs/atoms/binds-singletonize-let
    (defret expr-corep-of-expr-singletonize-let
      (implies (expr-corep expr)
               (expr-corep result))
      :fn expr-singletonize-let)
    (defret expr-list-corep-of-expr-list-singletonize-let
      (implies (expr-list-corep expr-list)
               (expr-list-corep result))
      :fn expr-list-singletonize-let)
    (defret atom-corep-of-atom-singletonize-let
      (implies (atom-corep atom)
               (atom-corep result))
      :fn atom-singletonize-let)
    (defret atom-list-corep-of-atom-list-singletonize-let
      (implies (atom-list-corep atom-list)
               (atom-list-corep result))
      :fn atom-list-singletonize-let)
    (defret bind-corep-of-bind-singletonize-let
      (implies (bind-corep bind)
               (bind-corep result))
      :fn bind-singletonize-let)
    (defret bind-list-corep-of-bind-list-singletonize-let
      (implies (bind-list-corep bind-list)
               (bind-list-corep result))
      :fn bind-list-singletonize-let)
    :mutual-recursion exprs/atoms/binds-singletonize-let
    :hints (("Goal" :in-theory (enable expr-singletonize-let
                                       expr-list-singletonize-let
                                       atom-singletonize-let
                                       atom-list-singletonize-let
                                       bind-singletonize-let
                                       bind-list-singletonize-let
                                       expr-corep
                                       expr-list-corep
                                       atom-corep
                                       atom-list-corep
                                       bind-corep
                                       bind-list-corep)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection corep-of-flatten-let
  :short "Collapsing chains of @(':let')s preserves the core predicates."

  (defret-mutual shapes/ispaces-corep-of-shapes/ispaces-flatten-let
    (defret shape-corep-of-shape-flatten-let
      (implies (shape-corep shape)
               (shape-corep result))
      :fn shape-flatten-let)
    (defret shape-list-corep-of-shape-list-flatten-let
      (implies (shape-list-corep shape-list)
               (shape-list-corep result))
      :fn shape-list-flatten-let)
    (defret ispace-corep-of-ispace-flatten-let
      (implies (ispace-corep ispace)
               (ispace-corep result))
      :fn ispace-flatten-let)
    (defret ispace-list-corep-of-ispace-list-flatten-let
      (implies (ispace-list-corep ispace-list)
               (ispace-list-corep result))
      :fn ispace-list-flatten-let)
    :mutual-recursion shapes/ispaces-flatten-let
    :hints (("Goal" :in-theory (enable shape-flatten-let
                                       shape-list-flatten-let
                                       ispace-flatten-let
                                       ispace-list-flatten-let
                                       shape-corep
                                       shape-list-corep
                                       ispace-corep
                                       ispace-list-corep))))

  (defret-mutual types-corep-of-types-flatten-let
    (defret type-corep-of-type-flatten-let
      (implies (type-corep type)
               (type-corep result))
      :fn type-flatten-let)
    (defret type-list-corep-of-type-list-flatten-let
      (implies (type-list-corep type-list)
               (type-list-corep result))
      :fn type-list-flatten-let)
    :mutual-recursion types-flatten-let
    :hints (("Goal" :in-theory (enable type-flatten-let
                                       type-list-flatten-let
                                       type-corep
                                       type-list-corep))))

  (defrule type-option-corep-of-type-option-flatten-let
    (implies (type-option-corep ty?)
             (type-option-corep (type-option-flatten-let ty?)))
    :enable type-option-flatten-let)

  (defrule var+type?-corep-of-var+type?-flatten-let
    (implies (var+type?-corep vt)
             (var+type?-corep (var+type?-flatten-let vt)))
    :enable (var+type?-flatten-let var+type?-corep))

  (defrule var+type?-list-corep-of-var+type?-list-flatten-let
    (implies (var+type?-list-corep vts)
             (var+type?-list-corep (var+type?-list-flatten-let vts)))
    :induct t
    :enable (var+type?-list-flatten-let var+type?-list-corep))

  (defret-mutual exprs/atoms/binds-corep-of-exprs/atoms/binds-flatten-let
    (defret expr-corep-of-expr-flatten-let
      (implies (expr-corep expr)
               (expr-corep result))
      :fn expr-flatten-let)
    (defret expr-list-corep-of-expr-list-flatten-let
      (implies (expr-list-corep expr-list)
               (expr-list-corep result))
      :fn expr-list-flatten-let)
    (defret atom-corep-of-atom-flatten-let
      (implies (atom-corep atom)
               (atom-corep result))
      :fn atom-flatten-let)
    (defret atom-list-corep-of-atom-list-flatten-let
      (implies (atom-list-corep atom-list)
               (atom-list-corep result))
      :fn atom-list-flatten-let)
    (defret bind-corep-of-bind-flatten-let
      (implies (bind-corep bind)
               (bind-corep result))
      :fn bind-flatten-let)
    (defret bind-list-corep-of-bind-list-flatten-let
      (implies (bind-list-corep bind-list)
               (bind-list-corep result))
      :fn bind-list-flatten-let)
    :mutual-recursion exprs/atoms/binds-flatten-let
    :hints (("Goal" :in-theory (enable expr-flatten-let
                                       expr-list-flatten-let
                                       atom-flatten-let
                                       atom-list-flatten-let
                                       bind-flatten-let
                                       bind-list-flatten-let
                                       expr-corep
                                       expr-list-corep
                                       atom-corep
                                       atom-list-corep
                                       bind-corep
                                       bind-list-corep)))))

