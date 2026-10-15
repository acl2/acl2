; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "renaming-evaluation")

(local (include-book "kestrel/utilities/ordinals" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ value-groundness
  :parents (unique-names-validation)
  :short "Values that embed no abstract syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "Most values carry no abstract syntax, but some do: the three kinds of
     lambda value embed the body of the abstraction, and the type values of
     universal, product, and sum types embed the body of the type.  A value
     that embeds none is called ground.")
   (xdoc::p
    "Renaming the variables of an expression (see @(see unique-names))
     touches only abstract syntax, and a ground value embeds none, so ground
     values are unaffected by renaming: on ground results, agreement modulo
     renaming is literal equality.  The proof of @(tsee eval-top-expr-of-expr-uniquify-names)
     uses groundness as the proviso of its main theorem and in the collapse
     of the witness-indexed value relation on ground values (see @(see
     uniquify-alpha-relations)), which compares ground values by plain
     equality."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Groundness of values: no embedded abstract syntax.

;; The type-values/denv clique includes the map from type variables to type
;; values (for the environments captured in type values), for which
;; DEFFOLD-REDUCE generates a theorem about the values of OMAP::ASSOC whose
;; proof needs OMAP::ASSOC to open; the macro provides no hints for it, so
;; we enable it locally around the fold.

(encapsulate ()

  (local (in-theory (enable omap::assoc)))

  (fty::deffold-reduce groundp
    :short "Check that a (type or expression) value embeds no abstract syntax."
    :long
    (xdoc::topstring
     (xdoc::p
      "Base values, primitive operations, and vectors of ground values are
       ground.  Lambda values (of all three kinds) are not, since they embed
       the abstract syntax of their bodies; neither are the type values of
       universal, product, and sum types, for the same reason.  The dynamic
       environments captured in the latter are reached by the fold but do
       not matter, since the type values containing them are never ground.")
     (xdoc::p
      "Ground values are unaffected by renaming the variables of the
       expression that produced them; this is the proviso under which
       evaluation results are literally equal in
       @('eval-top-expr-of-expr-uniquify-names')."))
    :types (type-values/denv
            expr-values/denv)
    :result booleanp
    :default t
    :combine and
    :override
    ((type-value :forall nil)
     (type-value :pi nil)
     (type-value :sigma nil)
     (expr-value :lambda nil)
     (expr-value :tlambda nil)
     (expr-value :ilambda nil))
    :name value-groundp))
