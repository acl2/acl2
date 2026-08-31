; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-well-formedness")
(include-book "variable-substitution-operations")
(include-book "utility-transforms")

(include-book "std/util/define-sk" :dir :system)

(include-book "portcullis")

(local (include-book "std/omaps/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The rules that DEFFOLD-REDUCE and DEFFOLD-MAP generate for the constructors
; and accessors of each node, which is how the goals about a rebuilt node's
; well-formedness are decomposed.  (Same idiom as in the sibling book
; WELL-FORMEDNESS-UNDER-DESUGARING.)

(local (in-theory (enable* ast-wfp-rules
                           ast-subst-type-vars-rules
                           ast-singletonize-let-rules
                           ast-flatten-let-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ well-formedness-support
  :parents (abstract-syntax-well-formedness)
  :short "Well-formedness of the AST operations that monomorphization builds on."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the parts of @(see monomorphize-well-formedness) that do not
     mention monomorphization itself, collected here so that they can be
     certified without @(see monomorphize).")
   (xdoc::p
    "The first section introduces @(tsee type-map-wfp), the invariant on
     type substitutions, and shows that it is preserved by the operations
     performed on those maps; the second shows that substituting type
     variables preserves well-formedness under that invariant.")
   (xdoc::p
    "The third section covers the @(':let') normalizations @(tsee
     expr-singletonize-let) and @(tsee expr-flatten-let), which
     monomorphization applies around its traversal."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The type-substitution invariant.
;
; A type substitution replaces a type variable by the type the map sends
; it to, so it preserves well-formedness exactly when those types are well
; formed.  As with RENAMING-WFP in UNIQUE-NAMES-WELL-FORMEDNESS, this is
; stated as a quantified predicate rather than a recursion over the omap,
; because every operation performed on these maps --- update, delete, and
; the bulk delete of the type variables bound at a binder --- has a rule
; about ASSOC, which is what the quantifier instantiates.

(define-sk type-map-wfp ((tmap string-type-mapp))
  :returns (yes/no booleanp)
  :short "Check that every type a type substitution may introduce
          is well formed."
  (forall (key)
          (b* ((tmap (string-type-map-fix tmap))
               (pair (omap::assoc key tmap)))
            (implies pair
                     (type-wfp (cdr pair))))))

(defsection type-map-wfp-lemmas
  :short "The type-substitution invariant is preserved by the operations
          on these maps."

  (defrule type-wfp-of-cdr-of-assoc-when-type-map-wfp
    (implies (and (type-map-wfp tmap)
                  (string-type-mapp tmap)
                  (omap::assoc key tmap))
             (type-wfp (cdr (omap::assoc key tmap))))
    :use type-map-wfp-necc)

  (defrule type-map-wfp-of-string-type-map-fix
    (equal (type-map-wfp (string-type-map-fix tmap))
           (type-map-wfp tmap))
    :expand ((type-map-wfp (string-type-map-fix tmap))
             (type-map-wfp tmap))
    :use ((:instance type-map-wfp-necc
                     (key (type-map-wfp-witness (string-type-map-fix tmap))))
          (:instance type-map-wfp-necc
                     (tmap (string-type-map-fix tmap))
                     (key (type-map-wfp-witness tmap)))))

  (defrule type-map-wfp-of-update
    (implies (and (type-map-wfp tmap)
                  (stringp key)
                  (typep val)
                  (type-wfp val))
             (type-map-wfp (omap::update key val (string-type-map-fix tmap))))
    :expand ((type-map-wfp (omap::update key val (string-type-map-fix tmap))))
    :use ((:instance type-map-wfp-necc
                     (key (type-map-wfp-witness
                           (omap::update key val (string-type-map-fix tmap)))))))

  (defrule type-map-wfp-of-delete
    (implies (type-map-wfp tmap)
             (type-map-wfp (omap::delete key (string-type-map-fix tmap))))
    :expand ((type-map-wfp (omap::delete key (string-type-map-fix tmap))))
    :use ((:instance type-map-wfp-necc
                     (key (type-map-wfp-witness
                           (omap::delete key (string-type-map-fix tmap)))))))

  (defrule type-map-wfp-of-delete*
    (implies (type-map-wfp tmap)
             (type-map-wfp (omap::delete* keys (string-type-map-fix tmap))))
    :expand ((type-map-wfp (omap::delete* keys (string-type-map-fix tmap))))
    :use ((:instance type-map-wfp-necc
                     (key (type-map-wfp-witness
                           (omap::delete* keys (string-type-map-fix tmap)))))))

  (defrule type-map-wfp-of-atom/array-subst-remove-bound
    :short "Reducing the substitutions at a binder preserves the invariant."
    (implies (and (type-map-wfp atom-subst)
                  (type-map-wfp array-subst))
             (b* (((mv new-atom new-array)
                   (atom/array-subst-remove-bound vars atom-subst array-subst)))
               (and (type-map-wfp new-atom)
                    (type-map-wfp new-array))))
    :enable atom/array-subst-remove-bound)

  (defrule type-map-wfp-of-nil
    :short "The empty substitution satisfies the invariant."
    (type-map-wfp nil)
    :expand ((type-map-wfp nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Type substitution preserves well-formedness under the invariant.

(defsection wfp-of-subst-type-vars
  :short "Substituting type variables preserves well-formedness,
          if the substituted types are well formed."

  (defret-mutual types-wfp-of-types-subst-type-vars
    (defret type-wfp-of-type-subst-type-vars
      (implies (and (type-wfp type)
                    (type-map-wfp atom-subst)
                    (type-map-wfp array-subst))
               (type-wfp result))
      :fn type-subst-type-vars)
    (defret type-list-wfp-of-type-list-subst-type-vars
      (implies (and (type-list-wfp type-list)
                    (type-map-wfp atom-subst)
                    (type-map-wfp array-subst))
               (type-list-wfp result))
      :fn type-list-subst-type-vars)
    :mutual-recursion types-subst-type-vars
    :hints (("Goal" :in-theory (enable type-subst-type-vars
                                       type-list-subst-type-vars
                                       type-wfp type-list-wfp
                                       len-of-type-list-subst-type-vars))))

  (defrule type-option-wfp-of-type-option-subst-type-vars
    (implies (and (type-option-wfp ty?)
                  (type-map-wfp atom-subst)
                  (type-map-wfp array-subst))
             (type-option-wfp (type-option-subst-type-vars ty? atom-subst array-subst)))
    :enable (type-option-subst-type-vars type-option-wfp
             type-option-some->val))

  (defrule type-list-option-wfp-of-type-list-option-subst-type-vars
    (implies (and (type-list-option-wfp tys?)
                  (type-map-wfp atom-subst)
                  (type-map-wfp array-subst))
             (type-list-option-wfp
              (type-list-option-subst-type-vars tys? atom-subst array-subst)))
    :enable (type-list-option-subst-type-vars type-list-option-wfp))

  (defrule var+type?-wfp-of-var+type?-subst-type-vars
    (implies (and (var+type?-wfp vt)
                  (type-map-wfp atom-subst)
                  (type-map-wfp array-subst))
             (var+type?-wfp (var+type?-subst-type-vars vt atom-subst array-subst)))
    :enable (var+type?-subst-type-vars var+type?-wfp))

  (defrule var+type?-list-wfp-of-var+type?-list-subst-type-vars
    (implies (and (var+type?-list-wfp vts)
                  (type-map-wfp atom-subst)
                  (type-map-wfp array-subst))
             (var+type?-list-wfp
              (var+type?-list-subst-type-vars vts atom-subst array-subst)))
    :induct t
    :enable (var+type?-list-subst-type-vars var+type?-list-wfp))

  ; The bind-list case of the fold is overridden, so DEFFOLD-MAP does not
  ; generate the length theorem for it.

  (defret-mutual len-of-bind-list-subst-type-vars
    (defret len-of-bind-list-subst-type-vars
      (equal (len result) (len bind-list))
      :fn bind-list-subst-type-vars)
    :skip-others t
    :mutual-recursion exprs/atoms/binds-subst-type-vars
    :hints (("Goal" :in-theory (enable bind-list-subst-type-vars len))))

  (defret-mutual consp-of-bind-list-subst-type-vars
    (defret consp-of-bind-list-subst-type-vars
      (equal (consp result) (consp bind-list))
      :fn bind-list-subst-type-vars)
    :skip-others t
    :mutual-recursion exprs/atoms/binds-subst-type-vars
    :hints (("Goal" :in-theory (enable bind-list-subst-type-vars))))

  (defret-mutual exprs/atoms/binds-wfp-of-exprs/atoms/binds-subst-type-vars
    (defret expr-wfp-of-expr-subst-type-vars
      (implies (and (expr-wfp expr)
                    (type-map-wfp atom-subst)
                    (type-map-wfp array-subst))
               (expr-wfp result))
      :fn expr-subst-type-vars)
    (defret expr-list-wfp-of-expr-list-subst-type-vars
      (implies (and (expr-list-wfp expr-list)
                    (type-map-wfp atom-subst)
                    (type-map-wfp array-subst))
               (expr-list-wfp result))
      :fn expr-list-subst-type-vars)
    (defret atom-wfp-of-atom-subst-type-vars
      (implies (and (atom-wfp atom)
                    (type-map-wfp atom-subst)
                    (type-map-wfp array-subst))
               (atom-wfp result))
      :fn atom-subst-type-vars)
    (defret atom-list-wfp-of-atom-list-subst-type-vars
      (implies (and (atom-list-wfp atom-list)
                    (type-map-wfp atom-subst)
                    (type-map-wfp array-subst))
               (atom-list-wfp result))
      :fn atom-list-subst-type-vars)
    (defret bind-wfp-of-bind-subst-type-vars
      (implies (and (bind-wfp bind)
                    (type-map-wfp atom-subst)
                    (type-map-wfp array-subst))
               (bind-wfp result))
      :fn bind-subst-type-vars)
    (defret bind-list-wfp-of-bind-list-subst-type-vars
      (implies (and (bind-list-wfp bind-list)
                    (type-map-wfp atom-subst)
                    (type-map-wfp array-subst))
               (bind-list-wfp result))
      :fn bind-list-subst-type-vars)
    :mutual-recursion exprs/atoms/binds-subst-type-vars
    :hints (("Goal" :in-theory (enable expr-subst-type-vars
                                       expr-list-subst-type-vars
                                       atom-subst-type-vars
                                       atom-list-subst-type-vars
                                       bind-subst-type-vars
                                       bind-list-subst-type-vars
                                       expr-wfp expr-list-wfp
                                       atom-wfp atom-list-wfp
                                       bind-wfp bind-list-wfp
                                       var+type?-wfp
                                       len-of-expr-list-subst-type-vars
                                       len-of-atom-list-subst-type-vars
                                       len-of-bind-list-subst-type-vars
                                       consp-of-bind-list-subst-type-vars
                                       len-of-type-list-subst-type-vars
                                       len-of-var+type?-list-subst-type-vars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The :LET normalizations preserve well-formedness.
;
; Each of SINGLETONIZE-LET and FLATTEN-LET is a DEFFOLD-MAP whose only
; override is the :LET case; the inductions consume the length theorems
; that DEFFOLD-MAP generates for the list functions, at every node whose
; well-formedness constrains a length.

(defsection wfp-of-singletonize-let
  :short "Rewriting multi-bind @(':let')s as nested single-bind @(':let')s
          preserves well-formedness."

  (defrule expr-wfp-of-nest-let-binds
    (implies (and (bind-list-wfp binds)
                  (expr-wfp body))
             (expr-wfp (nest-let-binds binds body)))
    :induct t
    :enable (nest-let-binds bind-list-wfp)
    :expand ((:free (bs b) (expr-wfp (expr-let bs b)))))

  (defret-mutual shapes/ispaces-wfp-of-shapes/ispaces-singletonize-let
    (defret shape-wfp-of-shape-singletonize-let
      (implies (shape-wfp shape) (shape-wfp result))
      :fn shape-singletonize-let)
    (defret shape-list-wfp-of-shape-list-singletonize-let
      (implies (shape-list-wfp shape-list) (shape-list-wfp result))
      :fn shape-list-singletonize-let)
    (defret ispace-wfp-of-ispace-singletonize-let
      (implies (ispace-wfp ispace) (ispace-wfp result))
      :fn ispace-singletonize-let)
    (defret ispace-list-wfp-of-ispace-list-singletonize-let
      (implies (ispace-list-wfp ispace-list) (ispace-list-wfp result))
      :fn ispace-list-singletonize-let)
    :mutual-recursion shapes/ispaces-singletonize-let
    :hints (("Goal" :in-theory (enable shape-singletonize-let
                                       shape-list-singletonize-let
                                       ispace-singletonize-let
                                       ispace-list-singletonize-let
                                       shape-wfp shape-list-wfp
                                       ispace-wfp ispace-list-wfp))))

  (defret-mutual types-wfp-of-types-singletonize-let
    (defret type-wfp-of-type-singletonize-let
      (implies (type-wfp type) (type-wfp result))
      :fn type-singletonize-let)
    (defret type-list-wfp-of-type-list-singletonize-let
      (implies (type-list-wfp type-list) (type-list-wfp result))
      :fn type-list-singletonize-let)
    :mutual-recursion types-singletonize-let
    :hints (("Goal" :in-theory (enable type-singletonize-let
                                       type-list-singletonize-let
                                       type-wfp type-list-wfp
                                       len-of-type-list-singletonize-let))))

  (defrule type-option-wfp-of-type-option-singletonize-let
    (implies (type-option-wfp ty?)
             (type-option-wfp (type-option-singletonize-let ty?)))
    :enable (type-option-singletonize-let type-option-wfp))

  (defrule type-list-option-wfp-of-type-list-option-singletonize-let
    (implies (type-list-option-wfp tys?)
             (type-list-option-wfp (type-list-option-singletonize-let tys?)))
    :enable (type-list-option-singletonize-let type-list-option-wfp))

  (defrule ispace-list-option-wfp-of-ispace-list-option-singletonize-let
    (implies (ispace-list-option-wfp isps?)
             (ispace-list-option-wfp (ispace-list-option-singletonize-let isps?)))
    :enable (ispace-list-option-singletonize-let ispace-list-option-wfp))

  (defrule var+type?-wfp-of-var+type?-singletonize-let
    (implies (var+type?-wfp vt)
             (var+type?-wfp (var+type?-singletonize-let vt)))
    :enable (var+type?-singletonize-let var+type?-wfp))

  (defrule var+type?-list-wfp-of-var+type?-list-singletonize-let
    (implies (var+type?-list-wfp vts)
             (var+type?-list-wfp (var+type?-list-singletonize-let vts)))
    :induct t
    :enable (var+type?-list-singletonize-let var+type?-list-wfp))

  (defret-mutual exprs/atoms/binds-wfp-of-exprs/atoms/binds-singletonize-let
    (defret expr-wfp-of-expr-singletonize-let
      (implies (expr-wfp expr) (expr-wfp result))
      :fn expr-singletonize-let)
    (defret expr-list-wfp-of-expr-list-singletonize-let
      (implies (expr-list-wfp expr-list) (expr-list-wfp result))
      :fn expr-list-singletonize-let)
    (defret atom-wfp-of-atom-singletonize-let
      (implies (atom-wfp atom) (atom-wfp result))
      :fn atom-singletonize-let)
    (defret atom-list-wfp-of-atom-list-singletonize-let
      (implies (atom-list-wfp atom-list) (atom-list-wfp result))
      :fn atom-list-singletonize-let)
    (defret bind-wfp-of-bind-singletonize-let
      (implies (bind-wfp bind) (bind-wfp result))
      :fn bind-singletonize-let)
    (defret bind-list-wfp-of-bind-list-singletonize-let
      (implies (bind-list-wfp bind-list) (bind-list-wfp result))
      :fn bind-list-singletonize-let)
    :mutual-recursion exprs/atoms/binds-singletonize-let
    :hints (("Goal" :in-theory (enable expr-singletonize-let
                                       expr-list-singletonize-let
                                       atom-singletonize-let
                                       atom-list-singletonize-let
                                       bind-singletonize-let
                                       bind-list-singletonize-let
                                       expr-wfp expr-list-wfp
                                       atom-wfp atom-list-wfp
                                       bind-wfp bind-list-wfp
                                       var+type?-wfp
                                       len-of-expr-list-singletonize-let
                                       len-of-atom-list-singletonize-let
                                       len-of-bind-list-singletonize-let
                                       len-of-type-list-singletonize-let
                                       len-of-ispace-list-singletonize-let
                                       len-of-var+type?-list-singletonize-let)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection wfp-of-flatten-let
  :short "Collapsing chains of @(':let')s preserves well-formedness."
  :long
  (xdoc::topstring
   (xdoc::p
    "@(tsee coalesce-let) builds a @(':let') out of the binds it is given
     and those of its body, so it needs the binds to be non-empty ---
     which they are, since a well-formed @(':let') has at least one bind
     and the fold maps its bind list pointwise."))

  (defrule expr-wfp-of-coalesce-let
    (implies (and (bind-list-wfp binds)
                  (consp binds)
                  (expr-wfp body))
             (expr-wfp (coalesce-let binds body)))
    :enable (coalesce-let bind-list-wfp-of-append
             positive-len-when-consp)
    :expand ((:free (bs b) (expr-wfp (expr-let bs b)))
             (expr-wfp body)))

  (defret-mutual shapes/ispaces-wfp-of-shapes/ispaces-flatten-let
    (defret shape-wfp-of-shape-flatten-let
      (implies (shape-wfp shape) (shape-wfp result))
      :fn shape-flatten-let)
    (defret shape-list-wfp-of-shape-list-flatten-let
      (implies (shape-list-wfp shape-list) (shape-list-wfp result))
      :fn shape-list-flatten-let)
    (defret ispace-wfp-of-ispace-flatten-let
      (implies (ispace-wfp ispace) (ispace-wfp result))
      :fn ispace-flatten-let)
    (defret ispace-list-wfp-of-ispace-list-flatten-let
      (implies (ispace-list-wfp ispace-list) (ispace-list-wfp result))
      :fn ispace-list-flatten-let)
    :mutual-recursion shapes/ispaces-flatten-let
    :hints (("Goal" :in-theory (enable shape-flatten-let
                                       shape-list-flatten-let
                                       ispace-flatten-let
                                       ispace-list-flatten-let
                                       shape-wfp shape-list-wfp
                                       ispace-wfp ispace-list-wfp))))

  (defret-mutual types-wfp-of-types-flatten-let
    (defret type-wfp-of-type-flatten-let
      (implies (type-wfp type) (type-wfp result))
      :fn type-flatten-let)
    (defret type-list-wfp-of-type-list-flatten-let
      (implies (type-list-wfp type-list) (type-list-wfp result))
      :fn type-list-flatten-let)
    :mutual-recursion types-flatten-let
    :hints (("Goal" :in-theory (enable type-flatten-let
                                       type-list-flatten-let
                                       type-wfp type-list-wfp
                                       len-of-type-list-flatten-let))))

  (defrule type-option-wfp-of-type-option-flatten-let
    (implies (type-option-wfp ty?)
             (type-option-wfp (type-option-flatten-let ty?)))
    :enable (type-option-flatten-let type-option-wfp))

  (defrule type-list-option-wfp-of-type-list-option-flatten-let
    (implies (type-list-option-wfp tys?)
             (type-list-option-wfp (type-list-option-flatten-let tys?)))
    :enable (type-list-option-flatten-let type-list-option-wfp))

  (defrule ispace-list-option-wfp-of-ispace-list-option-flatten-let
    (implies (ispace-list-option-wfp isps?)
             (ispace-list-option-wfp (ispace-list-option-flatten-let isps?)))
    :enable (ispace-list-option-flatten-let ispace-list-option-wfp))

  (defrule var+type?-wfp-of-var+type?-flatten-let
    (implies (var+type?-wfp vt)
             (var+type?-wfp (var+type?-flatten-let vt)))
    :enable (var+type?-flatten-let var+type?-wfp))

  (defrule var+type?-list-wfp-of-var+type?-list-flatten-let
    (implies (var+type?-list-wfp vts)
             (var+type?-list-wfp (var+type?-list-flatten-let vts)))
    :induct t
    :enable (var+type?-list-flatten-let var+type?-list-wfp))

  (defret-mutual exprs/atoms/binds-wfp-of-exprs/atoms/binds-flatten-let
    (defret expr-wfp-of-expr-flatten-let
      (implies (expr-wfp expr) (expr-wfp result))
      :fn expr-flatten-let)
    (defret expr-list-wfp-of-expr-list-flatten-let
      (implies (expr-list-wfp expr-list) (expr-list-wfp result))
      :fn expr-list-flatten-let)
    (defret atom-wfp-of-atom-flatten-let
      (implies (atom-wfp atom) (atom-wfp result))
      :fn atom-flatten-let)
    (defret atom-list-wfp-of-atom-list-flatten-let
      (implies (atom-list-wfp atom-list) (atom-list-wfp result))
      :fn atom-list-flatten-let)
    (defret bind-wfp-of-bind-flatten-let
      (implies (bind-wfp bind) (bind-wfp result))
      :fn bind-flatten-let)
    (defret bind-list-wfp-of-bind-list-flatten-let
      (implies (bind-list-wfp bind-list) (bind-list-wfp result))
      :fn bind-list-flatten-let)
    :mutual-recursion exprs/atoms/binds-flatten-let
    :hints (("Goal" :in-theory (enable expr-flatten-let
                                       expr-list-flatten-let
                                       atom-flatten-let
                                       atom-list-flatten-let
                                       bind-flatten-let
                                       bind-list-flatten-let
                                       expr-wfp expr-list-wfp
                                       atom-wfp atom-list-wfp
                                       bind-wfp bind-list-wfp
                                       var+type?-wfp
                                       consp-when-positive-len
                                       len-of-expr-list-flatten-let
                                       len-of-atom-list-flatten-let
                                       len-of-bind-list-flatten-let
                                       len-of-type-list-flatten-let
                                       len-of-ispace-list-flatten-let
                                       len-of-var+type?-list-flatten-let)))))

