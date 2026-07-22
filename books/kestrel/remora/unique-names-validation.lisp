; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "evaluation")
(include-book "renaming-evaluation")
(include-book "unique-names")

(include-book "kestrel/fty/deffold-reduce" :dir :system)

(include-book "portcullis")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unique-names-validation
  :parents (unique-names)
  :short "Semantic validation of bind-name uniquification."
  :long
  (xdoc::topstring
   (xdoc::p
    "Uniquifying the binder names (bind names and parameter names) of an
     expression does not change its meaning:
     evaluating the result of @(tsee expr-uniquify-names) succeeds or
     fails exactly when evaluating the original expression does (with the
     same evaluation limit), and on success the two values are equal
     whenever the original value is @('ground'), i.e. embeds no abstract
     syntax (see @(tsee expr-value-groundp)).  The groundness proviso is
     necessary: lambda values and universal/product/sum type values embed
     abstract syntax (the bodies of the abstractions), which uniquification
     may rename, so for expressions evaluating to such values the results
     agree only up to that renaming.")
   (xdoc::p
    "The informal argument is that uniquification is a capture-free alpha
     renaming: it changes only binder names (bind and parameter names) and,
     consistently, the
     occurrences in their scopes.  A binder that keeps its name contributes
     no change at all.  A renamed binder receives a name that avoids every
     variable name occurring anywhere in the expression (see the @('avoid')
     component of @(tsee var-renamings)) as well as all previously
     generated names, so the renaming applied to its scope can neither
     capture an occurrence bound elsewhere nor be captured by any binder.
     Evaluation depends on variable names only through the lookups in the
     dynamic environment, which the renaming affects consistently at
     binding sites and use sites; and since the renamed expression has
     exactly the same tree structure as the original, the evaluation
     recursion consumes the limit identically on both sides.")
   (xdoc::p
    "That argument presupposes static scoping, which the evaluator now
     provides: lambda values capture (the restriction to their free
     variables of) their creation environment, and applying a lambda
     evaluates the body in the captured environment.  Under the earlier,
     dynamically scoped evaluator the theorem below was falsified; the
     counterexamples recorded in the comment preceding the theorem have
     been re-checked by execution against the closure evaluator and no
     longer apply.  The theorem is now believed true; it remains under
     @(tsee acl2::skip-proofs) until its proof, outlined below, is
     completed.")
   (xdoc::p
    "The mechanical proof is in progress.  The structurally recursive
     levels of evaluation under renamings of the ispace and type variables
     --- dimensions, shapes, and ispaces, whose values contain no abstract
     syntax, as well as types, whose values are related modulo renaming
     because of the abstract syntax and captured environments embedded in
     universal/product/sum type values --- are done, along with the value
     side of all the renamings (including the renaming of the environments
     captured in lambda and type values) and its commutation with the
     evaluator's rank-polymorphic application machinery: see @(see
     renaming-evaluation).  This book proves that all
     the value renamings are the identity on ground values (see e.g.
     @(tsee expr-value-rename-expr-vars-when-groundp)), which will
     discharge the groundness proviso of the main theorem: the eventual
     induction yields results equal modulo renaming, which on ground
     values collapses to literal equality.  The remaining pieces are the
     relations between dynamic environments under the renamings reduced at
     binders, and the expression level itself, by mutual induction over
     the @(see eval-exprs/atoms/binds) clique with the dynamic
     environments of the two evaluations related modulo the in-scope
     renaming of their keys (and with expression values related modulo
     renaming, because of lambda values and their captured environments).
     Because of the @(tsee acl2::skip-proofs), this book is not included
     in @('top.lisp'), so that the rest of the library remains free of
     skipped proofs."))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Renaming is the identity on ground values.
;
; The renaming of a value renames just the abstract syntax embedded in it
; (see e.g. TYPE-VALUE-RENAME-ISPACE-VARS), and a ground value embeds none,
; so renaming a ground value gives back the value itself, for all five
; renamings (of ispace and type variables in type values, and of expression,
; ispace, and type variables in expression values).  These theorems will
; discharge the groundness proviso of the main theorem: the eventual
; induction over evaluation yields results equal modulo renaming, which on
; ground values collapses to literal equality.

(defret-mutual type-value-rename-ispace-vars-when-groundp
  (defret type-value-rename-ispace-vars-when-groundp
    (implies (type-value-groundp tval)
             (equal new-tval (type-value-fix tval)))
    :fn type-value-rename-ispace-vars)
  (defret type-value-list-rename-ispace-vars-when-groundp
    (implies (type-value-list-groundp tvals)
             (equal new-tvals (type-value-list-fix tvals)))
    :fn type-value-list-rename-ispace-vars)
  :mutual-recursion type-value-rename-ispace-vars
  ;; The map and environment members of the clique are skipped: they are
  ;; reached only through the type values of universal, product, and sum
  ;; types, which are never ground.
  :skip-others t
  :hints (("Goal" :in-theory (enable type-value-rename-ispace-vars
                                     type-value-list-rename-ispace-vars
                                     type-value-groundp
                                     type-value-list-groundp))))

(defret-mutual type-value-rename-type-vars-when-groundp
  (defret type-value-rename-type-vars-when-groundp
    (implies (type-value-groundp tval)
             (equal new-tval (type-value-fix tval)))
    :fn type-value-rename-type-vars)
  (defret type-value-list-rename-type-vars-when-groundp
    (implies (type-value-list-groundp tvals)
             (equal new-tvals (type-value-list-fix tvals)))
    :fn type-value-list-rename-type-vars)
  :mutual-recursion type-value-rename-type-vars
  ;; As above, the map and environment members are skipped.
  :skip-others t
  :hints (("Goal" :in-theory (enable type-value-rename-type-vars
                                     type-value-list-rename-type-vars
                                     type-value-groundp
                                     type-value-list-groundp))))

(defret-mutual expr-value-rename-expr-vars-when-groundp
  (defret expr-value-rename-expr-vars-when-groundp
    (implies (expr-value-groundp val)
             (equal new-val (expr-value-fix val)))
    :fn expr-value-rename-expr-vars)
  (defret expr-value-list-rename-expr-vars-when-groundp
    (implies (expr-value-list-groundp vals)
             (equal new-vals (expr-value-list-fix vals)))
    :fn expr-value-list-rename-expr-vars)
  :mutual-recursion expr-value-rename-expr-vars
  ;; As for the type values, the map and environment members of the clique
  ;; are skipped: they are reached only through lambda values, which are
  ;; never ground.
  :skip-others t
  :hints (("Goal" :in-theory (enable expr-value-rename-expr-vars
                                     expr-value-list-rename-expr-vars
                                     expr-value-groundp
                                     expr-value-list-groundp))))

(defret-mutual expr-value-rename-ispace-vars-when-groundp
  (defret expr-value-rename-ispace-vars-when-groundp
    (implies (expr-value-groundp val)
             (equal new-val (expr-value-fix val)))
    :fn expr-value-rename-ispace-vars)
  (defret expr-value-list-rename-ispace-vars-when-groundp
    (implies (expr-value-list-groundp vals)
             (equal new-vals (expr-value-list-fix vals)))
    :fn expr-value-list-rename-ispace-vars)
  :mutual-recursion expr-value-rename-ispace-vars
  ;; As for the type values, the map and environment members of the clique
  ;; are skipped: they are reached only through lambda values, which are
  ;; never ground.
  :skip-others t
  :hints (("Goal" :in-theory (enable expr-value-rename-ispace-vars
                                     expr-value-list-rename-ispace-vars
                                     expr-value-groundp
                                     expr-value-list-groundp))))

(defret-mutual expr-value-rename-type-vars-when-groundp
  (defret expr-value-rename-type-vars-when-groundp
    (implies (expr-value-groundp val)
             (equal new-val (expr-value-fix val)))
    :fn expr-value-rename-type-vars)
  (defret expr-value-list-rename-type-vars-when-groundp
    (implies (expr-value-list-groundp vals)
             (equal new-vals (expr-value-list-fix vals)))
    :fn expr-value-list-rename-type-vars)
  :mutual-recursion expr-value-rename-type-vars
  ;; As for the type values, the map and environment members of the clique
  ;; are skipped: they are reached only through lambda values, which are
  ;; never ground.
  :skip-others t
  :hints (("Goal" :in-theory (enable expr-value-rename-type-vars
                                     expr-value-list-rename-type-vars
                                     expr-value-groundp
                                     expr-value-list-groundp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The main theorem, as intended; its proof is deferred (see the xdoc above).
;
; HISTORY: under the earlier, dynamically scoped evaluator (lambda values
; captured no environment, and applying a lambda extended the environment
; in force at the call site), the theorem was FALSE, and this book recorded
; two counterexamples, checked by execution.  With the auxiliary constants
;
;   (defconst *int-type*  ; the scalar type int
;     (make-type-array :elem (make-type-base :type (base-type-int))
;                      :ispace (make-ispace-shape
;                               :shape (make-shape-dims :dims nil))))
;   (defconst *five*
;     (expr-atom (make-atom-base
;                 :lit (make-base-lit-int :lit (make-int-lit :digits '(#\5))))))
;   (defconst *zero*
;     (expr-atom (make-atom-base
;                 :lit (make-base-lit-int :lit (make-int-lit :digits '(#\0))))))
;   (defconst *lam*  ; (lambda ((x : int)) p)
;     (expr-atom (make-atom-lambda
;                 :params (list (make-var+type?
;                                :var "x"
;                                :type? (type-option-some *int-type*)))
;                 :body (expr-var "p")
;                 :type? (type-option-none))))
;
; the expression (in informal syntax)
;
;   (let ((f (lambda ((x : int)) p)))  ; p is free in the expression
;     (let ((p 5))
;       (f 0)))
;
; i.e.
;
;   (defconst *cex1*
;     (make-expr-let
;      :binds (list (make-bind-val :var "f" :type? (type-option-none)
;                                  :expr *lam*))
;      :body (make-expr-let
;             :binds (list (make-bind-val :var "p" :type? (type-option-none)
;                                         :expr *five*))
;             :body (make-expr-appn :fun (expr-var "f")
;                                   :args (list *zero*)))))
;
; evaluated to 5 --- (eval-top-expr *cex1* 1000) found the dynamically
; bound p --- while its uniquification evaluated to an error (the free
; variable p is in the initial set of used names, so the bind p is renamed
; to a fresh name, while the statically free occurrence p in the lambda
; body is correctly left alone), falsifying the first conjunct below; and
; the closed
;
;   (let ((p 1))
;     (let ((f (lambda ((x : int)) p)))
;       (let ((p 2))
;         (f 0))))
;
; evaluated to 2 (the body's p was dynamically captured by the inner bind)
; while its uniquification evaluated to 1, falsifying the second conjunct.
;
; The evaluator is now statically scoped: lambda values capture (the
; restriction to their free variables of) their creation environment, and
; application evaluates the body in the captured environment.  Both
; counterexamples were re-checked by execution (2026-07-09) against the
; closure evaluator, and neither applies any longer: in the first, both
; evaluations err (the free p is unbound in the captured environment); in
; the second, both evaluate to 1 (the p of the closure's creation
; environment).  So the theorem is now believed true.
;
; The no-free-variables hypotheses were added when the first counterexample
; falsified the unhypothesized statement; under static scoping they may
; well be unnecessary, but they are kept for now, since the statement below
; is assumed via SKIP-PROOFS and weaker assumptions are safer.  Note that
; they currently exclude expressions that use primitive operations, since
; primops occur as (free) variables bound by the initial environment (see
; INIT-EXPR-DENV); weakening the hypotheses to allow exactly the primop
; names is future work, together with the proof itself (see the xdoc
; above), after which the SKIP-PROOFS is to be discharged.

;; (acl2::skip-proofs
;;  (defthm eval-top-expr-of-expr-uniquify-names
;;    (implies (and (exprp expr)
;;                  (natp limit)
;;                  (set::emptyp (expr-free-expr-vars expr))
;;                  (set::emptyp (expr-free-ispace-vars expr))
;;                  (set::emptyp (expr-free-type-vars expr)))
;;             (b* ((val (eval-top-expr expr limit))
;;                  (uval (eval-top-expr (expr-uniquify-names expr) limit)))
;;               (and (equal (reserrp uval)
;;                           (reserrp val))
;;                    (implies (and (not (reserrp val))
;;                                  (expr-value-groundp val))
;;                             (equal uval val)))))))
