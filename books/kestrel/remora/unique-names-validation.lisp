; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "uniquify-evaluation")

(include-book "portcullis")

; The tau system contributes to no proof in this book; running it on every
; goal is pure overhead here, so we turn it off.
(local (acl2::in-theory (acl2::disable (:e acl2::tau-system))))

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
     counterexamples recorded in the HISTORY comment below have been
     re-checked by execution against the closure evaluator and no longer
     apply.  The theorem is proved below from the top-level
     statement of its inductive core,
     @(tsee eval-top-expr-alpha-equiv-of-expr-uniquify-names) --- that the
     two evaluations err together and on success yield alpha-equivalent
     values --- which is in turn the top-level instance of the induction
     carried out in @(see uniquify-evaluation).")
   (xdoc::p
    "The mechanical proof is organized as follows.  @(see
     renaming-evaluation) provides the facts about the renamings of ispace
     and type variables that the rest builds on: the renaming images of
     sets of variables, the free-variable laws of renamed types, and the
     environment relations for the ispace layer.  The invariant of the
     induction is the
     alpha-relatedness of ASTs and of expression values modulo in-scope
     renamings, defined in @(see uniquify-alpha-relations) together with
     the freshness companion @(tsee expr-alpha-fresh-p) of the AST relation,
     which carries the no-capture conditions on the new binder names that
     the application cases of the induction need (see the witness-indexed
     value relation @(tsee expr-value-alpha-related-via-p)).  Its three
     consumers are: the bridge theorems, that the output of @(tsee
     expr-uniquify-names) is alpha-related to its input (see @('expr-alpha-related-p-of-expr-uniquify-names')) and satisfies the
     freshness conditions (see @(see uniquify-freshness) and @('expr-alpha-fresh-p-of-expr-uniquify-names')); the groundness collapse,
     proved in @(see uniquify-alpha-relations) on the groundness notions of
     @(see value-groundness) (see @('expr-value-alpha-related-via-p-when-groundp')): alpha-related values are
     literally equal when the original is ground, since ground values embed
     no abstract syntax and their type values are unmoved by the renamings;
     and the induction itself, in @(see uniquify-evaluation): a mutual induction
     over the @(see eval-exprs/atoms/binds) clique, with the dynamic
     environments of the two evaluations related entry by entry, modulo
     the in-scope renaming of their keys and via witnesses for their values
     (see @(tsee expr-denv-alpha-related-via-p)), one lemma per case of
     the evaluator, assembled into the flag theorem
     @('eval-expr-ok-holds').  The initial environments, in which both
     sides are evaluated, are related as the induction requires, with the
     empty witness (see @(tsee
     expr-denv-alpha-related-via-p-of-init-expr-denv)), and the names of
     the primitive operations (their keys) are the induction's support
     set.  The groundness collapse then discharges the groundness proviso
     of the main theorem: @(tsee eval-top-expr-of-expr-uniquify-names) is
     proved from the core by the collapse."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The main theorem, derived from its inductive core.
;
; The core below is the top-level instance of the induction of
; UNIQUIFY-EVALUATION --- the two evaluations err together and, on success,
; yield alpha-equivalent values, i.e. values related via SOME witness
; (EXPR-VALUE-ALPHA-EQUIV-P).  The main theorem follows from it by the
; groundness collapse (EXPR-VALUE-ALPHA-RELATED-VIA-P-WHEN-GROUNDP), which
; makes alpha-related values literally equal when the original is ground.
;
; The initial environments, in which EVAL-TOP-EXPR evaluates both sides,
; are related as the induction requires: at the bridge's renaming
; bundle (empty renamings; the avoid set is immaterial to the relation),
; with the empty witness, since the initial environment holds only the
; primitive operations, whose values the relation compares by equality.
; The relation on that constant map is settled by evaluation.

(defrule expr-denv-alpha-related-via-p-of-init-expr-denv
  :short "The initial environment is alpha-related to itself
          at the empty renamings, with the empty witness."
  (expr-denv-alpha-related-via-p
   (init-expr-denv)
   (init-expr-denv)
   (make-var-renamings :dim nil :shape nil :atom nil :array nil :expr nil
                       :avoid avoid)
   (make-denv-witness :types nil :exprs nil))
  :enable (expr-denv-alpha-related-via-p
           type-denv-alpha-related-via-p
           type-var-type-value-map-alpha-related-via-p
           denv-ispace-vars-covered-p
           init-expr-denv))

(defrule expr-denv-alpha-equiv-p-of-init-expr-denv
  :short "The initial environment is alpha-equivalent to itself
          at the empty renamings."
  (expr-denv-alpha-equiv-p
   (init-expr-denv)
   (init-expr-denv)
   (make-var-renamings :dim nil :shape nil :atom nil :array nil :expr nil
                       :avoid avoid))
  ;; The relation is re-established by the same evaluation as above rather
  ;; than by that rule, whose left-hand side the prover would first have
  ;; evaluated into a constant, past syntactic matching.
  :use ((:instance expr-denv-alpha-equiv-p-suff
                   (new-denv (init-expr-denv))
                   (denv (init-expr-denv))
                   (r (make-var-renamings :dim nil :shape nil
                                          :atom nil :array nil
                                          :expr nil :avoid avoid))
                   (dw (make-denv-witness :types nil :exprs nil))))
  :enable (expr-denv-alpha-related-via-p
           type-denv-alpha-related-via-p
           type-var-type-value-map-alpha-related-via-p
           denv-ispace-vars-covered-p
           init-expr-denv)
  :disable expr-denv-alpha-equiv-p-suff)

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
;     (expr-atom (make-atom-lambdan
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
; environment).  With static scoping the theorem holds, and is proved
; below.
;
; The theorems need no hypothesis on the free variables of the expression
; (which include the primitive operations it uses, bound by the initial
; environment, see INIT-EXPR-DENV): the failure-direction relation of the
; initial environment with itself, at the empty renamings, holds at any
; variable sets.

; The inductive core, at the top level: the main induction (see
; UNIQUIFY-EVALUATION) instantiated at the initial environments, the
; bridge's renaming bundle (empty renamings, avoiding all the variable
; names of the expression), the empty environment witness, and the names
; of the primitive operations as the support set (the keys of the initial
; environments).

(defruled support-invariant-p-of-primop-names
  (support-invariant-p (primop-names)
                       (set::union (expr-free-var-names expr) (primop-names))
                       avoid)
  :enable (support-invariant-p
           acl2::string-listp-when-string-setp
           str::string-list-fix-when-string-listp
           set::mergesort-set
           subset-of-union-right-1
           subset-of-union-right-2))

(defruled expr-denv-keys-supported-p-of-init-expr-denv
  (expr-denv-keys-supported-p
   (init-expr-denv)
   (make-var-renamings :dim nil :shape nil :atom nil :array nil :expr nil
                       :avoid avoid)
   (primop-names))
  :enable (expr-denv-keys-supported-p
           string-set-supported-p
           init-expr-denv))

(defruled string-expr-value-map-avoided-p-of-same-nil
  (string-expr-value-map-avoided-p map map nil vars)
  :enable (string-expr-value-map-avoided-p rename-var-string)
  :expand ((string-sfix vars)))

(defruled type-var-map-avoided-p-of-same-nil
  (type-var-map-avoided-p map map nil nil vars)
  :enable (type-var-map-avoided-p rename-type-var))

(defruled denv-ispace-vars-avoided-p-of-same-nil
  (denv-ispace-vars-avoided-p denv denv nil nil vars)
  :enable (denv-ispace-vars-avoided-p rename-ispace-var))

(defruled expr-denv-alpha-avoided-p-of-same-empty-renamings
  (expr-denv-alpha-avoided-p
   denv denv
   (make-var-renamings :dim nil :shape nil :atom nil :array nil :expr nil
                       :avoid avoid)
   ivars tvars evars)
  :enable (expr-denv-alpha-avoided-p
           type-denv-alpha-avoided-p
           string-expr-value-map-avoided-p-of-same-nil
           type-var-map-avoided-p-of-same-nil
           denv-ispace-vars-avoided-p-of-same-nil))

(defrule eval-top-expr-alpha-equiv-of-expr-uniquify-names
  :short "The inductive core at the top level:
          the two evaluations err together and,
          on success, yield alpha-equivalent values."
  (implies (and (exprp expr)
                (natp limit))
           (b* ((val (eval-top-expr expr limit))
                (uval (eval-top-expr (expr-uniquify-names expr) limit)))
             (and (equal (reserrp uval)
                         (reserrp val))
                  (implies (not (reserrp val))
                           (expr-value-alpha-equiv-p uval val)))))
  :enable (eval-top-expr)
  ;; The initial environment and the primop names are constants, which
  ;; the prover evaluates, so the facts about them are supplied as
  ;; instances rather than as rules (whose left-hand sides would not
  ;; match the evaluated constants).
  :use ((:instance eval-expr-ok-necc
                   (denv (init-expr-denv))
                   (new-expr (expr-uniquify-names expr))
                   (new-denv (init-expr-denv))
                   (r (make-var-renamings :dim nil :shape nil :atom nil
                                          :array nil :expr nil
                                          :avoid (expr-all-var-names expr)))
                   (dw (make-denv-witness :types nil :exprs nil))
                   (b (primop-names)))
        (:instance expr-alpha-fresh-p-of-expr-uniquify-names
                   (b (primop-names)))
        (:instance support-invariant-p-of-primop-names
                   (avoid (expr-all-var-names expr)))
        (:instance expr-denv-keys-supported-p-of-init-expr-denv
                   (avoid (expr-all-var-names expr)))
        (:instance expr-denv-alpha-related-via-p-of-init-expr-denv
                   (avoid (expr-all-var-names expr)))
        (:instance expr-denv-alpha-avoided-p-of-same-empty-renamings
                   (denv (init-expr-denv))
                   (avoid (expr-all-var-names expr))
                   (ivars (expr-free-ispace-vars expr))
                   (tvars (expr-free-type-vars expr))
                   (evars (expr-free-expr-vars expr)))))

; The main theorem: from the core, by the groundness collapse.  The
; witness of the core's existential is the one the collapse is applied
; to, and the fixes in the collapse's conclusion vanish because both
; results are values (neither being an error).

(defrule eval-top-expr-of-expr-uniquify-names
  :short "Uniquifying binder names preserves evaluation:
          the two evaluations err together, and on success
          yield equal values when the original value is ground."
  (implies (and (exprp expr)
                (natp limit))
           (b* ((val (eval-top-expr expr limit))
                (uval (eval-top-expr (expr-uniquify-names expr) limit)))
             (and (equal (reserrp uval)
                         (reserrp val))
                  (implies (and (not (reserrp val))
                                (expr-value-groundp val))
                           (equal uval val)))))
  :use (eval-top-expr-alpha-equiv-of-expr-uniquify-names
        (:instance expr-value-alpha-related-via-p-when-groundp
                   (new-val (eval-top-expr (expr-uniquify-names expr) limit))
                   (val (eval-top-expr expr limit))
                   (w (expr-value-alpha-equiv-p-witness
                       (eval-top-expr (expr-uniquify-names expr) limit)
                       (eval-top-expr expr limit)))))
  :enable (expr-value-alpha-equiv-p
           expr-valuep-when-result-not-error)
  :disable (eval-top-expr-alpha-equiv-of-expr-uniquify-names
            expr-value-alpha-related-via-p-when-groundp))
