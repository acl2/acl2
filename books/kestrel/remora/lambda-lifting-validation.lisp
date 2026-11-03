; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "lambda-lifting")
(include-book "evaluation")
(include-book "validator")
(include-book "values-to-abstract-syntax")
(include-book "value-groundness")

(include-book "portcullis")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lambda-lifting-validation
  :parents (lambda-lifting)
  :short "Semantic validation of lambda lifting: the statement."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lambda lifting should not change the meaning of a program:
     if evaluating a well-typed expression succeeds with a ground value
     (see @(tsee expr-value-groundp)),
     evaluating its lambda-lifted form, with a large enough limit,
     succeeds with the same value.
     This book states that property;
     its proof is not done yet.")
   (xdoc::p
    "Unlike uniquification (see @(see unique-names-validation)),
     lambda lifting depends on types at run time.
     A variable captured by a lifted lambda becomes a parameter
     of the lifted definition, typed as the type environment of the
     transformation types it (see @(tsee names-to-params)),
     and the lifted program passes the variable to that parameter:
     the application checks the shape of the value against the type,
     and splits off a frame if the value has more dimensions.
     So the lifted program behaves like the original only if
     the captured values have the shapes of their static types.
     That is a consequence of the soundness of the type checker,
     which is not proved;
     so it is a hypothesis of the theorem,
     as the soundness of the checker with respect to evaluation
     (@(tsee check-sound-p)).")
   (xdoc::p
    "Soundness must be about all values, not just shapes:
     whether a value bound by a @('let') has the shape of its inferred type
     depends on the behavior of the functions used to compute it,
     which may be values of parameters.
     So the hypothesis relates the checker to the evaluator through
     a typing of values (@(tsee expr-value-type)):
     data values are typed structurally,
     and closures by checking their bodies,
     with the types of the values they capture.")
   (xdoc::p
    "Only one direction is claimed.
     The lifted program may succeed where the original fails:
     e.g. a lifted definition carries its result type,
     where an unannotated original lambda does not.
     And the lifted program needs a larger limit:
     a captured variable is passed to the lifted definition
     by an application, which consumes some of the limit.
     By the monotonicity of evaluation in the limit
     (see @(tsee eval-top-expr-when-larger-limit)),
     a limit that suffices may be increased at will."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Typing of values.
;
; The type of an expression value is the type an expression evaluating to it
; has: always an array type, whose shape is the dimensions of the value, and
; whose element type is an atom type (not itself an array type: the types
; are flat).  A value of an atom type, such as a closure, is a zero-rank
; array of it.
;
; Closures are typed by checking their bodies, in static environments built
; from the environments they capture: their ispace and type variables are
; given as definitions (their values, as an ispace and a type), and their
; expression variables the types of their values.  Primitive operation
; values are typed by reading them back as expressions (see
; PRIMOP-VALUE-TO-EXPR) and checking those; a stage of an operation that
; holds a value with no literal syntax (see FLOAT-VALUE-TO-FLOAT-LIT) cannot
; be read back, and is typed by its function type (see
; TYPE-OF-PRIMOP-VALUE-FUN), when it is applicable to values.

(define base-value-base-type ((val base-valuep))
  :returns (type base-typep)
  :short "The base type of a base value."
  (base-value-case val
                   :bool (base-type-bool)
                   :int (base-type-int)
                   :float (base-type-float)))

(define scalar-type-value ((tval type-valuep))
  :returns (tval type-valuep)
  :short "The zero-rank array type value of an atom type value."
  (make-type-value-array :elem tval :dims nil))

(define primop-value-type ((pval primop-valuep))
  :returns (tval type-value-resultp)
  :short "The type of a primitive operation value."
  (b* (((mv err expr) (primop-value-to-expr pval))
       ((when err)
        (if (primop-value-funp pval)
            (type-of-primop-value-fun pval)
          (reserr (list :primop-value-untyped (primop-value-fix pval)))))
       ((ok type+expr) (check-expr expr
                                   (init-ispace-senv)
                                   (init-type-senv)
                                   (init-expr-senv))))
    (eval-type (type+expr->type type+expr)
               (expr-denv->tenv (init-expr-denv))))
  :guard-hints (("Goal" :in-theory (enable type+expr-p-when-result-not-error))))

(define ispace-value-map-to-defs ((map ispace-var-ispace-value-mapp))
  :returns (defs ispace-var-ispace-option-mapp)
  :short "The ispace definitions of the ispace variables
          of a captured environment."
  (b* (((when (omap::emptyp (ispace-var-ispace-value-map-fix map))) nil))
    (omap::update (omap::head-key (ispace-var-ispace-value-map-fix map))
                  (ispace-option-some
                   (ispace-value-to-ispace
                    (omap::head-val (ispace-var-ispace-value-map-fix map))))
                  (ispace-value-map-to-defs
                   (omap::tail (ispace-var-ispace-value-map-fix map)))))
  :measure (acl2-count (ispace-var-ispace-value-map-fix map))
  :verify-guards nil)

(define type-value-map-to-defs ((map type-var-type-value-mapp))
  :returns (defs type-var-type-option-mapp)
  :short "The type definitions of the type variables
          of a captured environment."
  (b* (((when (omap::emptyp (type-var-type-value-map-fix map))) nil))
    (omap::update (omap::head-key (type-var-type-value-map-fix map))
                  (type-option-some
                   (type-value-to-type
                    (omap::head-val (type-var-type-value-map-fix map))))
                  (type-value-map-to-defs
                   (omap::tail (type-var-type-value-map-fix map)))))
  :measure (acl2-count (type-var-type-value-map-fix map))
  :verify-guards nil)

; Whether every type value in a list is equivalent to a given one.

(define type-value-list-all-equivp ((tvals type-value-listp)
                                    (tval type-valuep))
  :returns (yes/no booleanp)
  :short "Whether every type value in a list is equivalent to a given one."
  (or (endp tvals)
      (and (type-equivp (type-value-to-type (car tvals))
                        (type-value-to-type tval))
           (type-value-list-all-equivp (cdr tvals) tval))))

(defines expr-value-types
  :short "Types of expression values."
  :verify-guards nil
  :flag-local nil
  :returns-hints (("Goal" :in-theory (enable type-valuep-when-result-not-error
                                             type-value-listp-when-result-not-error
                                             string-type-mapp-when-result-not-error)))

  (define expr-value-type ((val expr-valuep))
    :returns (tval type-value-resultp)
    :short "The type of an expression value."
    :long
    (xdoc::topstring
     (xdoc::p
      "A box has the sum type it carries,
       provided its array has the type
       the body of that type gives it at the boxed ispace.")
     (xdoc::p
      "The elements of a non-empty vector must have equivalent types;
       the vector's type is the first element's,
       with the number of elements as an outer dimension."))
    (expr-value-case
     val
     :base (scalar-type-value
            (type-value-base (base-value-base-type val.val)))
     :primop (b* (((ok tval) (primop-value-type val.val)))
               (type-value-case
                tval
                :array (if (and (endp tval.dims)
                                (not (type-value-case tval.elem :array)))
                           tval
                         (reserr (list :primop-value-not-scalar
                                       (expr-value-fix val))))
                :otherwise (scalar-type-value tval)))
     :lambda (b* (((ok senvs) (expr-denv-static-senvs val.denv))
                  ((senvs+binds senvs) senvs)
                  (ptype (var+typevalue->type val.param))
                  (eenv (expr-senv
                         (omap::update (var+typevalue->var val.param)
                                       (type-value-to-type ptype)
                                       (expr-senv->exprs senvs.eenv))))
                  ((ok type+expr)
                   (check-expr val.body senvs.ienv senvs.tenv eenv))
                  ((ok out) (eval-type (type+expr->type type+expr)
                                       (expr-denv->tenv val.denv))))
               (scalar-type-value (make-type-value-fun :in ptype :out out)))
     :tlambda (b* (((ok senvs) (expr-denv-static-senvs val.denv))
                   ((senvs+binds senvs) senvs)
                   (tenv (type-senv-add-var val.param senvs.tenv))
                   ((ok type+expr)
                    (check-expr val.body senvs.ienv tenv senvs.eenv)))
                (scalar-type-value
                 (make-type-value-forall :param val.param
                                         :body (type+expr->type type+expr)
                                         :denv (expr-denv->tenv val.denv))))
     :ilambda (b* (((ok senvs) (expr-denv-static-senvs val.denv))
                   ((senvs+binds senvs) senvs)
                   (ienv (ispace-senv-add-var val.param senvs.ienv))
                   ((ok type+expr)
                    (check-expr val.body ienv senvs.tenv senvs.eenv)))
                (scalar-type-value
                 (make-type-value-pi :param val.param
                                     :body (type+expr->type type+expr)
                                     :denv (expr-denv->tenv val.denv))))
     :box (b* (((unless (type-value-case val.type :sigma))
                (reserr (list :box-type-not-sigma (expr-value-fix val))))
               ((type-value-sigma sum) val.type)
               ((unless (ispace-values-match-ispace-vars-p
                         (list val.ispace) (list sum.param)))
                (reserr (list :box-ispace-mismatch (expr-value-fix val))))
               ((ok inner) (eval-type sum.body
                                      (type-denv-add-ispace sum.param
                                                            val.ispace
                                                            sum.denv)))
               ((ok array-type) (expr-value-type val.array))
               ((unless (type-equivp (type-value-to-type array-type)
                                     (type-value-to-type inner)))
                (reserr (list :box-array-mismatch (expr-value-fix val)))))
            (scalar-type-value val.type))
     :vector (b* (((ok tvals) (expr-value-list-types val.elems))
                  ((unless (consp tvals))
                   (reserr (list :vector-empty (expr-value-fix val))))
                  (first (car tvals))
                  ((unless (type-value-list-all-equivp (cdr tvals) first))
                   (reserr (list :vector-mixed (expr-value-fix val)))))
               (type-value-case
                first
                :array (make-type-value-array
                        :elem first.elem
                        :dims (cons (len val.elems) first.dims))
                :otherwise (make-type-value-array
                            :elem first
                            :dims (list (len val.elems)))))
     :vector-empty (if (type-value-case val.elem :array)
                       (reserr (list :vector-empty-array-elem
                                     (expr-value-fix val)))
                     (make-type-value-array :elem val.elem
                                            :dims (cons 0 val.dims))))
    :measure (expr-value-count val))

  (define expr-value-list-types ((vals expr-value-listp))
    :returns (tvals type-value-list-resultp)
    :short "The types of a list of expression values."
    (b* (((when (endp vals)) nil)
         ((ok tval) (expr-value-type (car vals)))
         ((ok tvals) (expr-value-list-types (cdr vals))))
      (cons tval tvals))
    :measure (expr-value-list-count vals))

  (define string-expr-value-map-types ((map string-expr-value-mapp))
    :returns (types string-type-map-resultp)
    :short "The types of the values of a map from strings to expression values,
            as types."
    (b* (((when (omap::emptyp (string-expr-value-map-fix map))) nil)
         ((ok tval) (expr-value-type (omap::head-val map)))
         ((ok types) (string-expr-value-map-types (omap::tail map))))
      (omap::update (str-fix (omap::head-key map))
                    (type-value-to-type tval)
                    types))
    :measure (string-expr-value-map-count map))

  (define expr-denv-static-senvs ((denv expr-denvp))
    :returns (senvs senvs+binds-resultp)
    :short "The static environments in which the body of a closure
            that captures a dynamic environment is checked."
    :long
    (xdoc::topstring
     (xdoc::p
      "The ispace and type variables are given as definitions,
       and the expression variables the types of their values,
       over the primitive operations.
       The bindings component is unused."))
    (b* ((tdenv (expr-denv->tenv denv))
         ((ok types) (string-expr-value-map-types (expr-denv->exprs denv))))
      (make-senvs+binds
       :ienv (ispace-senv (ispace-value-map-to-defs
                           (ispace-denv->ispaces (type-denv->ienv tdenv))))
       :tenv (type-senv (type-value-map-to-defs (type-denv->types tdenv)))
       :eenv (expr-senv (omap::update* types (primop-types)))
       :binds nil))
    :measure (expr-denv-count denv)))

(define expr-value-typed-p ((val expr-valuep) (tval type-valuep))
  :returns (yes/no booleanp)
  :short "Whether an expression value has a type value."
  :long
  (xdoc::topstring
   (xdoc::p
    "Its type (see @(tsee expr-value-type)) must be equivalent to the type
     value, as types (see @(tsee type-value-to-type))."))
  (b* ((vtype (expr-value-type val)))
    (and (not (reserrp vtype))
         (type-equivp (type-value-to-type vtype)
                      (type-value-to-type tval))))
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Typing of dynamic environments by static ones: every variable of the
; static environments is bound in the dynamic one, to a value of its sort,
; kind, or type, which is the value of its definition if it has one.

(define ispace-denv-typed-p ((defs ispace-var-ispace-option-mapp)
                             (ienv ispace-denvp))
  :returns (yes/no booleanp)
  :short "Whether an ispace dynamic environment has the ispace variables
          of an ispace static environment."
  (b* ((defs (ispace-var-ispace-option-map-fix defs))
       ((when (omap::emptyp defs)) t)
       (var (omap::head-key defs))
       (def? (omap::head-val defs))
       (pair (omap::assoc var (ispace-denv->ispaces ienv))))
    (and (consp pair)
         (ispace-values-match-ispace-vars-p (list (cdr pair)) (list var))
         (ispace-option-case def?
                             :none t
                             :some (equal (eval-ispace def?.val ienv)
                                          (cdr pair)))
         (ispace-denv-typed-p (omap::tail defs) ienv)))
  :measure (acl2-count (ispace-var-ispace-option-map-fix defs))
  :verify-guards nil)

(define type-denv-typed-p ((defs type-var-type-option-mapp)
                           (tdenv type-denvp))
  :returns (yes/no booleanp)
  :short "Whether a type dynamic environment has the type variables
          of a type static environment."
  (b* ((defs (type-var-type-option-map-fix defs))
       ((when (omap::emptyp defs)) t)
       (var (omap::head-key defs))
       (def? (omap::head-val defs))
       (pair (omap::assoc var (type-denv->types tdenv))))
    (and (consp pair)
         (type-values-match-type-vars-p (list (cdr pair)) (list var))
         (type-option-case def?
                           :none t
                           :some (equal (eval-type def?.val tdenv)
                                        (cdr pair)))
         (type-denv-typed-p (omap::tail defs) tdenv)))
  :measure (acl2-count (type-var-type-option-map-fix defs))
  :verify-guards nil)

(define expr-vars-typed-p ((types string-type-mapp) (denv expr-denvp))
  :returns (yes/no booleanp)
  :short "Whether an expression dynamic environment binds the variables
          of a map to values of their types."
  (b* ((types (string-type-map-fix types))
       ((when (omap::emptyp types)) t)
       (val (expr-denv-lookup-expr (omap::head-key types) denv))
       (tval (eval-type (omap::head-val types) (expr-denv->tenv denv))))
    (and (not (reserrp val))
         (not (reserrp tval))
         (expr-value-typed-p val tval)
         (expr-vars-typed-p (omap::tail types) denv)))
  :measure (acl2-count (string-type-map-fix types))
  :verify-guards nil)

(define expr-denv-typed-p ((denv expr-denvp)
                           (ienv ispace-senvp)
                           (tenv type-senvp)
                           (eenv expr-senvp))
  :returns (yes/no booleanp)
  :short "Whether an expression dynamic environment is typed by
          static environments."
  (b* ((tdenv (expr-denv->tenv denv)))
    (and (ispace-denv-typed-p (ispace-senv->ispaces ienv)
                              (type-denv->ienv tdenv))
         (type-denv-typed-p (type-senv->types tenv) tdenv)
         (expr-vars-typed-p (expr-senv->exprs eenv) denv)))
  :verify-guards nil)

; The initial dynamic environment, of the primitive operations, is typed by
; the initial static environments: so the evaluation of a checked expression
; starts typed.  This is a fact about constants, settled by evaluation.

(defrule expr-denv-typed-p-of-init
  (expr-denv-typed-p (init-expr-denv)
                     (init-ispace-senv)
                     (init-type-senv)
                     (init-expr-senv))
  :hints (("Goal" :in-theory (enable (:e expr-denv-typed-p)
                                     (:e init-expr-denv)
                                     (:e init-ispace-senv)
                                     (:e init-type-senv)
                                     (:e init-expr-senv)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection check-sound-p
  :short "The soundness of the type checker with respect to evaluation,
          the hypothesis of the validation of lambda lifting."
  :long
  (xdoc::topstring
   (xdoc::p
    "In dynamic environments typed by the static ones,
     a checked expression evaluates, if successfully,
     to a value of the type the checker gives it
     (evaluated in the dynamic environment),
     and checked bindings evaluate, if successfully,
     to an environment typed by the static environments
     the checker extends the given ones to.")
   (xdoc::p
    "It is the expression as given that is evaluated,
     not the one the checker returns,
     which may be augmented with type information
     (e.g. inferred type applications, and result types of lambdas).
     That is a stronger claim,
     since the given expression may lack that information;
     but where it does, its evaluation fails rather than
     succeeding differently (applying a type lambda to a term fails,
     as does applying an unannotated lambda over an empty frame)."))

  (defun-sk check-sound-p ()
    (forall (expr binds ienv tenv eenv denv limit)
            (and (b* ((type+expr (check-expr expr ienv tenv eenv))
                      (val (eval-expr expr denv limit)))
                   (implies (and (expr-denv-typed-p denv ienv tenv eenv)
                                 (not (reserrp type+expr))
                                 (not (reserrp val)))
                            (b* ((tval (eval-type (type+expr->type type+expr)
                                                  (expr-denv->tenv denv))))
                              (and (not (reserrp tval))
                                   (expr-value-typed-p val tval)))))
                 (b* ((senvs (check-bind-list binds ienv tenv eenv))
                      (new-denv (eval-bind-list binds denv limit)))
                   (implies (and (expr-denv-typed-p denv ienv tenv eenv)
                                 (not (reserrp senvs))
                                 (not (reserrp new-denv)))
                            (expr-denv-typed-p new-denv
                                               (senvs+binds->ienv senvs)
                                               (senvs+binds->tenv senvs)
                                               (senvs+binds->eenv senvs))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection lambda-lift-top-expr-eval-ok-p
  :short "That the lambda-lifted form of an expression evaluates,
          with some limit, to the value of the expression at a given limit."
  (defun-sk lambda-lift-top-expr-eval-ok-p (expr limit)
    (exists (limit2)
            (and (natp limit2)
                 (equal (eval-top-expr (lambda-lift-top-expr expr) limit2)
                        (eval-top-expr expr limit))))))

(define lambda-lift-validation-claim-p ((expr exprp) (limit natp))
  :returns (yes/no booleanp)
  :short "The validation of lambda lifting, at an expression and a limit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the statement of the theorem still to be proved:
     that this holds for every @('expr') and @('limit').
     Under the soundness of the type checker (@(tsee check-sound-p)),
     if a type-checked expression whose binders bind distinct names
     evaluates, with some limit, to a ground value,
     its lambda-lifted form evaluates, with some limit,
     to the same value.")
   (xdoc::p
    "The binders must bind distinct names, as the guard of
     @(tsee lambda-lift-top-expr) requires:
     the transformation respects shadowing,
     but the proof may assume uniqueness.
     The expression must type-check, so that its evaluation is typed,
     by @(tsee check-sound-p),
     starting from the typing of the initial dynamic environment
     by the initial static ones (@('expr-denv-typed-p-of-init'))."))
  (implies (and (check-sound-p)
                (not (expr-duplicate-names expr))
                (not (reserrp (check-top-expr expr)))
                (not (reserrp (eval-top-expr expr limit)))
                (expr-value-groundp (eval-top-expr expr limit)))
           (lambda-lift-top-expr-eval-ok-p expr limit))
  :verify-guards nil)
