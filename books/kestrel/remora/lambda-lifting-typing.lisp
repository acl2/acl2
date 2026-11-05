; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "lambda-lifting-validation")

(include-book "portcullis")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lambda-lifting-typing
  :parents (lambda-lifting-validation)
  :short "Typing facts for the validation of lambda lifting."
  :long
  (xdoc::topstring
   (xdoc::p
    "A lifted definition takes the variables its lambda captured as
     parameters typed by closed types (see @(tsee captured-params-closed-p)),
     and its binding is evaluated at the top, outside the binders of those
     variables.  The evaluation of a closed type does not depend on the
     environment, which is what lets the types be evaluated there."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The evaluation of a closed dimension, shape, ispace, or type is its
; evaluation in the empty environment.  The rules apply only to a
; non-constant environment, so that they do not rewrite their own right-hand
; sides.

(defthm-eval-dims-flag
  (defthm eval-dim-when-closed
    (implies (and (syntaxp (not (quotep denv)))
                  (set::emptyp (dim-free-ispace-vars dim)))
             (equal (eval-dim dim denv)
                    (eval-dim dim (ispace-denv nil))))
    :flag eval-dim)
  (defthm eval-dim-list-when-closed
    (implies (and (syntaxp (not (quotep denv)))
                  (set::emptyp (dim-list-free-ispace-vars dims)))
             (equal (eval-dim-list dims denv)
                    (eval-dim-list dims (ispace-denv nil))))
    :flag eval-dim-list)
  :hints (("Goal" :in-theory (enable eval-dim eval-dim-list
                                     dim-free-ispace-vars
                                     dim-list-free-ispace-vars))))

(defthm-eval-shapes/ispaces-flag
  (defthm eval-shape-when-closed
    (implies (and (syntaxp (not (quotep denv)))
                  (set::emptyp (shape-free-ispace-vars shape)))
             (equal (eval-shape shape denv)
                    (eval-shape shape (ispace-denv nil))))
    :flag eval-shape)
  (defthm eval-shape-list-when-closed
    (implies (and (syntaxp (not (quotep denv)))
                  (set::emptyp (shape-list-free-ispace-vars shapes)))
             (equal (eval-shape-list shapes denv)
                    (eval-shape-list shapes (ispace-denv nil))))
    :flag eval-shape-list)
  (defthm eval-ispace-when-closed
    (implies (and (syntaxp (not (quotep denv)))
                  (set::emptyp (ispace-free-ispace-vars ispace)))
             (equal (eval-ispace ispace denv)
                    (eval-ispace ispace (ispace-denv nil))))
    :flag eval-ispace)
  (defthm eval-ispace-list-when-closed
    (implies (and (syntaxp (not (quotep denv)))
                  (set::emptyp (ispace-list-free-ispace-vars ispaces)))
             (equal (eval-ispace-list ispaces denv)
                    (eval-ispace-list ispaces (ispace-denv nil))))
    :flag eval-ispace-list)
  :hints (("Goal" :in-theory (enable eval-shape eval-shape-list
                                     eval-ispace eval-ispace-list
                                     shape-free-ispace-vars
                                     shape-list-free-ispace-vars
                                     ispace-free-ispace-vars
                                     ispace-list-free-ispace-vars))))

(defthm-eval-types-flag
  (defthm eval-type-when-closed
    (implies (and (syntaxp (not (quotep denv)))
                  (set::emptyp (type-free-type-vars type))
                  (set::emptyp (type-free-ispace-vars type)))
             (equal (eval-type type denv)
                    (eval-type type (type-denv (ispace-denv nil) nil))))
    :flag eval-type)
  (defthm eval-type-list-when-closed
    (implies (and (syntaxp (not (quotep denv)))
                  (set::emptyp (type-list-free-type-vars types))
                  (set::emptyp (type-list-free-ispace-vars types)))
             (equal (eval-type-list types denv)
                    (eval-type-list types (type-denv (ispace-denv nil) nil))))
    :flag eval-type-list)
  :hints (("Goal" :in-theory (enable eval-type eval-type-list
                                     type-denv-restrict ispace-denv-restrict)
           :expand ((type-free-type-vars type)
                    (type-free-ispace-vars type)
                    (type-list-free-type-vars types)
                    (type-list-free-ispace-vars types)))))

(in-theory (disable eval-dim-when-closed
                    eval-dim-list-when-closed
                    eval-shape-when-closed
                    eval-shape-list-when-closed
                    eval-ispace-when-closed
                    eval-ispace-list-when-closed
                    eval-type-when-closed
                    eval-type-list-when-closed))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Constant dimensions are in normal form (see NORMALIZE-DIM): this is the
; first step towards the shapes of typed values, whose types have constant
; dimensions, being compared by ISPACE-EQUIVP as lists of numbers.

(defruled dim-poly-const-when-posp
  (implies (posp n)
           (equal (dim-poly-const n) (omap::update nil n nil)))
  :enable (dim-poly-const dim-poly-add-term))

(defrule normalize-dim-of-dim-const
  (implies (natp n)
           (equal (normalize-dim (dim-const n)) (dim-const n)))
  :cases ((posp n))
  :enable (normalize-dim poly-to-dim dim-to-poly poly-to-dim-parts
           poly-to-dim-term poly-to-dim-sum dim-poly-const-when-posp)
  :expand ((dim-to-poly (dim-const n))))

(defrule normalize-dim-list-of-dim-const-list
  (implies (nat-listp d)
           (equal (normalize-dim-list (dim-const-list d))
                  (dim-const-list d)))
  :induct (len d)
  :enable (normalize-dim-list dim-const-list len))

(defrule flatten-append-in-shape-list-of-singletons
  (equal (flatten-append-in-shape-list
          (shape-dims-list (list-to-singletons dims)) t)
         (shape-dims-list (list-to-singletons dims)))
  :induct (len dims)
  :enable (len list-to-singletons shape-dims-list
           flatten-append-in-shape-list flatten-append-in-shape))

; A constant shape normalizes to the concatenation of its single
; dimensions (see NORMALIZE-ISPACE), from which the dimensions are
; recovered: so constant shapes are equivalent exactly when their lists of
; dimensions are equal.

(defrule normalize-ispace-of-const-shape
  (implies (nat-listp d)
           (equal (normalize-ispace
                   (ispace-shape (shape-dims (dim-const-list d))))
                  (ispace-shape
                   (shape-append
                    (shape-dims-list (list-to-singletons (dim-const-list d)))))))
  :cases ((endp d) (endp (cdr d)))
  :enable (normalize-ispace normalize-dims-in-ispace normalize-dims-in-shape
           normalize-shapes-single-in-ispace normalize-shapes-single-in-shape
           flatten-append-in-ispace flatten-append-in-shape
           flatten-append-in-shape-list list-to-singletons shape-dims-list))

(local
 (defun cdr-cdr-induct-local (a b)
   (if (and (consp a) (consp b))
       (cdr-cdr-induct-local (cdr a) (cdr b))
     (list a b))))

(defrule singleton-shapes-injective
  (implies (and (nat-listp d1) (nat-listp d2))
           (equal (equal (shape-dims-list (list-to-singletons (dim-const-list d1)))
                         (shape-dims-list (list-to-singletons (dim-const-list d2))))
                  (equal d1 d2)))
  :induct (cdr-cdr-induct-local d1 d2)
  :enable (list-to-singletons shape-dims-list dim-const-list))

(defrule ispace-equivp-of-const-shapes
  (implies (and (nat-listp d1) (nat-listp d2))
           (equal (ispace-equivp (ispace-shape (shape-dims (dim-const-list d1)))
                                 (ispace-shape (shape-dims (dim-const-list d2))))
                  (equal d1 d2)))
  :enable ispace-equivp)

; The empty shape, as the constant the prover evaluates it to.

(defrule ispace-equivp-of-const-shape-and-empty
  (implies (nat-listp d)
           (equal (ispace-equivp (ispace-shape (shape-dims (dim-const-list d)))
                                 '(:shape (:dims nil)))
                  (not (consp d))))
  :use ((:instance ispace-equivp-of-const-shapes (d1 d) (d2 nil)))
  :disable ispace-equivp-of-const-shapes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Flat array types with constant shapes are equivalent only if their shapes
; are equal, and such a type is equivalent to an atom type only if its shape
; is empty.  (Equivalence unwraps a zero-rank array, so a nested array type
; may be equivalent to a flat one with a different outer shape: the types
; must be flat.)

(defrule dims-equal-when-type-equivp-of-flat-arrays
  (implies (and (nat-listp d1)
                (nat-listp d2)
                (member-equal (type-kind e1) '(:base :fun :forall :pi :sigma))
                (member-equal (type-kind e2) '(:base :fun :forall :pi :sigma))
                (type-equivp
                 (make-type-array :elem e1
                                  :ispace (ispace-shape
                                           (shape-dims (dim-const-list d1))))
                 (make-type-array :elem e2
                                  :ispace (ispace-shape
                                           (shape-dims (dim-const-list d2))))))
           (equal d1 d2))
  :rule-classes nil
  :cases ((consp d1))
  :enable (type-equivp normalize-type))

(defruled dims-nil-when-type-equivp-of-flat-array-and-atom
  (implies (and (nat-listp d1)
                (member-equal (type-kind e1) '(:base :fun :forall :pi :sigma))
                (member-equal (type-kind e2) '(:base :fun :forall :pi :sigma))
                (type-equivp
                 (make-type-array :elem e1
                                  :ispace (ispace-shape
                                           (shape-dims (dim-const-list d1))))
                 e2))
           (not (consp d1)))
  :enable (type-equivp normalize-type))

(defruled type-kind-of-type-value-to-type-when-not-array
  (implies (not (equal (type-value-kind tval) :array))
           (member-equal (type-kind (type-value-to-type tval))
                         '(:base :fun :forall :pi :sigma)))
  :expand ((type-value-to-type tval)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The type of a value (see EXPR-VALUE-TYPE) is a flat array type whose
; dimensions are the value's.

(define flat-types-dims-p ((tvals type-value-listp) (dimss nat-list-listp))
  :returns (yes/no booleanp)
  :short "Whether type values are flat array types
          with the given lists of dimensions."
  (if (consp tvals)
      (and (consp dimss)
           (type-value-case (car tvals) :array)
           (not (type-value-case (type-value-array->elem (car tvals)) :array))
           (equal (type-value-array->dims (car tvals)) (car dimss))
           (flat-types-dims-p (cdr tvals) (cdr dimss)))
    (not (consp dimss))))

(defthm-expr-value-types-flag
  (defthm expr-value-type-flat
    (implies (and (not (reserrp (expr-value-type val)))
                  (not (reserrp (check-dims-of-expr-value val))))
             (and (equal (type-value-kind (expr-value-type val)) :array)
                  (not (equal (type-value-kind
                               (type-value-array->elem (expr-value-type val)))
                              :array))
                  (equal (type-value-array->dims (expr-value-type val))
                         (check-dims-of-expr-value val))))
    :flag expr-value-type)
  (defthm expr-value-list-types-flat
    (implies (and (not (reserrp (expr-value-list-types vals)))
                  (not (reserrp (check-dims-of-expr-value-list vals))))
             (flat-types-dims-p (expr-value-list-types vals)
                                (check-dims-of-expr-value-list vals)))
    :flag expr-value-list-types)
  (defthm string-expr-value-map-types-flat
    t
    :rule-classes nil
    :flag string-expr-value-map-types)
  (defthm expr-denv-static-senvs-flat
    t
    :rule-classes nil
    :flag expr-denv-static-senvs)
  :hints (("Goal" :in-theory (enable expr-value-type
                                     expr-value-list-types
                                     check-dims-of-expr-value
                                     check-dims-of-expr-value-list
                                     scalar-type-value
                                     flat-types-dims-p))))

(define type-value-flat-p ((tval type-valuep))
  :returns (yes/no booleanp)
  :short "Whether a type value is flat:
          an atom type, or an array type of an atom type."
  (or (not (type-value-case tval :array))
      (not (type-value-case (type-value-array->elem tval) :array))))

; A well-formed value of a flat type has the dimensions of the type, so it
; passes the check that the application of a lambda makes of its argument
; (see EXPR-VALUES-MATCH-TYPE-VALUES-P): a captured variable, of a flat
; type, may be passed to the parameter it becomes.

(defruled dims-of-expr-value-when-typed
  (implies (and (expr-value-typed-p v tv)
                (expr-value-wfp v)
                (type-value-flat-p tv))
           (equal (dims-of-expr-value v)
                  (dims-of-type-value tv)))
  :enable (expr-value-typed-p dims-of-expr-value dims-of-type-value
           expr-value-wfp type-value-flat-p)
  :disable expr-value-type-flat
  :use ((:instance expr-value-type-flat (val v))
        (:instance type-kind-of-type-value-to-type-when-not-array
                   (tval (type-value-array->elem (expr-value-type v))))
        (:instance type-kind-of-type-value-to-type-when-not-array
                   (tval (type-value-array->elem tv)))
        (:instance type-kind-of-type-value-to-type-when-not-array
                   (tval tv))
        (:instance dims-equal-when-type-equivp-of-flat-arrays
                   (e1 (type-value-to-type
                        (type-value-array->elem (expr-value-type v))))
                   (d1 (check-dims-of-expr-value v))
                   (e2 (type-value-to-type (type-value-array->elem tv)))
                   (d2 (type-value-array->dims tv)))
        (:instance dims-nil-when-type-equivp-of-flat-array-and-atom
                   (e1 (type-value-to-type
                        (type-value-array->elem (expr-value-type v))))
                   (d1 (check-dims-of-expr-value v))
                   (e2 (type-value-to-type tv))))
  :expand ((type-value-to-type (expr-value-type v))
           (type-value-to-type tv)))

(defruled expr-values-match-type-values-p-when-typed
  (implies (and (expr-value-typed-p v tv)
                (expr-value-wfp v)
                (type-value-flat-p tv))
           (expr-values-match-type-values-p (list v) (list tv)))
  :enable (expr-values-match-type-values-p dims-of-type-value)
  :use dims-of-expr-value-when-typed)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A syntactically flat type (see TYPE-FLAT-SYNTAX-P), as a captured
; variable's must be, evaluates to a flat type value.

(defrule type-value-kind-of-nest-function-type-values-when-consp
  (implies (consp in)
           (equal (type-value-kind (nest-function-type-values in out)) :fun))
  :expand ((nest-function-type-values in out)))

(defrule consp-of-eval-type-list-when-consp
  (implies (and (consp types)
                (not (reserrp (eval-type-list types denv))))
           (consp (eval-type-list types denv)))
  :expand ((eval-type-list types denv)))

(defrule eval-type-not-array-when-evals-to-atom
  (implies (and (type-evals-to-atom-p type)
                (not (reserrp (eval-type type denv))))
           (not (equal (type-value-kind (eval-type type denv)) :array)))
  :enable type-evals-to-atom-p
  :expand ((eval-type type denv)))

(defrule type-value-flat-p-of-eval-type
  (implies (and (type-flat-syntax-p type)
                (not (reserrp (eval-type type denv))))
           (type-value-flat-p (eval-type type denv)))
  :induct (type-flat-syntax-p type)
  :enable (type-flat-syntax-p type-value-flat-p)
  :expand ((eval-type type denv)
           (eval-type-list nil denv)
           (:free (out) (nest-function-type-values nil out))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The definitions lifted out of an expression are bound at the top, and
; the evaluation of such a binding evaluates the type of the first
; parameter and the result type (see EVAL-BIND).  Lambda lifting makes
; sure those evaluate (see TYPE-EVALUABLE-P), whether or not the original
; program ever evaluates the lambda or binding a definition comes from, so
; that the binding of a lifted definition never fails.

(define bind-bindable-p ((b bindp))
  :returns (yes/no booleanp)
  :short "Whether a binding is a function binding with parameters
          whose first parameter's type and result type evaluate."
  (and (bind-case b :fun)
       (consp (bind-fun->params b))
       (param-evaluable-p (car (bind-fun->params b)))
       (type-option-evaluable-p (bind-fun->type? b))))

(define binds-bindable-p ((binds bind-listp))
  :returns (yes/no booleanp)
  :short "Whether every binding of a list is bindable."
  (or (endp binds)
      (and (bind-bindable-p (car binds))
           (binds-bindable-p (cdr binds))))
  ///
  (defrule binds-bindable-p-of-append
    (equal (binds-bindable-p (append a b))
           (and (binds-bindable-p a)
                (binds-bindable-p b)))
    :induct (len a)
    :enable len))

(defrule type-option-evaluable-p-of-type-option-fix
  (equal (type-option-evaluable-p (type-option-fix type?))
         (type-option-evaluable-p type?))
  :enable type-option-evaluable-p)

(defrule param-evaluable-p-of-var+type?-fix
  (equal (param-evaluable-p (var+type?-fix param))
         (param-evaluable-p param))
  :enable param-evaluable-p)

(defrule binds-bindable-p-of-emit-lifted-lambda
  (binds-bindable-p
   (mv-nth 1 (emit-lifted-lambda params body type? tenv locals used)))
  :enable (emit-lifted-lambda binds-bindable-p bind-bindable-p))

(defrule consp-of-names-to-params
  (equal (consp (names-to-params names tenv))
         (consp names))
  :expand ((names-to-params names tenv)))

(defrule param-evaluable-p-of-car-of-names-to-params
  (implies (and (captured-params-typed-p s tenv)
                (consp s))
           (param-evaluable-p (car (names-to-params s tenv))))
  :enable (captured-params-typed-p names-to-params param-evaluable-p
           set::head set::emptyp)
  :expand ((captured-params-typed-p s tenv)))

(defrule bind-bindable-p-of-hoist-local-fun
  (implies (mv-nth 0 (hoist-local-fun b rebound tenv locals used))
           (bind-bindable-p
            (mv-nth 2 (hoist-local-fun b rebound tenv locals used))))
  :enable (hoist-local-fun bind-bindable-p)
  :disable (set::intersect-under-set-equiv
            acl2::set-equiv-implies-equal-consp-1))

(defret-mutual binds-bindable-p-of-lambda-lift-exprs/atoms/binds
  (defret binds-bindable-p-of-ll-expr
    (binds-bindable-p lifted)
    :fn ll-expr)
  (defret binds-bindable-p-of-ll-lambda
    (binds-bindable-p lifted)
    :fn ll-lambda)
  (defret binds-bindable-p-of-ll-expr-list
    (binds-bindable-p lifted)
    :fn ll-expr-list)
  (defret binds-bindable-p-of-ll-atom
    (binds-bindable-p lifted)
    :fn ll-atom)
  (defret binds-bindable-p-of-ll-atom-list
    (binds-bindable-p lifted)
    :fn ll-atom-list)
  (defret binds-bindable-p-of-ll-bind
    (binds-bindable-p lifted)
    :fn ll-bind)
  (defret binds-bindable-p-of-ll-let-binds
    (binds-bindable-p lifted)
    :fn ll-let-binds)
  :mutual-recursion lambda-lift-exprs/atoms/binds
  :hints (("Goal"
           :in-theory (e/d (binds-bindable-p)
                           (emit-lifted-lambda hoist-local-fun))
           :expand ((ll-expr x tenv tlets locals lmap used)
                    (:free (type?)
                     (ll-lambda params body type? tenv tlets locals lmap used))
                    (ll-expr-list x tenv tlets locals lmap used)
                    (ll-atom x tenv tlets locals lmap used)
                    (ll-atom-list x tenv tlets locals lmap used)
                    (ll-bind x tenv tlets locals lmap used)
                    (ll-let-binds binds body-binders
                                  tenv tlets locals lmap used)))))

; A bindable binding closed in type and ispace variables, as the lifted
; definitions are (see LAMBDA-LIFTING-CLOSEDNESS), evaluates successfully
; in any environment: the types it evaluates are closed, so they evaluate
; there as in the empty environment.

(defrule eval-bind-not-error-when-bindable
  (implies (and (bind-bindable-p b)
                (set::emptyp (bind-free-type-vars b))
                (set::emptyp (bind-free-ispace-vars b))
                (not (zp limit)))
           (not (reserrp (eval-bind b denv limit))))
  :enable (bind-bindable-p param-evaluable-p type-option-evaluable-p
           type-evaluable-p eval-var+type? var+type?->type-or-err
           eval-type-when-closed)
  :expand ((eval-bind b denv limit)
           (bind-free-type-vars b)
           (bind-free-ispace-vars b)
           (var+type?-list-free-type-vars (bind-fun->params b))
           (var+type?-list-free-ispace-vars (bind-fun->params b))
           (var+type?-free-type-vars (car (bind-fun->params b)))
           (var+type?-free-ispace-vars (car (bind-fun->params b)))
           (type-option-free-type-vars (bind-fun->type? b))
           (type-option-free-ispace-vars (bind-fun->type? b))
           (type-option-free-type-vars
            (var+type?->type? (car (bind-fun->params b))))
           (type-option-free-ispace-vars
            (var+type?->type? (car (bind-fun->params b))))))
