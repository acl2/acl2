; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "lambda-lifting-simulation")
(include-book "lambda-lifting-closedness")
(include-book "lambda-lifting-validation")

(include-book "portcullis")

(local (include-book "std/strings/decimal" :dir :system))
(local (include-book "omaps"))
(local (include-book "std/omaps/extensionality" :dir :system))
(local (include-book "osets"))
(local (include-book "free-variables-in-all-variables"))
;; Rules that profiling showed useless here and costly.
(local
 (in-theory
  (disable no-duplicatesp-equal-when-no-duplicatesp-equal-of-type-var-list->name
           no-duplicatesp-equal-when-no-duplicatesp-equal-of-ispace-var-list->name
           no-duplicatesp-equal-when-not-duplicated-names
           duplicated-names-when-no-duplicatesp-equal
           member-equal-of-type-var-list->name-when-member-equal
           member-equal-of-ispace-var-list->name-when-member-equal
           member-of-type-var->name-in-type-var-list->name
           member-of-ispace-var->name-in-ispace-var-list->name
           acl2::consp-when-member-equal-of-cons-listp
           acl2::subsetp-car-member
           consp-of-type-var-list->name
           consp-of-ispace-var-list->name
           cdr-of-type-var-list->name
           cdr-of-ispace-var-list->name
           type-var-list->name-when-not-consp
           ispace-var-list->name-when-not-consp
           omap::restrict-when-left-emptyp
           acl2::subsetp-member
           acl2::member-when-atom)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lambda-lifting-validation-proof
  :parents (lambda-lifting-validation)
  :short "The proof of the validation of lambda lifting."
  :long
  (xdoc::topstring
   (xdoc::p
    "This book proves @('lambda-lift-validation-claim'): for every
     expression and limit, @(tsee lambda-lift-validation-claim-p) holds.
     Under the soundness of the type checker, a type-checked expression
     whose binders bind distinct names, and which evaluates to a ground
     value, has a lambda-lifted form that evaluates, at a larger limit, to
     the same value.")
   (xdoc::p
    "The lifted program binds the lifted definitions at the top, one per
     nested @(':let') (see @(tsee nest-let-binds)), and evaluates the
     rebuilt expression in the environment they make (@('ll-top-env')).
     The simulation (see @(see lambda-lifting-simulation)) relates the
     evaluations of the original and rebuilt expressions in related
     environments, given the invariants of the traversal (@(tsee
     ll-context-ok-p)); its induction theorem is @('eval-expr-ll-ok-holds').
     What remains is to establish its hypotheses at the top, and to
     account for the bindings.")
   (xdoc::p
    "The lifted definitions are functions with parameters whose first
     parameter's type and result type evaluate, under fresh names in
     sequence (@('lifted-defs-ok-of-ll-expr')), so their names are
     distinct, none is a name in use at the start, and none is the name of
     a primitive operation (fresh names end in a digit, and no primitive's
     name does).  So binding them evaluates nothing and fails nowhere
     (@('eval-bind-when-ll-def-ok')).  By the placement theorem, each
     refers only to the definitions before it and to what is free in the
     input (@('no-forward-refs-p-when-placed')), so the closure that
     evaluating it gives is the same in the environment where it is bound
     and in the top one: the top environment is the fixed point that
     @(tsee ll-defs-bound-p) requires (@('ll-defs-bound-p-of-ll-top-env')).
     It also binds the primitive operations as the initial environment
     does, which with the empty context makes the environments related
     (@('expr-denv-ll-related-p-at-top')) and the invariants hold
     (@('ll-context-ok-p-at-top')).")
   (xdoc::p
    "The simulation then gives a limit at which the rebuilt expression
     evaluates, in the top environment, to a value related to the
     original's, which, being ground, is equal to it
     (@('equal-when-expr-value-ll-related-p-groundp')).  Each binding of a
     definition costs one unit of limit (@('eval-expr-of-nest-let-binds'))."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Lifted definitions are named apart from the primitive operations: fresh
; names end in a digit, and no name in the initial environment does.

(define ends-in-digit-p ((s stringp))
  :returns (yes/no booleanp)
  (b* ((cs (str::explode s)))
    (and (consp cs)
         (str::dec-digit-char-p (car (last cs))))))

(defruled dec-digit-char-p-of-car-last
  (implies (and (str::dec-digit-char-list*p cs) (consp cs))
           (str::dec-digit-char-p (car (last cs))))
  :induct (len cs)
  :enable (str::dec-digit-char-list*p last))

(defrule ends-in-digit-p-of-expr-var-with-index
  (ends-in-digit-p (expr-var-with-index prefix index))
  :enable (ends-in-digit-p expr-var-with-index)
  :use ((:instance dec-digit-char-p-of-car-last
                   (cs (str::explode (str::nat-to-dec-string (nfix index)))))
        (:instance car-last-of-append-consp
                   (a (str::explode (str::str-fix prefix)))
                   (b (str::explode (str::nat-to-dec-string (nfix index)))))))
(defrule ends-in-digit-p-of-fresh-expr-var-loop
  (ends-in-digit-p (fresh-expr-var-loop prefix index used))
  :induct (fresh-expr-var-loop prefix index used)
  :enable fresh-expr-var-loop)

(defrule ends-in-digit-p-of-fresh-expr-var
  (ends-in-digit-p (fresh-expr-var prefix used))
  :enable fresh-expr-var)

(define none-ends-in-digit-p ((names string-listp))
  :returns (yes/no booleanp)
  (or (endp names)
      (and (not (ends-in-digit-p (car names)))
           (none-ends-in-digit-p (cdr names)))))

(defruled not-member-when-none-ends-in-digit-p
  (implies (and (none-ends-in-digit-p names)
                (ends-in-digit-p s))
           (not (member-equal s names)))
  :induct (len names)
  :enable none-ends-in-digit-p)

(defruled none-ends-in-digit-p-of-init-names
  (none-ends-in-digit-p (omap::keys (expr-denv->exprs (init-expr-denv)))))

(defrule not-assoc-init-when-ends-in-digit-p
  (implies (ends-in-digit-p s)
           (not (omap::assoc s (expr-denv->exprs (init-expr-denv)))))
  :use (none-ends-in-digit-p-of-init-names
        (:instance not-member-when-none-ends-in-digit-p
                   (names (omap::keys (expr-denv->exprs (init-expr-denv)))))
        (:instance omap::in-of-keys-to-assoc
                   (key s) (map (expr-denv->exprs (init-expr-denv)))))
  :enable (set::in-to-member)
  :disable ((:e init-expr-denv)))
; The definitions lifted out of an expression are bound at the top, where
; each is evaluated: each is a function with parameters, whose first
; parameter and result type evaluate, under a fresh name (ending in a digit).

(define ll-def-ok-p ((b bindp))
  :returns (yes/no booleanp)
  (and (bind-case b :fun)
       (consp (bind-fun->params b))
       (param-evaluable-p (car (bind-fun->params b)))
       (type-option-evaluable-p (bind-fun->type? b))
       (ends-in-digit-p (bind-fun->var b))))

(define ll-defs-ok-p ((defs bind-listp))
  :returns (yes/no booleanp)
  (or (endp defs)
      (and (ll-def-ok-p (car defs))
           (ll-defs-ok-p (cdr defs)))))

(defrule ll-defs-ok-p-of-append
  (equal (ll-defs-ok-p (append a b))
         (and (ll-defs-ok-p a) (ll-defs-ok-p b)))
  :induct (len a)
  :enable ll-defs-ok-p)

(defrule ll-defs-ok-p-of-cons
  (equal (ll-defs-ok-p (cons a b))
         (and (ll-def-ok-p a) (ll-defs-ok-p b)))
  :enable ll-defs-ok-p)

(defrule bind-list-names-of-append
  (equal (bind-list-names (append a b))
         (append (bind-list-names a) (bind-list-names b)))
  :induct (len a)
  :enable bind-list-names)

; For lists of functions, the names and the bound variables agree.

(defrule ll-defs-ok-p-of-emit-lifted-lambda
  (ll-defs-ok-p (mv-nth 1 (emit-lifted-lambda params body type? tenv locals
                                              used)))
  :enable (emit-lifted-lambda ll-def-ok-p))

(defrule ll-def-ok-p-of-hoist-local-fun
  (implies (mv-nth 0 (hoist-local-fun b rebound tenv locals used))
           (ll-def-ok-p (mv-nth 2 (hoist-local-fun b rebound tenv locals
            used))))
  :enable (hoist-local-fun ll-def-ok-p)
  :disable (set::intersect-under-set-equiv
            acl2::set-equiv-implies-equal-consp-1))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The names of the lifted definitions are fresh in sequence: each is not in
; use, and is in use after it.  So they are distinct, and none is among the
; names in use at the start.

(define fresh-seq-p ((names string-listp) (used string-setp))
  :returns (yes/no booleanp)
  (or (endp names)
      (and (not (set::in (str-fix (car names)) (string-sfix used)))
           (fresh-seq-p (cdr names)
                        (set::insert (str-fix (car names))
                                     (string-sfix used))))))

(defrule fresh-seq-p-of-string-sfix
  (equal (fresh-seq-p names (string-sfix used))
         (fresh-seq-p names used))
  :expand ((fresh-seq-p names (string-sfix used))
           (fresh-seq-p names used)))

(defrule fresh-seq-p-of-nil
  (fresh-seq-p nil used)
  :enable fresh-seq-p)

(defun fresh-seq-2-ind (names used used1)
  (declare (xargs :verify-guards nil))
  (if (endp names)
      (list used used1)
    (fresh-seq-2-ind (cdr names)
                     (set::insert (str-fix (car names)) (string-sfix used))
                     (set::insert (str-fix (car names)) (string-sfix used1)))))

(defruled fresh-seq-p-when-fewer-used
  (implies (and (fresh-seq-p names used1)
                (set::subset (string-sfix used) (string-sfix used1)))
           (fresh-seq-p names used))
  :induct (fresh-seq-2-ind names used used1)
  :expand ((fresh-seq-p names used1)
           (fresh-seq-p names used))
  :hints (("Subgoal *1/2"
           :use ((:instance subset-of-insert-both
                            (a (str-fix (car names)))
                            (x (string-sfix used))
                            (y (string-sfix used1)))
                 (:instance set::subset-in
                            (set::a (str-fix (car names)))
                            (set::x (string-sfix used))
                            (set::y (string-sfix used1)))))))

(defun names-append-ind (a used)
  (declare (xargs :verify-guards nil))
  (if (endp a)
      used
    (names-append-ind (cdr a) (set::insert (bind-name (car a))
                                           (string-sfix used)))))

(defruled fresh-seq-p-of-names-append
  (implies (and (ll-defs-ok-p a)
                (fresh-seq-p (bind-list-names a) used)
                (fresh-seq-p (bind-list-names b) used1)
                (set::subset (string-sfix used) (string-sfix used1))
                (set::subset (bind-list-bound-expr-vars a) (string-sfix used1)))
           (fresh-seq-p (bind-list-names (append a b)) used))
  :induct (names-append-ind a used)
  :enable (fresh-seq-p bind-list-names ll-defs-ok-p ll-def-ok-p bind-name
           bind-list-bound-expr-vars bind-bound-expr-vars
           set::subset-insert-x)
  :hints (("Subgoal *1/1"
           :use ((:instance fresh-seq-p-when-fewer-used
                            (names (bind-list-names b)))))))

(defruled fresh-seq-p-of-cons-names
  (equal (fresh-seq-p (bind-list-names (cons b defs)) used)
         (and (not (set::in (bind-name b) (string-sfix used)))
              (fresh-seq-p (bind-list-names defs)
                           (set::insert (bind-name b) (string-sfix used)))))
  :expand ((bind-list-names (cons b defs))
           (fresh-seq-p (cons (bind-name b) (bind-list-names defs)) used)))

(defrule fresh-seq-p-of-emit-lifted-lambda
  (fresh-seq-p (bind-list-names
                (mv-nth 1 (emit-lifted-lambda params body type? tenv locals
                                              used)))
               used)
  :enable (emit-lifted-lambda bind-list-names bind-name fresh-seq-p))

(defruled fresh-seq-p-of-names-append-emit
  (implies (and (ll-defs-ok-p a)
                (fresh-seq-p (bind-list-names a) used)
                (set::subset (string-sfix used) (string-sfix used1))
                (set::subset (bind-list-bound-expr-vars a) (string-sfix used1)))
           (fresh-seq-p (bind-list-names
                         (append a (mv-nth 1 (emit-lifted-lambda
                                              params body type? tenv locals
                                              used1))))
                        used))
  :use ((:instance fresh-seq-p-of-names-append
                   (b (mv-nth 1 (emit-lifted-lambda params body type? tenv
                                                    locals used1)))))
  :disable bind-list-names-of-append)

(defruled bind-name-of-hoist-local-fun
  (implies (mv-nth 0 (hoist-local-fun b rebound tenv locals used))
           (equal (bind-name (mv-nth 2 (hoist-local-fun b rebound tenv locals
                                                        used)))
                  (fresh-expr-var (bind-fun->var b) (string-sfix used))))
  :enable (hoist-local-fun bind-name))

(defruled fresh-seq-p-of-names-append-hoisted
  (implies (and (mv-nth 0 (hoist-local-fun b rebound tenv locals used1))
                (ll-defs-ok-p a)
                (fresh-seq-p (bind-list-names a) used)
                (fresh-seq-p (bind-list-names rest)
                             (set::insert (fresh-expr-var (bind-fun->var b)
                                                          (string-sfix used1))
                                          (string-sfix used1)))
                (set::subset (string-sfix used) (string-sfix used1))
                (set::subset (bind-list-bound-expr-vars a) (string-sfix used1)))
           (fresh-seq-p (bind-list-names
                         (append a (cons (mv-nth 2 (hoist-local-fun
                                                    b rebound tenv locals
                                                    used1))
                                         rest)))
                        used))
  :use ((:instance fresh-seq-p-of-names-append
                   (b (cons (mv-nth 2 (hoist-local-fun b rebound tenv locals
                                                       used1))
                            rest)))
        (:instance bind-name-of-hoist-local-fun (used used1))
        (:instance fresh-expr-var-is-fresh
                   (prefix (bind-fun->var b)) (used (string-sfix used1))))
  :enable fresh-seq-p-of-cons-names
  :disable (bind-list-names-of-append hoist-local-fun-when-hoisted))

(defruled not-member-when-fresh-seq-p
  (implies (and (string-listp names)
                (fresh-seq-p names used)
                (set::in v (string-sfix used)))
           (not (member-equal v names)))
  :induct (fresh-seq-p names used)
  :enable fresh-seq-p)

(defruled no-duplicatesp-when-fresh-seq-p
  (implies (and (string-listp names) (fresh-seq-p names used))
           (no-duplicatesp-equal names))
  :induct (fresh-seq-p names used)
  :enable fresh-seq-p
  :hints (("Subgoal *1/2"
           :use ((:instance not-member-when-fresh-seq-p
                            (names (cdr names))
                            (used (set::insert (car names) (string-sfix used)))
                            (v (car names)))))))

(defret-mutual lifted-defs-ok-of-lambda-lift-exprs/atoms/binds
  (defret lifted-defs-ok-of-ll-expr
    (and (ll-defs-ok-p lifted)
         (fresh-seq-p (bind-list-names lifted) used))
    :fn ll-expr)
  (defret lifted-defs-ok-of-ll-lambda
    (and (ll-defs-ok-p lifted)
         (fresh-seq-p (bind-list-names lifted) used))
    :fn ll-lambda)
  (defret lifted-defs-ok-of-ll-let-binds
    (and (ll-defs-ok-p lifted)
         (fresh-seq-p (bind-list-names lifted) used))
    :fn ll-let-binds)
  (defret lifted-defs-ok-of-ll-expr-list
    (and (ll-defs-ok-p lifted)
         (fresh-seq-p (bind-list-names lifted) used))
    :fn ll-expr-list)
  (defret lifted-defs-ok-of-ll-atom
    (and (ll-defs-ok-p lifted)
         (fresh-seq-p (bind-list-names lifted) used))
    :fn ll-atom)
  (defret lifted-defs-ok-of-ll-atom-list
    (and (ll-defs-ok-p lifted)
         (fresh-seq-p (bind-list-names lifted) used))
    :fn ll-atom-list)
  (defret lifted-defs-ok-of-ll-bind
    (and (ll-defs-ok-p lifted)
         (fresh-seq-p (bind-list-names lifted) used))
    :fn ll-bind)
  :mutual-recursion lambda-lift-exprs/atoms/binds
  :hints (("Goal"
           :in-theory (e/d (fresh-seq-p-of-names-append
                            fresh-seq-p-of-names-append-emit
                            fresh-seq-p-of-names-append-hoisted
                            fresh-seq-p-of-cons-names
                            fresh-seq-p-of-emit-lifted-lambda
                            fresh-seq-p-of-nil)
                           (emit-lifted-lambda hoist-local-fun apply-to-names
                            bind-list-names-of-append
                            acl2::utf8-table36-length-lemmas))
           :expand ((ll-expr x tenv tlets locals lmap used)
                    (:free (type?) (ll-lambda params body type? tenv tlets
                     locals lmap used))
                    (ll-let-binds binds body-binders tenv tlets locals lmap
                     used)
                    (ll-expr-list x tenv tlets locals lmap used)
                    (ll-atom x tenv tlets locals lmap used)
                    (ll-atom-list x tenv tlets locals lmap used)
                    (ll-bind x tenv tlets locals lmap used)
                    (ll-bind (bind-fix (car binds)) tenv tlets locals lmap
                     used)))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Evaluating a lifted definition: it binds its name to a closure, which
; depends on the environment only through its type environment and the
; variables free in the definition.

(define ll-def-value ((d bindp) (denv expr-denvp))
  :verify-guards nil
  (expr-denv-lookup-expr (bind-fun->var d) (eval-bind d denv 1)))

(defmacro %closed-def (d)
  `(and (set::emptyp (bind-free-type-vars ,d))
        (set::emptyp (bind-free-ispace-vars ,d))))

(defruled closed-of-car-param-type
  (implies (and (consp ps)
                (var+type?->type? (car ps))
                (set::emptyp (var+type?-list-free-type-vars ps))
                (set::emptyp (var+type?-list-free-ispace-vars ps)))
           (and (set::emptyp (type-free-type-vars
                              (type-option-some->val
                               (var+type?->type? (car ps)))))
                (set::emptyp (type-free-ispace-vars
                              (type-option-some->val
                               (var+type?->type? (car ps)))))))
  :expand ((var+type?-list-free-type-vars ps)
           (var+type?-list-free-ispace-vars ps)
           (var+type?-free-type-vars (car ps))
           (var+type?-free-ispace-vars (car ps))
           (type-option-free-type-vars (var+type?->type? (car ps)))
           (type-option-free-ispace-vars (var+type?->type? (car ps)))))

(defruled closed-of-type-option-some
  (implies (and (type-option-fix type?)
                (set::emptyp (type-option-free-type-vars type?))
                (set::emptyp (type-option-free-ispace-vars type?)))
           (and (set::emptyp (type-free-type-vars
                              (type-option-some->val type?)))
                (set::emptyp (type-free-ispace-vars
                              (type-option-some->val type?)))))
  :expand ((type-option-free-type-vars type?)
           (type-option-free-ispace-vars type?)))

(defruled eval-bind-when-ll-def-ok
  (implies (and (ll-def-ok-p d)
                (%closed-def d)
                (posp l))
           (and (not (reserrp (eval-bind d denv l)))
                (equal (eval-bind d denv l)
                       (expr-denv-add-expr (bind-fun->var d)
                                           (ll-def-value d denv)
                                           denv))))
  :expand ((eval-bind d denv l)
           (eval-bind d denv 1)
           (bind-free-type-vars d)
           (bind-free-ispace-vars d))
  :use ((:instance closed-of-car-param-type (ps (bind-fun->params d)))
        (:instance closed-of-type-option-some (type? (bind-fun->type? d))))
  :enable (ll-def-value ll-def-ok-p param-evaluable-p type-option-evaluable-p
           type-evaluable-p eval-var+type? var+type?->type-or-err
           expr-denv-lookup-expr expr-denv-add-expr eval-type-when-closed))
(defruled ll-def-value-when-same-restriction
  (implies (and (ll-def-ok-p d)
                (equal (expr-denv->tenv e1) (expr-denv->tenv e2))
                (equal (omap::restrict (bind-free-expr-vars d)
                                       (expr-denv->exprs e1))
                       (omap::restrict (bind-free-expr-vars d)
                                       (expr-denv->exprs e2))))
           (equal (ll-def-value d e1) (ll-def-value d e2)))
  :expand ((eval-bind d e1 1)
           (eval-bind d e2 1)
           (bind-free-expr-vars d))
  :enable (ll-def-value ll-def-ok-p expr-denv-restrict expr-denv-lookup-expr
           expr-denv-add-expr))

; The environment at the top of the lifted program: the definitions bound
; in order.

(defun ll-top-env (defs denv)
  (declare (xargs :verify-guards nil))
  (if (endp defs)
      (expr-denv-fix denv)
    (ll-top-env (cdr defs) (eval-bind (car defs) denv 1))))

(define ll-defs-closed-p ((defs bind-listp))
  :returns (yes/no booleanp)
  (or (endp defs)
      (and (set::emptyp (bind-free-type-vars (car defs)))
           (set::emptyp (bind-free-ispace-vars (car defs)))
           (ll-defs-closed-p (cdr defs)))))

(defruled ll-defs-closed-p-when-binds-closed-p
  (implies (binds-closed-p defs)
           (ll-defs-closed-p defs))
  :induct (len defs)
  :enable (ll-defs-closed-p binds-closed-p))

(defmacro %top-hyps (defs)
  `(and (ll-defs-ok-p ,defs) (ll-defs-closed-p ,defs)))

(defrule tenv-of-ll-top-env
  (implies (%top-hyps defs)
           (equal (expr-denv->tenv (ll-top-env defs denv))
                  (expr-denv->tenv denv)))
  :induct (ll-top-env defs denv)
  :enable (ll-defs-ok-p ll-defs-closed-p expr-denv-add-expr)
  :hints (("Subgoal *1/2"
           :use ((:instance eval-bind-when-ll-def-ok
                            (d (car defs)) (l 1))))))

(defrule lookup-of-ll-top-env-when-not-name
  (implies (and (%top-hyps defs)
                (not (member-equal (str-fix k) (bind-list-names defs))))
           (equal (expr-denv-lookup-expr k (ll-top-env defs denv))
                  (expr-denv-lookup-expr k denv)))
  :induct (ll-top-env defs denv)
  :enable (ll-defs-ok-p ll-def-ok-p ll-defs-closed-p bind-list-names bind-name
           expr-denv-add-expr expr-denv-lookup-expr)
  :hints (("Subgoal *1/2"
           :use ((:instance eval-bind-when-ll-def-ok
                            (d (car defs)) (l 1))))))

(define names-not-in-p ((names string-listp) (s string-setp))
  :returns (yes/no booleanp)
  (or (endp names)
      (and (not (set::in (car names) s))
           (names-not-in-p (cdr names) s))))

(defrule restrict-of-ll-top-env-when-names-not-in
  (implies (and (%top-hyps defs)
                (names-not-in-p (bind-list-names defs) s))
           (equal (omap::restrict s (expr-denv->exprs (ll-top-env defs denv)))
                  (omap::restrict s (expr-denv->exprs denv))))
  :induct (ll-top-env defs denv)
  :enable (ll-defs-ok-p ll-def-ok-p ll-defs-closed-p bind-list-names bind-name
           names-not-in-p expr-denv-add-expr
           restrict-of-update-when-not-in)
  :hints (("Subgoal *1/2"
           :use ((:instance eval-bind-when-ll-def-ok
                            (d (car defs)) (l 1))))))

(defrule expr-denv-wfp-of-ll-top-env
  (implies (and (%top-hyps defs)
                (expr-denv-wfp denv))
           (expr-denv-wfp (ll-top-env defs denv)))
  :induct (ll-top-env defs denv)
  :enable (ll-defs-ok-p ll-defs-closed-p)
  :hints (("Subgoal *1/2"
           :use ((:instance eval-bind-when-ll-def-ok
                            (d (car defs)) (l 1))
                 (:instance expr-denv-wfp-of-eval-bind
                            (bind (car defs)) (limit 1))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The top environment is the fixed point that LL-DEFS-BOUND-P describes:
; each definition refers neither to itself nor to the ones after it, whose
; names are distinct, so binding them does not change the closure that
; evaluating it gives.

(define no-forward-refs-p ((defs bind-listp))
  :returns (yes/no booleanp)
  (or (endp defs)
      (and (names-not-in-p (bind-list-names defs)
                           (bind-free-expr-vars (car defs)))
           (no-forward-refs-p (cdr defs)))))

(defruled lookup-of-expr-denv-add-expr-same
  (equal (expr-denv-lookup-expr k (expr-denv-add-expr k v denv))
         (expr-value-fix v))
  :enable (expr-denv-lookup-expr expr-denv-add-expr))

(defrule ll-defs-bound-p-of-ll-top-env
  (implies (and (%top-hyps defs)
                (no-duplicatesp-equal (bind-list-names defs))
                (no-forward-refs-p defs))
           (ll-defs-bound-p defs (ll-top-env defs denv)))
  :induct (ll-top-env defs denv)
  :enable (ll-defs-bound-p ll-defs-ok-p ll-defs-closed-p no-forward-refs-p
           bind-list-names bind-name names-not-in-p ll-def-ok-p)
  :hints (("Subgoal *1/2"
           :use ((:instance eval-bind-when-ll-def-ok
                            (d (car defs)) (l 1))
                 (:instance eval-bind-when-ll-def-ok
                            (d (car defs)) (l 1)
                            (denv (ll-top-env (cdr defs)
                                              (eval-bind (car defs) denv 1))))
                 (:instance lookup-of-expr-denv-add-expr-same
                            (k (bind-fun->var (car defs)))
                            (v (ll-def-value (car defs)
                                             (ll-top-env
                                              (cdr defs)
                                              (eval-bind (car defs) denv 1))))
                            (denv (ll-top-env (cdr defs)
                                              (eval-bind (car defs) denv 1))))
                 (:instance lookup-of-expr-denv-add-expr-same
                            (k (bind-fun->var (car defs)))
                            (v (ll-def-value (car defs) denv)))
                 (:instance lookup-of-ll-top-env-when-not-name
                            (k (bind-fun->var (car defs)))
                            (defs (cdr defs))
                            (denv (eval-bind (car defs) denv 1)))
                 (:instance restrict-of-ll-top-env-when-names-not-in
                            (defs (cdr defs))
                            (denv (eval-bind (car defs) denv 1))
                            (s (bind-free-expr-vars (car defs))))
                 (:instance restrict-of-update-when-not-in
                            (k (bind-fun->var (car defs)))
                            (v (expr-value-fix (ll-def-value (car defs) denv)))
                            (s (bind-free-expr-vars (car defs)))
                            (m (expr-denv->exprs denv)))
                 (:instance ll-def-value-when-same-restriction
                            (d (car defs))
                            (e1 (ll-top-env (cdr defs)
                                            (eval-bind (car defs) denv 1)))
                            (e2 denv)))
           :in-theory (e/d (expr-denv-add-expr)
                           (lookup-of-ll-top-env-when-not-name
                            restrict-of-ll-top-env-when-names-not-in)))))

; The hypothesis follows from the placement of the definitions: what the
; definitions refer to, in sequence, is among some names that none of them
; is named like.

(defruled names-not-in-p-when-subset
  (implies (and (names-not-in-p names u)
                (set::subset s u))
           (names-not-in-p names s))
  :induct (len names)
  :enable names-not-in-p
  :hints (("Subgoal *1/1"
           :use ((:instance set::subset-in
                            (set::a (car names)) (set::x s) (set::y u))))))

(defruled names-not-in-p-of-insert
  (equal (names-not-in-p names (set::insert a s))
         (and (not (member-equal a names))
              (names-not-in-p names s)))
  :induct (len names)
  :enable names-not-in-p)

(defun defs-insert-ind (defs u)
  (declare (xargs :verify-guards nil))
  (if (endp defs)
      u
    (defs-insert-ind (cdr defs) (set::insert (bind-fun->var (car defs)) u))))

(defruled no-forward-refs-p-when-placed
  (implies (and (ll-defs-ok-p defs)
                (no-duplicatesp-equal (bind-list-names defs))
                (set::subset (bind-list-free-expr-vars defs) u)
                (names-not-in-p (bind-list-names defs) u))
           (no-forward-refs-p defs))
  :induct (defs-insert-ind defs u)
  :enable (no-forward-refs-p ll-defs-ok-p ll-def-ok-p bind-list-names
           bind-name names-not-in-p names-not-in-p-of-insert subset-of-union)
  :hints (("Subgoal *1/2"
           :expand ((bind-list-free-expr-vars defs)
                    (bind-bound-expr-vars (car defs)))
           :use ((:instance names-not-in-p-when-subset
                            (names (bind-list-names defs))
                            (s (bind-free-expr-vars (car defs))))
                 (:instance subset-insert-when-subset-delete
                            (a (bind-list-free-expr-vars (cdr defs)))
                            (n (bind-fun->var (car defs))))))))

(defruled names-not-in-p-when-fresh-seq-p
  (implies (and (string-listp names)
                (fresh-seq-p names used))
           (names-not-in-p names (string-sfix used)))
  :induct (fresh-seq-p names used)
  :enable (fresh-seq-p names-not-in-p)
  :hints (("Subgoal *1/2"
           :use ((:instance names-not-in-p-when-subset
                            (names (cdr names))
                            (u (set::insert (car names) (string-sfix used)))
                            (s (string-sfix used)))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Evaluating the nested :LETs of the lifted definitions: each consumes one
; unit of the limit (the binding itself needs limit 1), and the body is
; evaluated in the top environment.

(defruled eval-expr-of-single-let
  (implies (and (integerp m) (<= 2 m))
           (equal (eval-expr (expr-let (list b) r) denv (+ 1 m))
                  (b* ((d2 (eval-bind b denv (+ -1 m))))
                    (if (reserrp d2) d2 (eval-expr r d2 m)))))
  :expand ((eval-expr (expr-let (list b) r) denv (+ 1 m))
           (eval-bind-list (list (bind-fix b)) denv m)
           (eval-bind-list nil (eval-bind b denv (+ -1 m)) (+ -1 m))))

(defruled eval-expr-of-nest-let-binds
  (implies (and (%top-hyps defs)
                (integerp l)
                (<= 2 l))
           (equal (eval-expr (nest-let-binds defs body) denv (+ l (len defs)))
                  (eval-expr body (ll-top-env defs denv) l)))
  :induct (ll-top-env defs denv)
  :enable (nest-let-binds ll-defs-ok-p ll-defs-closed-p len)
  :hints (("Subgoal *1/2"
           :use ((:instance eval-expr-of-single-let
                            (b (car defs))
                            (r (nest-let-binds (cdr defs) body))
                            (m (+ l (len (cdr defs)))))
                 (:instance eval-bind-when-ll-def-ok
                            (d (car defs)) (l 1))
                 (:instance eval-bind-when-ll-def-ok
                            (d (car defs)) (l (+ -1 l (len (cdr defs)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The top environment binds what the initial one binds as it does, since no
; definition is named like a variable it binds.

(defruled names-bound-as-in-p-of-same
  (names-bound-as-in-p s g g)
  :induct (names-bound-as-in-p s g g)
  :enable names-bound-as-in-p)

(defruled not-in-when-names-not-in-p
  (implies (and (names-not-in-p names s)
                (member-equal v names))
           (not (set::in v s)))
  :induct (len names)
  :enable names-not-in-p)

(defruled lookup-of-ll-top-env-when-bound-before
  (implies (and (%top-hyps defs)
                (names-not-in-p (bind-list-names defs)
                                (omap::keys (expr-denv->exprs denv)))
                (not (reserrp (expr-denv-lookup-expr k denv))))
           (equal (expr-denv-lookup-expr k (ll-top-env defs denv))
                  (expr-denv-lookup-expr k denv)))
  :cases ((member-equal (str-fix k) (bind-list-names defs)))
  :hints (("Subgoal 1"
           :use ((:instance not-in-when-names-not-in-p
                            (names (bind-list-names defs))
                            (v (str-fix k))
                            (s (omap::keys (expr-denv->exprs denv)))))
           :in-theory (enable expr-denv-lookup-expr omap::in-of-keys-to-assoc)))
  :disable ll-top-env)

(defruled names-bound-as-in-p-of-ll-top-env
  (implies (and (%top-hyps defs)
                (names-not-in-p (bind-list-names defs)
                                (omap::keys (expr-denv->exprs denv))))
           (names-bound-as-in-p s (ll-top-env defs denv) denv))
  :induct (names-bound-as-in-p s (ll-top-env defs denv) denv)
  :enable (names-bound-as-in-p lookup-of-ll-top-env-when-bound-before)
  :disable ll-top-env)

(defruled names-not-in-p-init-when-ll-defs-ok
  (implies (ll-defs-ok-p defs)
           (names-not-in-p (bind-list-names defs)
                           (omap::keys (expr-denv->exprs (init-expr-denv)))))
  :induct (len defs)
  :enable (ll-defs-ok-p ll-def-ok-p names-not-in-p bind-list-names bind-name
           omap::in-of-keys-to-assoc)
  :disable ((:e init-expr-denv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The environments at the top are related: the initial one binds only the
; primitive operations, which are ground and bound as in the top one.

(defruled lookup-init-of-head-of-submap
  (implies (and (omap::submap m (expr-denv->exprs (init-expr-denv)))
                (not (omap::emptyp m))
                (string-expr-value-mapp m))
           (equal (expr-denv-lookup-expr (mv-nth 0 (omap::head m))
                                         (init-expr-denv))
                  (mv-nth 1 (omap::head m))))
  :use ((:instance omap::assoc-when-submap-and-assoc
                   (key (mv-nth 0 (omap::head m)))
                   (sub m)
                   (sup (expr-denv->exprs (init-expr-denv))))
        cdr-assoc-of-head-key)
  :enable expr-denv-lookup-expr
  :disable ((:e init-expr-denv)))

(defruled walker-at-top
  (implies (and (omap::submap m (expr-denv->exprs (init-expr-denv)))
                (string-expr-value-mapp m)
                (%top-hyps defs))
           (string-expr-value-map-ll-related-p
            (ll-top-env defs (init-expr-denv))
            m fv nfv
            (ll-context nil nil nil nil used)
            (ll-denv-witness nil 0)
            (ll-top-env defs (init-expr-denv))))
  :induct (omap::size m)
  :expand ((:free (c w g)
            (string-expr-value-map-ll-related-p g m fv nfv c w g)))
  :enable (lookup-of-ll-top-env-when-bound-before
           lookup-init-of-head-of-submap
           names-not-in-p-init-when-ll-defs-ok
           not-reserrp-when-expr-valuep
           value-meets-required-type-p var-required-type name-to-type-option
           omap::size)
  :disable (ll-top-env (:e init-expr-denv) expr-value-ll-related-p
            expr-denv-lookup-expr expr-value-groundp-of-init-lookup)
  :hints (("Subgoal *1/2"
           :use ((:instance expr-value-ll-related-p-of-ground
                            (val (mv-nth 1 (omap::head m)))
                            (genv (ll-top-env defs (init-expr-denv))))
                 (:instance expr-value-groundp-of-init-lookup
                            (v (mv-nth 0 (omap::head m))))))))

(defruled expr-denv-ll-related-p-at-top
  (implies (%top-hyps defs)
           (expr-denv-ll-related-p (ll-top-env defs (init-expr-denv))
                                   (init-expr-denv)
                                   x
                                   (ll-context nil nil nil nil used)
                                   nil
                                   (ll-denv-witness nil 0)
                                   (ll-top-env defs (init-expr-denv))))
  :expand ((:free (c w)
            (expr-denv-ll-related-p (ll-top-env defs (init-expr-denv))
                                    (init-expr-denv) x c nil w
                                    (ll-top-env defs (init-expr-denv)))))
  :use ((:instance walker-at-top
                   (m (expr-denv->exprs (init-expr-denv)))
                   (fv (set::difference (expr-free-expr-vars x)
                                        (set::mergesort nil)))
                   (nfv (expr-free-expr-vars
                         (ll-context-new-expr
                          x (ll-context nil nil nil nil used))))))
  :enable (names-bound-as-in-p-of-same new-values-meet-types-p)
  :disable (ll-top-env (:e init-expr-denv) walker-at-top
            string-expr-value-map-ll-related-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The context at the top: nothing is local, no function is hoisted, and the
; names in use are those of LAMBDA-LIFT-TOP-USED, which include every
; binder name.

(defruled top-lifted-facts
  (implies (not (expr-duplicate-names x))
           (b* ((u (lambda-lift-top-used x))
                (defs (mv-nth 1 (ll-expr x nil nil nil nil u))))
             (and (ll-defs-ok-p defs)
                  (ll-defs-closed-p defs)
                  (no-duplicatesp-equal (bind-list-names defs))
                  (names-not-in-p (bind-list-names defs) u)
                  (set::subset (bind-list-free-expr-vars defs) u)
                  (no-forward-refs-p defs))))
  :use ((:instance lifted-defs-ok-of-ll-expr
                   (tenv nil) (tlets nil) (locals nil) (lmap nil)
                   (used (lambda-lift-top-used x)))
        (:instance no-duplicatesp-when-fresh-seq-p
                   (names (bind-list-names
                           (mv-nth 1 (ll-expr x nil nil nil nil
                                              (lambda-lift-top-used x)))))
                   (used (lambda-lift-top-used x)))
        (:instance names-not-in-p-when-fresh-seq-p
                   (names (bind-list-names
                           (mv-nth 1 (ll-expr x nil nil nil nil
                                              (lambda-lift-top-used x)))))
                   (used (lambda-lift-top-used x)))
        binds-closed-p-of-lifted-of-lambda-lift-top-expr
        (:instance ll-defs-closed-p-when-binds-closed-p
                   (defs (mv-nth 1 (ll-expr x nil nil nil nil
                                            (lambda-lift-top-used x)))))
        expr-free-expr-vars-of-lambda-lift-top-expr
        (:instance expr-free-expr-vars-subset-all (expr x))
        subset-of-expr-all-expr-vars-of-lambda-lift-top-used
        (:instance no-forward-refs-p-when-placed
                   (defs (mv-nth 1 (ll-expr x nil nil nil nil
                                            (lambda-lift-top-used x))))
                   (u (lambda-lift-top-used x))))
  :enable (lambda-lift-top-expr subset-of-union set::subset-transitive)
  :disable (lifted-defs-ok-of-ll-expr
            binds-closed-p-of-lifted-of-lambda-lift-top-expr
            expr-free-expr-vars-of-lambda-lift-top-expr
            subset-of-expr-all-expr-vars-of-lambda-lift-top-used))

(defruled subsetp-binder-names-of-top-used
  (subsetp-equal (expr-binder-names x) (lambda-lift-top-used x))
  :use ((:instance subsetp-equal-when-all-in
                   (l (expr-binder-names x)) (s (lambda-lift-top-used x)))
        (:instance set::union-subset-y
                   (set::x (expr-all-expr-vars x))
                   (set::y (set::mergesort (expr-binder-names x)))))
  :enable lambda-lift-top-used)

(defruled ll-context-ok-p-at-top
  (implies (not (expr-duplicate-names x))
           (b* ((u (lambda-lift-top-used x))
                (defs (mv-nth 1 (ll-expr x nil nil nil nil u))))
             (ll-context-ok-p x (ll-context nil nil nil nil u)
                              (ll-top-env defs (init-expr-denv)))))
  :use (top-lifted-facts
        subsetp-binder-names-of-top-used
        (:instance ll-defs-bound-p-of-ll-top-env
                   (defs (mv-nth 1 (ll-expr x nil nil nil nil
                                            (lambda-lift-top-used x))))
                   (denv (init-expr-denv)))
        (:instance names-bound-as-in-p-of-ll-top-env
                   (defs (mv-nth 1 (ll-expr x nil nil nil nil
                                            (lambda-lift-top-used x))))
                   (denv (init-expr-denv))
                   (s (omap::keys (expr-denv->exprs (init-expr-denv)))))
        (:instance names-not-in-p-init-when-ll-defs-ok
                   (defs (mv-nth 1 (ll-expr x nil nil nil nil
                                            (lambda-lift-top-used x)))))
        (:instance expr-denv-wfp-of-ll-top-env
                   (defs (mv-nth 1 (ll-expr x nil nil nil nil
                                            (lambda-lift-top-used x))))
                   (denv (init-expr-denv))))
  :enable (ll-context-ok-p ll-context-lifted genv-agrees-with-init-p
           lmap-replacements-ok-p)
  :disable (ll-top-env (:e init-expr-denv) ll-defs-bound-p-of-ll-top-env
            expr-denv-wfp-of-ll-top-env lambda-lift-top-used
            (:e expr-denv-wfp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The theorem.  The simulation gives a limit at which the rebuilt
; expression, in the top environment, evaluates to a value related to the
; original one, which is equal to it if ground; the lifted program reaches
; the rebuilt expression with the top environment, at a limit larger by the
; number of definitions (and by two, so that each binding is evaluated).

(defrule equal-when-fixes-equal-and-not-errors
  (implies (and (expr-value-resultp a)
                (expr-value-resultp b)
                (not (reserrp a))
                (not (reserrp b))
                (equal (expr-value-fix a) (expr-value-fix b)))
           (equal a b))
  :rule-classes nil
  :enable expr-valuep-when-result-not-error)

(defruled eval-lambda-lift-top-expr-at
  (b* ((u (lambda-lift-top-used x))
       (defs (mv-nth 1 (ll-expr x nil nil nil nil u)))
       (nx (mv-nth 0 (ll-expr x nil nil nil nil u)))
       (g (ll-top-env defs (init-expr-denv))))
    (implies (and (not (expr-duplicate-names x))
                  (natp l)
                  (not (reserrp (eval-expr nx g l))))
             (equal (eval-expr (lambda-lift-top-expr x) (init-expr-denv)
                               (+ 2 l (len defs)))
                    (eval-expr nx g l))))
  :use (top-lifted-facts
        (:instance eval-expr-at-larger-limit
                   (expr (mv-nth 0 (ll-expr x nil nil nil nil
                                            (lambda-lift-top-used x))))
                   (denv (ll-top-env (mv-nth 1 (ll-expr x nil nil nil nil
                                                        (lambda-lift-top-used
                                                         x)))
                                     (init-expr-denv)))
                   (limit l) (limit2 (+ 2 l)))
        (:instance eval-expr-of-nest-let-binds
                   (defs (mv-nth 1 (ll-expr x nil nil nil nil
                                            (lambda-lift-top-used x))))
                   (body (mv-nth 0 (ll-expr x nil nil nil nil
                                            (lambda-lift-top-used x))))
                   (denv (init-expr-denv)) (l (+ 2 l))))
  :enable (lambda-lift-top-expr)
  :disable (ll-top-env (:e init-expr-denv) eval-expr-of-nest-let-binds
            top-lifted-facts))

(defmacro %top-nx (x)
  `(mv-nth 0 (ll-expr ,x nil nil nil nil (lambda-lift-top-used ,x))))

(defmacro %top-env (x)
  `(ll-top-env (mv-nth 1 (ll-expr ,x nil nil nil nil (lambda-lift-top-used ,x)))
               (init-expr-denv)))

(defruled lambda-lift-top-expr-eval-ok-p-when-related
  (b* ((val (eval-top-expr x limit))
       (nv (eval-expr (%top-nx x) (%top-env x) l)))
    (implies (and (not (expr-duplicate-names x))
                  (natp l)
                  (not (reserrp nv))
                  (expr-value-ll-related-p nv val w (%top-env x))
                  (not (reserrp val))
                  (expr-value-groundp val))
             (lambda-lift-top-expr-eval-ok-p x limit)))
  :use (eval-lambda-lift-top-expr-at
        (:instance equal-when-expr-value-ll-related-p-groundp
                   (new-val (eval-expr (%top-nx x) (%top-env x) l))
                   (val (eval-top-expr x limit))
                   (genv (%top-env x)))
        (:instance equal-when-fixes-equal-and-not-errors
                   (a (eval-expr (%top-nx x) (%top-env x) l))
                   (b (eval-top-expr x limit)))
        (:instance lambda-lift-top-expr-eval-ok-p-suff
                   (expr x)
                   (limit2 (+ 2 l (len (mv-nth 1 (ll-expr x nil nil nil nil
                                                          (lambda-lift-top-used
                                                           x))))))))
  :in-theory (e/d (eval-top-expr)
                  (ll-top-env lambda-lift-top-expr
                   lambda-lift-top-expr-eval-ok-p
                   lambda-lift-top-expr-eval-ok-p-suff expr-value-ll-related-p
                   eval-lambda-lift-top-expr-at
                   equal-when-expr-value-ll-related-p-groundp)))

(defmacro %top-w (x limit)
  `(eval-expr-ll-reaches-p-witness (%top-nx ,x) (%top-env ,x)
                                   (eval-expr ,x (init-expr-denv) ,limit)
                                   (%top-env ,x)))

(defruled lambda-lift-top-expr-eval-ok-when-ground
  (implies (and (check-sound-p)
                (exprp x)
                (not (expr-duplicate-names x))
                (not (reserrp (eval-top-expr x limit)))
                (expr-value-groundp (eval-top-expr x limit)))
           (lambda-lift-top-expr-eval-ok-p x limit))
  :use ((:instance eval-expr-ll-ok-holds
                   (expr x) (denv (init-expr-denv)))
        (:instance eval-expr-ll-ok-necc
                   (expr x) (denv (init-expr-denv))
                   (ctx (ll-context nil nil nil nil (lambda-lift-top-used x)))
                   (new-denv (%top-env x))
                   (dw (ll-denv-witness nil 0))
                   (genv (%top-env x)))
        (:instance expr-denv-ll-related-p-at-top
                   (defs (mv-nth 1 (ll-expr x nil nil nil nil
                                            (lambda-lift-top-used x))))
                   (used (lambda-lift-top-used x)))
        ll-context-ok-p-at-top
        top-lifted-facts
        (:instance expr-denv-wfp-of-ll-top-env
                   (defs (mv-nth 1 (ll-expr x nil nil nil nil
                                            (lambda-lift-top-used x))))
                   (denv (init-expr-denv)))
        (:instance eval-expr-ll-reaches-p-elim
                   (new-expr (%top-nx x))
                   (new-denv (%top-env x))
                   (val (eval-expr x (init-expr-denv) limit))
                   (genv (%top-env x)))
        (:instance posp-limit-when-eval-expr-ok
                   (expr (%top-nx x))
                   (denv (%top-env x))
                   (limit (mv-nth 0 (%top-w x limit))))
        (:instance lambda-lift-top-expr-eval-ok-p-when-related
                   (l (mv-nth 0 (%top-w x limit)))
                   (w (mv-nth 1 (%top-w x limit)))))
  :in-theory (e/d (eval-top-expr ll-context-new-expr)
                  (ll-top-env (:e init-expr-denv) eval-expr-ll-ok-holds
                   eval-expr-ll-ok eval-expr-ll-ok-necc eval-expr-ll-reaches-p
                   ll-context-ok-p lambda-lift-top-expr-eval-ok-p
                   expr-denv-ll-related-p expr-value-ll-related-p
                   lambda-lift-top-expr lambda-lift-top-used ll-expr)))

; The transformation depends on its input only up to fixing, so the claim
; holds for every object, not just expressions.

(fty::deffixequiv-mutual lambda-lift-exprs/atoms/binds
  :args ((ll-expr x) (ll-expr-list x) (ll-atom x) (ll-atom-list x)
         (ll-bind x) (ll-let-binds binds)))

(defrule lambda-lift-top-expr-of-expr-fix
  (equal (lambda-lift-top-expr (expr-fix x))
         (lambda-lift-top-expr x))
  :enable (lambda-lift-top-expr lambda-lift-top-used))

(defrule lambda-lift-validation-claim
  (lambda-lift-validation-claim-p expr limit)
  :use ((:instance lambda-lift-top-expr-eval-ok-when-ground
                   (x (expr-fix expr)))
        (:instance lambda-lift-top-expr-eval-ok-p-suff
                   (limit2 (lambda-lift-top-expr-eval-ok-p-witness
                            (expr-fix expr) limit))))
  :enable (lambda-lift-validation-claim-p lambda-lift-top-expr-eval-ok-p)
  :disable (check-sound-p lambda-lift-top-expr-eval-ok-p-suff))
