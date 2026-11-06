; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "lambda-lifting-free-variables")
(include-book "bound-variable-operations")

(include-book "portcullis")

(local (include-book "osets"))
(local (include-book "std/osets/top" :dir :system))

(local (in-theory (disable (:e tau-system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lambda-lifting-placement
  :parents (lambda-lifting)
  :short "Lifted definitions are placed after everything they refer to."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lambda lifting introduces no free expression variables:
     @('expr-free-expr-vars-of-lambda-lift-top-expr') says that the free
     variables of @(tsee lambda-lift-top-expr)'s result are among those of
     its input, and @('bind-list-free-expr-vars-of-lambda-lift-top-binds')
     and @('bind-list-free-expr-vars-of-lambda-lift-file') say the same of
     top-level bindings and of a file's declarations.  The free variables of
     a list of bindings are computed sequentially, as declarations are
     scoped: those of each binding that no binding before it binds.  So these
     theorems say that each lifted definition, and each rebuilt binding,
     refers only to what precedes it in the result (or to what is free in
     the input, such as primitive operations): no lifted definition is placed
     before a definition or declaration it depends on.  The lifted
     definitions' names are fresh (see @(see lambda-lifting-free-variables)),
     so nothing in the result is captured by them.")
   (xdoc::p
    (xdoc::b "Proof."))
   (xdoc::p
    "The traversal is reasoned about one variable @('v') at a time, with
     @('v0') the names in use at the start; the names in use but not in
     @('v0') are then the names of the definitions lifted so far, which
     precede, in the result, the ones still to be lifted.  The invariant
     @(tsee placement-inv) says that @('v'), if in @('v0'), is in use, and
     that if @('v') is free in the replacement of a hoisted function, it is
     the name of a definition lifted before or a local variable.  There are
     three inductions over the traversal: how the bindings of a @(':let')
     change the local names and the keys of the map of hoisted functions
     (@('keys-and-locals-of-ll-let-binds')); the free variables of a
     rebuilt node, which are those of the original node that are not hoisted
     functions, those of their replacements, and names of earlier lifted
     definitions (@('rebuilt-free-vars-of-ll-expr')); and the free
     variables of the lifted definitions, which are the non-local free
     variables of the original node and names of earlier lifted definitions
     (@('lifted-free-vars-of-ll-expr')).  The free variables of the values
     of the map are those of @(tsee string-expr-map-free-expr-vars), which is
     characterized through @('map-values-free-within')."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The free variables of the values of a map from names to expressions.

(defruled expr-free-expr-vars-of-assoc-subset
  (implies (and (string-expr-mapp m)
                (omap::assoc k m))
           (set::subset (expr-free-expr-vars (cdr (omap::assoc k m)))
                        (string-expr-map-free-expr-vars m)))
  :induct (string-expr-map-free-expr-vars m)
  :enable (string-expr-map-free-expr-vars
           omap::assoc-of-tail-when-not-head
           subset-of-union-right-1
           subset-of-union-right-2)
  :expand ((omap::assoc k m)))

(acl2::defun-sk map-values-free-within (m s)
  (forall (k)
          (implies (omap::assoc k m)
                   (set::subset (expr-free-expr-vars (cdr (omap::assoc k m)))
                                s))))

(in-theory (disable map-values-free-within))

(defruled map-values-free-within-of-tail
  (implies (map-values-free-within m s)
           (map-values-free-within (omap::tail m) s))
  :expand ((map-values-free-within (omap::tail m) s))
  :use ((:instance map-values-free-within-necc
                   (k (map-values-free-within-witness (omap::tail m) s)))
        (:instance omap::assoc-of-tail-when-assoc-of-tail
                   (key (map-values-free-within-witness (omap::tail m) s))
                   (map m))))

(defruled expr-free-expr-vars-of-head-val-when-values-free-within
  (implies (and (map-values-free-within m s)
                (not (omap::emptyp m)))
           (set::subset (expr-free-expr-vars (mv-nth 1 (omap::head m))) s))
  :expand ((omap::assoc (mv-nth 0 (omap::head m)) m))
  :use ((:instance map-values-free-within-necc
                   (k (mv-nth 0 (omap::head m))))))

(defruled subset-of-string-expr-map-free-expr-vars-when-values-free-within
  (implies (and (string-expr-mapp m)
                (map-values-free-within m s))
           (set::subset (string-expr-map-free-expr-vars m) s))
  :induct (string-expr-map-free-expr-vars m)
  :enable (string-expr-map-free-expr-vars
           subset-of-union
           map-values-free-within-of-tail
           expr-free-expr-vars-of-head-val-when-values-free-within))


(defrule string-expr-map-free-expr-vars-of-update
  (implies (and (string-expr-mapp m)
                (stringp k)
                (exprp v))
           (set::subset (string-expr-map-free-expr-vars (omap::update k v m))
                        (set::union (expr-free-expr-vars v)
                                    (string-expr-map-free-expr-vars m))))
  :use ((:instance subset-of-string-expr-map-free-expr-vars-when-values-free-within
                   (m (omap::update k v m))
                   (s (set::union (expr-free-expr-vars v)
                                  (string-expr-map-free-expr-vars m))))
        (:instance expr-free-expr-vars-of-assoc-subset
                   (k (map-values-free-within-witness
                       (omap::update k v m)
                       (set::union (expr-free-expr-vars v)
                                   (string-expr-map-free-expr-vars m))))))
  :expand ((map-values-free-within
            (omap::update k v m)
            (set::union (expr-free-expr-vars v)
                        (string-expr-map-free-expr-vars m))))
  :enable (subset-of-union-right-1 subset-of-union-right-2))

(defrule string-expr-map-free-expr-vars-of-delete
  (implies (string-expr-mapp m)
           (set::subset (string-expr-map-free-expr-vars (omap::delete k m))
                        (string-expr-map-free-expr-vars m)))
  :use ((:instance subset-of-string-expr-map-free-expr-vars-when-values-free-within
                   (m (omap::delete k m))
                   (s (string-expr-map-free-expr-vars m)))
        (:instance expr-free-expr-vars-of-assoc-subset
                   (k (map-values-free-within-witness
                       (omap::delete k m)
                       (string-expr-map-free-expr-vars m)))))
  :expand ((map-values-free-within
            (omap::delete k m)
            (string-expr-map-free-expr-vars m))))

(defruled subset-of-free-expr-vars-of-delete-when-subset
  (implies (set::subset (string-expr-map-free-expr-vars m) s)
           (set::subset (string-expr-map-free-expr-vars
                         (omap::delete k (string-expr-map-fix m)))
                        s))
  :use ((:instance string-expr-map-free-expr-vars-of-delete
                   (m (string-expr-map-fix m)))
        (:instance set::subset-transitive
                   (set::x (string-expr-map-free-expr-vars
                            (omap::delete k (string-expr-map-fix m))))
                   (set::y (string-expr-map-free-expr-vars m))
                   (set::z s)))
  :disable string-expr-map-free-expr-vars-of-delete)

(defruled string-expr-map-free-expr-vars-of-remove-keys-when-subset
  (implies (set::subset (string-expr-map-free-expr-vars map) s)
           (set::subset (string-expr-map-free-expr-vars
                         (string-expr-map-remove-keys keys map))
                        s))
  :induct (string-expr-map-remove-keys keys map)
  :enable (string-expr-map-remove-keys
           subset-of-free-expr-vars-of-delete-when-subset))

(defrule string-expr-map-free-expr-vars-of-string-expr-map-remove-keys
  (set::subset (string-expr-map-free-expr-vars
                (string-expr-map-remove-keys keys map))
               (string-expr-map-free-expr-vars map))
  :use ((:instance string-expr-map-free-expr-vars-of-remove-keys-when-subset
                   (s (string-expr-map-free-expr-vars map)))))

(defrule keys-of-string-expr-map-remove-keys-superset
  (set::subset (set::difference (omap::keys (string-expr-map-fix map))
                                (set::mergesort (str::string-list-fix keys)))
               (omap::keys (string-expr-map-remove-keys keys map)))
  :enable (set::pick-a-point-subset-strategy
           omap::in-of-keys-to-assoc))


; Sequential free variables of bindings.

(defruled in-of-bind-list-free-expr-vars-of-append
  (equal (set::in v (bind-list-free-expr-vars (append a b)))
         (or (set::in v (bind-list-free-expr-vars a))
             (and (set::in v (bind-list-free-expr-vars b))
                  (not (set::in v (bind-list-bound-expr-vars a))))))
  :induct (len a)
  :enable (len append bind-list-bound-expr-vars)
  :expand ((:free (x y) (bind-list-free-expr-vars (cons x y)))
           (bind-list-free-expr-vars a)
           (bind-list-free-expr-vars nil)))

; One-step SETP rule for the fold, for SET::DOUBLE-CONTAINMENT, whose
; SETP hypotheses are relieved with a limited backchain.

(defrule setp-of-bind-list-free-expr-vars
  (set::setp (bind-list-free-expr-vars x)))

(defrule bind-list-free-expr-vars-of-list
  (equal (bind-list-free-expr-vars (list b))
         (bind-free-expr-vars b))
  :expand ((bind-list-free-expr-vars (list b))
           (bind-list-free-expr-vars nil)))

(defrule bind-list-bound-expr-vars-of-list
  (equal (bind-list-bound-expr-vars (list b))
         (bind-bound-expr-vars b))
  :enable bind-list-bound-expr-vars)

(defruled in-of-expr-free-expr-vars-of-nest-let-binds
  (equal (set::in v (expr-free-expr-vars (nest-let-binds binds body)))
         (or (set::in v (bind-list-free-expr-vars binds))
             (and (set::in v (expr-free-expr-vars body))
                  (not (set::in v (bind-list-bound-expr-vars binds))))))
  :induct (nest-let-binds binds body)
  :enable (nest-let-binds bind-list-bound-expr-vars)
  :expand ((:free (bs b) (expr-free-expr-vars (expr-let bs b)))
           (:free (x y) (bind-list-free-expr-vars (cons x y)))
           (:free (x y) (bind-list-bound-expr-vars (cons x y)))
           (bind-list-free-expr-vars binds)
           (bind-list-free-expr-vars nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The parameters that captured variables become have those variables'
; names.

(defrule var+type?-list->var-of-names-to-params
  (equal (var+type?-list->var (names-to-params names tenv))
         (str::string-list-fix names))
  :induct (names-to-params names tenv)
  :enable (names-to-params str::string-list-fix))

(defrule member-of-var+type?-list->var-of-append
  (iff (member-equal a (var+type?-list->var (append x y)))
       (or (member-equal a (var+type?-list->var x))
           (member-equal a (var+type?-list->var y))))
  :induct (len x)
  :enable (len append var+type?-list->var))

(defrule member-of-string-list-fix-when-string-setp
  (implies (string-setp s)
           (iff (member-equal a (str::string-list-fix s))
                (set::in a s)))
  :use ((:instance mergesort-of-string-list-fix-when-string-setp)
        (:instance set::in-mergesort (set::a a) (set::x (str::string-list-fix s))))
  :disable (mergesort-of-string-list-fix-when-string-setp set::in-mergesort))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A lifted lambda's definition refers to the non-local free variables of
; the lambda: its captured variables, the local free ones, are parameters.

(defrulel consp-of-intersect-of-difference-when-in
  (implies (and (set::in x a)
                (not (set::in x c))
                (set::in x b))
           (consp (set::intersect (set::difference a c) b)))
  :use ((:instance set::never-in-empty
                   (set::a x)
                   (set::x (set::intersect (set::difference a c) b))))
  :enable set::emptyp
  :disable (set::intersect-under-set-equiv
            set::difference-under-set-equiv
            acl2::set-equiv-implies-equal-consp-1))

(defrulel consp-of-names-to-params
  (equal (consp (names-to-params names tenv))
         (consp names))
  :expand ((names-to-params names tenv)))

(defrule bind-list-free-expr-vars-of-lifted-of-emit-lifted-lambda
  (set::subset (bind-list-free-expr-vars
                (mv-nth 1 (emit-lifted-lambda params body type? tenv locals used)))
               (set::difference
                (set::difference (expr-free-expr-vars body)
                                 (set::mergesort (var+type?-list->var params)))
                locals))
  :cases ((consp (mv-nth 1 (emit-lifted-lambda params body type? tenv locals used))))
  :enable (emit-lifted-lambda set::pick-a-point-subset-strategy)
  :disable (set::intersect-under-set-equiv
            set::difference-under-set-equiv
            set::mergesort-under-set-equiv)
  :expand ((:free (v ps ty e) (bind-free-expr-vars (bind-fun v ps ty e)))))

; A hoisted function's definition likewise refers to the non-local free
; variables of the function, and its replacement to its name and the local
; ones.

(defrule hoist-local-fun-free-expr-vars-when-hoisted
  (implies (mv-nth 0 (hoist-local-fun b rebound tenv locals used))
           (and (set::subset
                 (bind-free-expr-vars
                  (mv-nth 2 (hoist-local-fun b rebound tenv locals used)))
                 (set::difference (bind-free-expr-vars b) locals))
                (set::subset
                 (expr-free-expr-vars
                  (mv-nth 3 (hoist-local-fun b rebound tenv locals used)))
                 (set::insert (fresh-expr-var (bind-fun->var b) (string-sfix used))
                              (set::intersect (bind-free-expr-vars b)
                                              locals)))))
  :enable (hoist-local-fun set::pick-a-point-subset-strategy)
  :expand ((bind-free-expr-vars b)
           (:free (v ps ty e) (bind-free-expr-vars (bind-fun v ps ty e)))
           (:free (n) (expr-free-expr-vars (expr-var n)))))


; Membership forms of the facts above, for the traversal proofs, which
; reason about one variable at a time.

(defruled in-fv-of-assoc
  (implies (and (string-expr-mapp m)
                (omap::assoc k m)
                (set::in v (expr-free-expr-vars (cdr (omap::assoc k m)))))
           (set::in v (string-expr-map-free-expr-vars m)))
  :use (expr-free-expr-vars-of-assoc-subset
        (:instance set::subset-in
                   (set::a v)
                   (set::x (expr-free-expr-vars (cdr (omap::assoc k m))))
                   (set::y (string-expr-map-free-expr-vars m)))))

(defruled in-fv-of-update
  (implies (and (string-expr-mapp m)
                (stringp k)
                (exprp val)
                (set::in v (string-expr-map-free-expr-vars (omap::update k val m))))
           (or (set::in v (expr-free-expr-vars val))
               (set::in v (string-expr-map-free-expr-vars m))))
  :use ((:instance string-expr-map-free-expr-vars-of-update (v val))
        (:instance set::subset-in
                   (set::a v)
                   (set::x (string-expr-map-free-expr-vars (omap::update k val m)))
                   (set::y (set::union (expr-free-expr-vars val)
                                       (string-expr-map-free-expr-vars m)))))
  :disable string-expr-map-free-expr-vars-of-update)

(defruled in-fv-of-remove-keys
  (implies (set::in v (string-expr-map-free-expr-vars
                       (string-expr-map-remove-keys keys m)))
           (set::in v (string-expr-map-free-expr-vars m)))
  :use ((:instance string-expr-map-free-expr-vars-of-string-expr-map-remove-keys (map m))
        (:instance set::subset-in
                   (set::a v)
                   (set::x (string-expr-map-free-expr-vars
                            (string-expr-map-remove-keys keys m)))
                   (set::y (string-expr-map-free-expr-vars m))))
  :disable string-expr-map-free-expr-vars-of-string-expr-map-remove-keys)

(defruled in-keys-of-remove-keys
  (equal (set::in v (omap::keys (string-expr-map-remove-keys keys m)))
         (and (set::in v (omap::keys (string-expr-map-fix m)))
              (not (member-equal v (str::string-list-fix keys)))))
  :enable omap::in-of-keys-to-assoc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The lifting step and the hoisting step, a variable at a time.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A lambda whose body is a lambda has the free variables of the inner
; body less all the parameters.

(defruled in-of-free-of-nested-lambda-body
  (b* (((mv nestedp more inner &) (nested-lambda body)))
    (implies nestedp
             (equal (set::in v (expr-free-expr-vars body))
                    (and (set::in v (expr-free-expr-vars inner))
                         (not (member-equal v (var+type?-list->var more)))))))
  :enable nested-lambda
  :expand ((expr-free-expr-vars body)
           (atom-free-expr-vars (expr-atom->atom body))))


; The names in use grow by exactly the names of the definitions lifted out:
; those, and the input names, are the names in use afterwards.

(defrule in-new-used-of-emit-lifted-lambda
  (equal (set::in v (mv-nth 2 (emit-lifted-lambda params body type?
                                                  tenv locals used)))
         (or (set::in v (string-sfix used))
             (set::in v (bind-list-bound-expr-vars
                         (mv-nth 1 (emit-lifted-lambda params body type?
                                                       tenv locals used))))))
  :cases ((consp (mv-nth 1 (emit-lifted-lambda params body type?
                                               tenv locals used)))))

(defret-mutual in-new-used-of-lambda-lift-exprs/atoms/binds
  (defret in-new-used-of-ll-expr
    (equal (set::in v new-used)
           (or (set::in v (string-sfix used))
               (set::in v (bind-list-bound-expr-vars lifted))))
    :fn ll-expr)
  (defret in-new-used-of-ll-lambda
    (equal (set::in v new-used)
           (or (set::in v (string-sfix used))
               (set::in v (bind-list-bound-expr-vars lifted))))
    :fn ll-lambda)
  (defret in-new-used-of-ll-let-binds
    (equal (set::in v new-used)
           (or (set::in v (string-sfix used))
               (set::in v (bind-list-bound-expr-vars lifted))))
    :fn ll-let-binds)
  (defret in-new-used-of-ll-expr-list
    (equal (set::in v new-used)
           (or (set::in v (string-sfix used))
               (set::in v (bind-list-bound-expr-vars lifted))))
    :fn ll-expr-list)
  (defret in-new-used-of-ll-atom
    (equal (set::in v new-used)
           (or (set::in v (string-sfix used))
               (set::in v (bind-list-bound-expr-vars lifted))))
    :fn ll-atom)
  (defret in-new-used-of-ll-atom-list
    (equal (set::in v new-used)
           (or (set::in v (string-sfix used))
               (set::in v (bind-list-bound-expr-vars lifted))))
    :fn ll-atom-list)
  (defret in-new-used-of-ll-bind
    (equal (set::in v new-used)
           (or (set::in v (string-sfix used))
               (set::in v (bind-list-bound-expr-vars lifted))))
    :fn ll-bind)
  :mutual-recursion lambda-lift-exprs/atoms/binds
  :hints (("Goal" :in-theory (e/d (bind-list-bound-expr-vars)
                                  (emit-lifted-lambda hoist-local-fun apply-to-names
                            no-duplicatesp-equal-when-no-duplicatesp-equal-of-type-var-list->name
                            no-duplicatesp-equal-when-no-duplicatesp-equal-of-ispace-var-list->name
                            no-duplicatesp-equal-when-not-duplicated-names
                            duplicated-names-when-no-duplicatesp-equal
                            member-equal-of-type-var-list->name-when-member-equal
                            member-equal-of-ispace-var-list->name-when-member-equal
                            member-of-type-var->name-in-type-var-list->name
                            member-of-ispace-var->name-in-ispace-var-list->name
                            cdr-of-type-var-list->name
                            cdr-of-ispace-var-list->name
                            type-var-list->name-when-not-consp
                            ispace-var-list->name-when-not-consp
                            consp-of-type-var-list->name
                            consp-of-ispace-var-list->name
                            acl2::utf8-table36-length-lemmas
                            acl2::subsetp-car-member
                            acl2::subsetp-when-atom-right))
           :expand ((ll-expr x tenv tlets locals lmap used)
                    (:free (type?) (ll-lambda params body type? tenv tlets locals lmap used))
                    (ll-let-binds binds body-binders tenv tlets locals lmap used)
                    (ll-expr-list x tenv tlets locals lmap used)
                    (ll-atom x tenv tlets locals lmap used)
                    (ll-atom-list x tenv tlets locals lmap used)
                    (ll-bind x tenv tlets locals lmap used)
                    (ll-bind (bind-fix (car binds)) tenv tlets locals lmap used)
                    (ll-expr (car x) tenv tlets locals lmap used)
                    (ll-atom (car x) tenv tlets locals lmap used)))))


(defrule bind-bound-expr-vars-of-ll-bind
  (equal (bind-bound-expr-vars (mv-nth 0 (ll-bind x tenv tlets locals lmap used)))
         (bind-bound-expr-vars x))
  :expand ((ll-bind x tenv tlets locals lmap used))
  :enable bind-bound-expr-vars)

(defrule bind-free-expr-vars-of-bind-fix
  (equal (bind-free-expr-vars (bind-fix x))
         (bind-free-expr-vars x))
  :expand ((bind-free-expr-vars x)
           (bind-free-expr-vars (bind-fix x))))

(defruled bind-bound-expr-vars-when-fun
  (implies (equal (bind-kind b) :fun)
           (equal (bind-bound-expr-vars b)
                  (set::insert (bind-fun->var b) nil)))
  :enable bind-bound-expr-vars)

; A binding that is hoisted binds the name of the function it defines.

(defruled bind-bound-expr-vars-when-ll-bind-hoisted
  (implies (mv-nth 0 (hoist-local-fun
                      (mv-nth 0 (ll-bind (bind-fix x) tenv tlets locals lmap used))
                      rebound tenv2 locals2 used2))
           (equal (bind-bound-expr-vars x)
                  (set::insert (bind-fun->var
                                (mv-nth 0 (ll-bind (bind-fix x) tenv tlets locals lmap used)))
                               nil)))
  :use ((:instance hoist-local-fun-when-hoisted
                   (b (mv-nth 0 (ll-bind (bind-fix x) tenv tlets locals lmap used)))
                   (tenv tenv2) (locals locals2) (used used2))
        (:instance bind-bound-expr-vars-when-fun
                   (b (mv-nth 0 (ll-bind (bind-fix x) tenv tlets locals lmap used))))
        (:instance bind-bound-expr-vars-of-ll-bind (x (bind-fix x))))
  :disable (hoist-local-fun-when-hoisted bind-bound-expr-vars-of-ll-bind))

; Stage A: how the bindings of a :LET change the local names and the map of
; hoisted functions.  A name bound by a binding that is not kept is a key of
; the map afterwards, and so is a key that is not bound again.

(defret-mutual keys-and-locals-of-ll-let-binds
  (defret keys-and-locals-of-ll-let-binds
    (implies (string-expr-mapp lmap)
             (and (equal (set::in v new-locals)
                         (or (set::in v (string-sfix locals))
                             (set::in v (bind-list-bound-expr-vars binds))))
                  (implies (and (set::in v (omap::keys lmap))
                                (not (set::in v (bind-list-bound-expr-vars binds))))
                           (set::in v (omap::keys new-lmap)))
                  (implies (and (set::in v (bind-list-bound-expr-vars binds))
                                (not (set::in v (bind-list-bound-expr-vars kept))))
                           (set::in v (omap::keys new-lmap)))))
    :fn ll-let-binds)
  :skip-others t
  :mutual-recursion lambda-lift-exprs/atoms/binds
  :hints (("Goal"
           :in-theory (e/d (ll-let-binds
                            bind-list-bound-expr-vars
                            in-keys-of-remove-keys
                            bind-bound-expr-vars-when-ll-bind-hoisted)
                           (emit-lifted-lambda
                            hoist-local-fun
                            apply-to-names
                            liftable-lambda-p
                            ll-bind
                            bind-bound-expr-vars)))))


; The invariant of the traversal, for one variable V: if V is one of the
; names V0 in use at the start, it is in use now; and if V is free in the
; replacement of a hoisted function, it is either the name of a definition
; lifted before (in use but not in V0) or local.

(define placement-inv (v v0 used locals lmap)
  :parents (lambda-lifting-placement)
  :short "The per-variable invariant of the placement traversal."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the variable is one of the names in use at the start,
     it is in use now;
     and if it is free in the replacement of a hoisted function,
     it is either the name of a definition lifted before
     (in use but not among the names in use at the start) or local."))
  :verify-guards nil
  (and (implies (set::in v v0) (set::in v used))
       (implies (set::in v (string-expr-map-free-expr-vars lmap))
                (or (and (set::in v used) (not (set::in v v0)))
                    (set::in v locals)))))

(defruled not-in-v0-when-placement-inv
  (implies (and (placement-inv v v0 used locals lmap)
                (not (set::in v used)))
           (not (set::in v v0)))
  :enable placement-inv)

(defruled in-used-when-placement-inv-and-in-fv
  (implies (and (placement-inv v v0 used locals lmap)
                (set::in v (string-expr-map-free-expr-vars lmap))
                (not (set::in v locals)))
           (and (set::in v used)
                (not (set::in v v0))))
  :enable placement-inv)

(defrule placement-inv-of-nil-map
  (implies (implies (set::in v v0) (set::in v used))
           (placement-inv v v0 used locals nil))
  :enable placement-inv
  :expand ((string-expr-map-free-expr-vars nil)))

; The fresh names of the lifting and hoisting steps are not in use before
; the steps.

(defrule fresh-of-ll-expr-not-in-used
  (implies (string-setp used)
           (not (set::in (fresh-expr-var prefix
                                         (string-sfix
                                          (mv-nth 2 (ll-expr x tenv tlets locals lmap used))))
                         used)))
  :use ((:instance fresh-expr-var-is-fresh
                   (used (mv-nth 2 (ll-expr x tenv tlets locals lmap used))))
        (:instance in-new-used-of-ll-expr
                   (v (fresh-expr-var prefix
                                      (string-sfix
                                       (mv-nth 2 (ll-expr x tenv tlets locals lmap used))))))))

(defrule fresh-of-ll-bind-not-in-used
  (implies (string-setp used)
           (not (set::in (fresh-expr-var prefix
                                         (string-sfix
                                          (mv-nth 2 (ll-bind x tenv tlets locals lmap used))))
                         used)))
  :use ((:instance fresh-expr-var-is-fresh
                   (used (mv-nth 2 (ll-bind x tenv tlets locals lmap used))))
        (:instance in-new-used-of-ll-bind
                   (v (fresh-expr-var prefix
                                      (string-sfix
                                       (mv-nth 2 (ll-bind x tenv tlets locals lmap used))))))))

(defrule in-locals-with-params
  (equal (set::in v (locals-with-params params locals))
         (or (and (member-equal v (var+type?-list->var params)) t)
             (set::in v (string-sfix locals))))
  :enable locals-with-params)


; The invariant carries over to a call with more names in use and more local
; names, and with the map unchanged or with keys removed from it.

(defruled placement-inv-when-more-used-and-locals
  (implies (and (placement-inv v v0 used locals lmap)
                (implies (set::in v used) (set::in v used2))
                (implies (set::in v locals) (set::in v locals2)))
           (placement-inv v v0 used2 locals2 lmap))
  :enable placement-inv)

(defruled placement-inv-of-remove-keys-when-more-used-and-locals
  (implies (and (placement-inv v v0 used locals lmap)
                (implies (set::in v used) (set::in v used2))
                (implies (set::in v locals) (set::in v locals2)))
           (placement-inv v v0 used2 locals2 (string-expr-map-remove-keys keys lmap)))
  :enable (placement-inv in-fv-of-remove-keys))


; Exact membership forms of the lifting and hoisting steps, which rewrite
; into case splits (the forms above, with disjunctive conclusions, do not
; serve as rewrite rules).

(defruled in-free-of-lifted-of-emit-lifted-lambda
  (equal (set::in v (bind-list-free-expr-vars
                     (mv-nth 1 (emit-lifted-lambda params body type? tenv locals used))))
         (and (consp (mv-nth 1 (emit-lifted-lambda params body type? tenv locals used)))
              (set::in v (expr-free-expr-vars body))
              (not (member-equal v (var+type?-list->var params)))
              (not (set::in v locals))))
  :cases ((consp (mv-nth 1 (emit-lifted-lambda params body type? tenv locals used))))
  :enable emit-lifted-lambda
  :disable (set::intersect-under-set-equiv
            set::difference-under-set-equiv
            set::mergesort-under-set-equiv)
  :expand ((:free (w ps ty e) (bind-free-expr-vars (bind-fun w ps ty e)))))

(defruled in-free-of-e-of-emit-lifted-lambda
  (equal (set::in v (expr-free-expr-vars
                     (mv-nth 0 (emit-lifted-lambda params body type? tenv locals used))))
         (if (consp (mv-nth 1 (emit-lifted-lambda params body type? tenv locals used)))
             (or (equal v (fresh-expr-var "lam_" (string-sfix used)))
                 (and (set::in v (expr-free-expr-vars body))
                      (not (member-equal v (var+type?-list->var params)))
                      (set::in v locals)))
           (and (set::in v (expr-free-expr-vars body))
                (not (member-equal v (var+type?-list->var params))))))
  :cases ((consp (mv-nth 1 (emit-lifted-lambda params body type? tenv locals used))))
  :enable (emit-lifted-lambda make-atom-lambda/lambdan len)
  :disable (set::intersect-under-set-equiv
            set::difference-under-set-equiv
            set::mergesort-under-set-equiv)
  :expand ((len params)
           (len (cdr params))
           (:free (n) (expr-free-expr-vars (expr-var n)))
           (:free (a) (expr-free-expr-vars (expr-atom a)))
           (:free (p b ty) (atom-free-expr-vars (atom-lambda p b ty)))
           (:free (ps b ty) (atom-free-expr-vars (atom-lambdan ps b ty)))))

(defruled in-free-of-hoisted-of-hoist-local-fun
  (implies (mv-nth 0 (hoist-local-fun b rebound tenv locals used))
           (equal (set::in v (bind-free-expr-vars
                              (mv-nth 2 (hoist-local-fun b rebound tenv locals used))))
                  (and (set::in v (bind-free-expr-vars b))
                       (not (set::in v locals)))))
  :enable hoist-local-fun
  :expand ((bind-free-expr-vars b)
           (:free (w ps ty e) (bind-free-expr-vars (bind-fun w ps ty e)))))

(defruled in-free-of-replacement-of-hoist-local-fun
  (implies (mv-nth 0 (hoist-local-fun b rebound tenv locals used))
           (equal (set::in v (expr-free-expr-vars
                              (mv-nth 3 (hoist-local-fun b rebound tenv locals used))))
                  (or (equal v (fresh-expr-var (bind-fun->var b) (string-sfix used)))
                      (and (set::in v (bind-free-expr-vars b))
                           (set::in v locals)))))
  :enable hoist-local-fun
  :expand ((bind-free-expr-vars b)
           (:free (n) (expr-free-expr-vars (expr-var n)))))

; The invariant after a binding is hoisted: the new names in use are the
; fresh name and those of the definitions lifted out of the binding, the
; hoisted function's name is local, and its replacement refers to the
; fresh name and to local names.

(defruled placement-inv-of-hoisting
  (b* ((new-b (mv-nth 0 (ll-bind b tenv tlets locals lmap used)))
       (used1 (mv-nth 2 (ll-bind b tenv tlets locals lmap used))))
    (implies (and (placement-inv v v0 used locals lmap)
                  (string-setp used)
                  (string-setp locals)
                  (string-expr-mapp lmap)
                  (mv-nth 0 (hoist-local-fun new-b rebound tenv locals used1)))
             (placement-inv
              v v0
              (set::insert (fresh-expr-var (bind-fun->var new-b) used1) used1)
              (set::insert (bind-fun->var new-b) locals)
              (omap::update (bind-fun->var new-b)
                            (mv-nth 3 (hoist-local-fun new-b rebound tenv locals used1))
                            lmap))))
  :enable (placement-inv in-free-of-replacement-of-hoist-local-fun)
  :use ((:instance in-fv-of-update
                   (m lmap)
                   (k (bind-fun->var (mv-nth 0 (ll-bind b tenv tlets locals lmap used))))
                   (val (mv-nth 3 (hoist-local-fun
                                   (mv-nth 0 (ll-bind b tenv tlets locals lmap used))
                                   rebound tenv locals
                                   (mv-nth 2 (ll-bind b tenv tlets locals lmap used))))))
        (:instance fresh-of-ll-bind-not-in-used
                   (x b)
                   (prefix (bind-fun->var (mv-nth 0 (ll-bind b tenv tlets locals lmap used)))))))


; The fresh names, in the form in which they appear in goals (the used sets
; are sets of strings, so their fixing is dropped).

(defrule fresh-of-ll-expr-not-in-used-unfixed
  (implies (string-setp used)
           (not (set::in (fresh-expr-var prefix
                                         (mv-nth 2 (ll-expr x tenv tlets locals lmap used)))
                         used)))
  :use fresh-of-ll-expr-not-in-used)

(defrule fresh-of-ll-bind-not-in-used-unfixed
  (implies (string-setp used)
           (not (set::in (fresh-expr-var prefix
                                         (mv-nth 2 (ll-bind x tenv tlets locals lmap used)))
                         used)))
  :use fresh-of-ll-bind-not-in-used)

; The invariant after a binding is hoisted, with the new names in use, local
; names, key, and value given by equations, so that it applies whatever
; form the goal has put them in.

(defruled placement-inv-of-hoisting-gen
  (implies (and (placement-inv v v0 used locals lmap)
                (mv-nth 0 (hoist-local-fun
                           (mv-nth 0 (ll-bind b tenv tlets locals lmap used))
                           rebound tenv locals
                           (mv-nth 2 (ll-bind b tenv tlets locals lmap used))))
                (string-setp used)
                (string-setp locals)
                (string-expr-mapp lmap)
                (equal used2
                       (set::insert (fresh-expr-var
                                     (bind-fun->var (mv-nth 0 (ll-bind b tenv tlets locals lmap used)))
                                     (mv-nth 2 (ll-bind b tenv tlets locals lmap used)))
                                    (mv-nth 2 (ll-bind b tenv tlets locals lmap used))))
                (equal locals2
                       (set::insert (bind-fun->var (mv-nth 0 (ll-bind b tenv tlets locals lmap used)))
                                    locals))
                (equal k (bind-fun->var (mv-nth 0 (ll-bind b tenv tlets locals lmap used))))
                (equal val (mv-nth 3 (hoist-local-fun
                                      (mv-nth 0 (ll-bind b tenv tlets locals lmap used))
                                      rebound tenv locals
                                      (mv-nth 2 (ll-bind b tenv tlets locals lmap used))))))
           (placement-inv v v0 used2 locals2 (omap::update k val lmap)))
  :use placement-inv-of-hoisting)


; A key of the map stays a key after the bindings of a :LET unless a kept
; binding binds it again.

(defrule in-keys-of-ll-let-binds-unless-kept
  (b* (((mv kept & & & new-lmap &)
        (ll-let-binds binds body-binders tenv tlets locals lmap used)))
    (implies (and (string-expr-mapp lmap)
                  (set::in v (omap::keys lmap))
                  (not (set::in v (bind-list-bound-expr-vars kept))))
             (set::in v (omap::keys new-lmap))))
  :cases ((set::in v (bind-list-bound-expr-vars binds)))
  :use keys-and-locals-of-ll-let-binds
  :disable keys-and-locals-of-ll-let-binds)

; A lambda that lifting handles is a lambda.

; The names of the lifted definitions were not in use before, a variable at
; a time.

(defruled not-in-used-when-in-lifted-of-ll-expr
  (implies (set::in v (bind-list-bound-expr-vars
                       (mv-nth 1 (ll-expr x tenv tlets locals lmap used))))
           (not (set::in v (string-sfix used))))
  :use (used-of-ll-expr
        (:instance set::never-in-empty
                   (set::a v)
                   (set::x (set::intersect
                            (bind-list-bound-expr-vars
                             (mv-nth 1 (ll-expr x tenv tlets locals lmap used)))
                            (string-sfix used)))))
  :disable used-of-ll-expr)

(defruled not-in-used-when-in-lifted-of-ll-bind
  (implies (set::in v (bind-list-bound-expr-vars
                       (mv-nth 1 (ll-bind x tenv tlets locals lmap used))))
           (not (set::in v (string-sfix used))))
  :use (used-of-ll-bind
        (:instance set::never-in-empty
                   (set::a v)
                   (set::x (set::intersect
                            (bind-list-bound-expr-vars
                             (mv-nth 1 (ll-bind x tenv tlets locals lmap used)))
                            (string-sfix used)))))
  :disable used-of-ll-bind)

(defruled not-in-used-when-in-lifted-of-ll-let-binds
  (implies (set::in v (bind-list-bound-expr-vars
                       (mv-nth 1 (ll-let-binds binds body-binders tenv tlets locals lmap used))))
           (not (set::in v (string-sfix used))))
  :use (used-of-ll-let-binds
        (:instance set::never-in-empty
                   (set::a v)
                   (set::x (set::intersect
                            (bind-list-bound-expr-vars
                             (mv-nth 1 (ll-let-binds binds body-binders
                                                     tenv tlets locals lmap used)))
                            (string-sfix used)))))
  :disable used-of-ll-let-binds)

(defruled not-in-used-when-in-lifted-of-ll-lambda
  (implies (set::in v (bind-list-bound-expr-vars
                       (mv-nth 1 (ll-lambda params body type? tenv tlets locals lmap used))))
           (not (set::in v (string-sfix used))))
  :use (used-of-ll-lambda
        (:instance set::never-in-empty
                   (set::a v)
                   (set::x (set::intersect
                            (bind-list-bound-expr-vars
                             (mv-nth 1 (ll-lambda params body type? tenv tlets locals lmap used)))
                            (string-sfix used)))))
  :disable used-of-ll-lambda)

(defruled not-in-used-when-in-lifted-of-ll-expr-list
  (implies (set::in v (bind-list-bound-expr-vars
                       (mv-nth 1 (ll-expr-list x tenv tlets locals lmap used))))
           (not (set::in v (string-sfix used))))
  :use (used-of-ll-expr-list
        (:instance set::never-in-empty
                   (set::a v)
                   (set::x (set::intersect
                            (bind-list-bound-expr-vars
                             (mv-nth 1 (ll-expr-list x tenv tlets locals lmap used)))
                            (string-sfix used)))))
  :disable used-of-ll-expr-list)

(defruled not-in-used-when-in-lifted-of-ll-atom
  (implies (set::in v (bind-list-bound-expr-vars
                       (mv-nth 1 (ll-atom x tenv tlets locals lmap used))))
           (not (set::in v (string-sfix used))))
  :use (used-of-ll-atom
        (:instance set::never-in-empty
                   (set::a v)
                   (set::x (set::intersect
                            (bind-list-bound-expr-vars
                             (mv-nth 1 (ll-atom x tenv tlets locals lmap used)))
                            (string-sfix used)))))
  :disable used-of-ll-atom)

(defruled not-in-used-when-in-lifted-of-ll-atom-list
  (implies (set::in v (bind-list-bound-expr-vars
                       (mv-nth 1 (ll-atom-list x tenv tlets locals lmap used))))
           (not (set::in v (string-sfix used))))
  :use (used-of-ll-atom-list
        (:instance set::never-in-empty
                   (set::a v)
                   (set::x (set::intersect
                            (bind-list-bound-expr-vars
                             (mv-nth 1 (ll-atom-list x tenv tlets locals lmap used)))
                            (string-sfix used)))))
  :disable used-of-ll-atom-list)


; As above, with the freshness of the generated name attached to the
; variable, so that it is available whatever the variable is rewritten to.

(defruled in-free-of-e-of-emit-lifted-lambda-2
  (equal (set::in v (expr-free-expr-vars
                     (mv-nth 0 (emit-lifted-lambda params body type? tenv locals used))))
         (if (consp (mv-nth 1 (emit-lifted-lambda params body type? tenv locals used)))
             (or (and (equal v (fresh-expr-var "lam_" (string-sfix used)))
                      (not (set::in v (string-sfix used))))
                 (and (set::in v (expr-free-expr-vars body))
                      (not (member-equal v (var+type?-list->var params)))
                      (set::in v locals)))
           (and (set::in v (expr-free-expr-vars body))
                (not (member-equal v (var+type?-list->var params))))))
  :use in-free-of-e-of-emit-lifted-lambda)

(defruled in-free-of-replacement-of-hoist-local-fun-2
  (implies (mv-nth 0 (hoist-local-fun b rebound tenv locals used))
           (equal (set::in v (expr-free-expr-vars
                              (mv-nth 3 (hoist-local-fun b rebound tenv locals used))))
                  (or (and (equal v (fresh-expr-var (bind-fun->var b) (string-sfix used)))
                           (not (set::in v (string-sfix used))))
                      (and (set::in v (bind-free-expr-vars b))
                           (set::in v locals)))))
  :use in-free-of-replacement-of-hoist-local-fun)


; The free variables of the values of an updated map, exactly: those of the
; new value and those of the other values.

(defruled string-expr-map-free-expr-vars-of-update-subset-1
  (implies (and (string-expr-mapp m)
                (stringp k)
                (exprp val))
           (set::subset (string-expr-map-free-expr-vars (omap::update k val m))
                        (set::union (expr-free-expr-vars val)
                                    (string-expr-map-free-expr-vars
                                     (omap::delete k m)))))
  :use ((:instance subset-of-string-expr-map-free-expr-vars-when-values-free-within
                   (m (omap::update k val m))
                   (s (set::union (expr-free-expr-vars val)
                                  (string-expr-map-free-expr-vars
                                   (omap::delete k m)))))
        (:instance expr-free-expr-vars-of-assoc-subset
                   (m (omap::delete k m))
                   (k (map-values-free-within-witness
                       (omap::update k val m)
                       (set::union (expr-free-expr-vars val)
                                   (string-expr-map-free-expr-vars
                                    (omap::delete k m)))))))
  :expand ((map-values-free-within
            (omap::update k val m)
            (set::union (expr-free-expr-vars val)
                        (string-expr-map-free-expr-vars (omap::delete k m)))))
  :enable (subset-of-union-right-1 subset-of-union-right-2))

(defruled string-expr-map-free-expr-vars-of-update-subset-2
  (implies (and (string-expr-mapp m)
                (stringp k)
                (exprp val))
           (set::subset (string-expr-map-free-expr-vars (omap::delete k m))
                        (string-expr-map-free-expr-vars (omap::update k val m))))
  :use ((:instance subset-of-string-expr-map-free-expr-vars-when-values-free-within
                   (m (omap::delete k m))
                   (s (string-expr-map-free-expr-vars (omap::update k val m))))
        (:instance expr-free-expr-vars-of-assoc-subset
                   (m (omap::update k val m))
                   (k (map-values-free-within-witness
                       (omap::delete k m)
                       (string-expr-map-free-expr-vars (omap::update k val m))))))
  :expand ((map-values-free-within
            (omap::delete k m)
            (string-expr-map-free-expr-vars (omap::update k val m)))))

(defruled in-fv-of-update-equal
  (implies (and (string-expr-mapp m)
                (stringp k)
                (exprp val))
           (equal (set::in v (string-expr-map-free-expr-vars (omap::update k val m)))
                  (or (set::in v (expr-free-expr-vars val))
                      (set::in v (string-expr-map-free-expr-vars (omap::delete k m))))))
  :use (string-expr-map-free-expr-vars-of-update-subset-1
        string-expr-map-free-expr-vars-of-update-subset-2
        (:instance set::subset-in
                   (set::a v)
                   (set::x (string-expr-map-free-expr-vars (omap::update k val m)))
                   (set::y (set::union (expr-free-expr-vars val)
                                       (string-expr-map-free-expr-vars
                                        (omap::delete k m)))))
        (:instance set::subset-in
                   (set::a v)
                   (set::x (string-expr-map-free-expr-vars (omap::delete k m)))
                   (set::y (string-expr-map-free-expr-vars (omap::update k val m))))
        (:instance in-fv-of-assoc
                   (m (omap::update k val m)))))

(defruled in-fv-when-in-fv-of-delete
  (implies (and (set::in v (string-expr-map-free-expr-vars (omap::delete k m)))
                (string-expr-mapp m))
           (set::in v (string-expr-map-free-expr-vars m)))
  :use (string-expr-map-free-expr-vars-of-delete
        (:instance set::subset-in
                   (set::a v)
                   (set::x (string-expr-map-free-expr-vars (omap::delete k m)))
                   (set::y (string-expr-map-free-expr-vars m))))
  :disable string-expr-map-free-expr-vars-of-delete)


; Stage B: a variable free in a rebuilt node is free in the original node
; and not a hoisted function's name (whose uses are replaced), or free in a
; replacement, or the name of a definition lifted before.  For the bindings
; of a :LET, the same holds of the kept bindings and of the replacements
; recorded in the map, and the invariant holds for the body.

(defret-mutual rebuilt-free-vars-of-lambda-lift-exprs/atoms/binds
  (defret rebuilt-free-vars-of-ll-expr
    (implies (and (string-setp locals)
                  (string-setp used)
                  (string-expr-mapp lmap)
                  (placement-inv v v0 used locals lmap)
                  (set::in v (expr-free-expr-vars new-x)))
             (or (and (set::in v (expr-free-expr-vars x))
                      (not (set::in v (omap::keys lmap))))
                 (set::in v (string-expr-map-free-expr-vars lmap))
                 (and (set::in v new-used) (not (set::in v v0)))))
    :fn ll-expr)
  (defret rebuilt-free-vars-of-ll-lambda
    (implies (and (string-setp locals)
                  (string-setp used)
                  (string-expr-mapp lmap)
                  (placement-inv v v0 used locals lmap)
                  (set::in v (expr-free-expr-vars e)))
             (or (and (set::in v (expr-free-expr-vars body))
                      (not (member-equal v (var+type?-list->var params)))
                      (not (set::in v (omap::keys lmap))))
                 (set::in v (string-expr-map-free-expr-vars lmap))
                 (and (set::in v new-used) (not (set::in v v0)))))
    :fn ll-lambda)
  (defret rebuilt-free-vars-of-ll-let-binds
    (implies (and (string-setp locals)
                  (string-setp used)
                  (string-expr-mapp lmap)
                  (placement-inv v v0 used locals lmap))
             (and (implies (set::in v (bind-list-free-expr-vars kept))
                           (or (and (set::in v (bind-list-free-expr-vars binds))
                                    (not (set::in v (omap::keys lmap))))
                               (set::in v (string-expr-map-free-expr-vars lmap))
                               (and (set::in v new-used) (not (set::in v v0)))))
                  (implies (and (set::in v (string-expr-map-free-expr-vars new-lmap))
                                (not (set::in v (bind-list-bound-expr-vars kept))))
                           (or (and (set::in v (bind-list-free-expr-vars binds))
                                    (not (set::in v (omap::keys lmap))))
                               (set::in v (string-expr-map-free-expr-vars lmap))
                               (and (set::in v new-used) (not (set::in v v0)))))
                  (placement-inv v v0 new-used new-locals new-lmap)))
    :fn ll-let-binds)
  (defret rebuilt-free-vars-of-ll-expr-list
    (implies (and (string-setp locals)
                  (string-setp used)
                  (string-expr-mapp lmap)
                  (placement-inv v v0 used locals lmap)
                  (set::in v (expr-list-free-expr-vars new-x)))
             (or (and (set::in v (expr-list-free-expr-vars x))
                      (not (set::in v (omap::keys lmap))))
                 (set::in v (string-expr-map-free-expr-vars lmap))
                 (and (set::in v new-used) (not (set::in v v0)))))
    :fn ll-expr-list)
  (defret rebuilt-free-vars-of-ll-atom
    (implies (and (string-setp locals)
                  (string-setp used)
                  (string-expr-mapp lmap)
                  (placement-inv v v0 used locals lmap)
                  (set::in v (atom-free-expr-vars new-x)))
             (or (and (set::in v (atom-free-expr-vars x))
                      (not (set::in v (omap::keys lmap))))
                 (set::in v (string-expr-map-free-expr-vars lmap))
                 (and (set::in v new-used) (not (set::in v v0)))))
    :fn ll-atom)
  (defret rebuilt-free-vars-of-ll-atom-list
    (implies (and (string-setp locals)
                  (string-setp used)
                  (string-expr-mapp lmap)
                  (placement-inv v v0 used locals lmap)
                  (set::in v (atom-list-free-expr-vars new-x)))
             (or (and (set::in v (atom-list-free-expr-vars x))
                      (not (set::in v (omap::keys lmap))))
                 (set::in v (string-expr-map-free-expr-vars lmap))
                 (and (set::in v new-used) (not (set::in v v0)))))
    :fn ll-atom-list)
  (defret rebuilt-free-vars-of-ll-bind
    (implies (and (string-setp locals)
                  (string-setp used)
                  (string-expr-mapp lmap)
                  (placement-inv v v0 used locals lmap)
                  (set::in v (bind-free-expr-vars new-x)))
             (or (and (set::in v (bind-free-expr-vars x))
                      (not (set::in v (omap::keys lmap))))
                 (set::in v (string-expr-map-free-expr-vars lmap))
                 (and (set::in v new-used) (not (set::in v v0)))))
    :fn ll-bind)
  :mutual-recursion lambda-lift-exprs/atoms/binds
  :hints (("Goal"
           :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (e/d (bind-list-bound-expr-vars
                            placement-inv-when-more-used-and-locals
                            placement-inv-of-remove-keys-when-more-used-and-locals
                            placement-inv-of-hoisting-gen
                            not-in-used-when-in-lifted-of-ll-expr
                            not-in-used-when-in-lifted-of-ll-bind
                            not-in-used-when-in-lifted-of-ll-let-binds
                            not-in-used-when-in-lifted-of-ll-lambda
                            not-in-used-when-in-lifted-of-ll-expr-list
                            not-in-used-when-in-lifted-of-ll-atom
                            not-in-used-when-in-lifted-of-ll-atom-list
                            consp-when-positive-len
                            positive-len-when-consp
                            not-in-v0-when-placement-inv
                            in-fv-of-assoc
                            in-fv-of-update-equal
                            in-fv-when-in-fv-of-delete
                            in-fv-of-remove-keys
                            in-keys-of-remove-keys
                            omap::assoc-to-in-of-keys
                            in-free-of-e-of-emit-lifted-lambda-2
                            in-free-of-replacement-of-hoist-local-fun-2
                            liftable-lambda-p
                            in-of-free-of-nested-lambda-body
                            bind-bound-expr-vars-when-ll-bind-hoisted)
                           (emit-lifted-lambda
                            hoist-local-fun
                            apply-to-names
                            bind-bound-expr-vars
                            bind-list-free-expr-vars-of-append
                            set::pick-a-point-subset-strategy
                            no-duplicatesp-equal-when-no-duplicatesp-equal-of-type-var-list->name
                            no-duplicatesp-equal-when-no-duplicatesp-equal-of-ispace-var-list->name
                            no-duplicatesp-equal-when-not-duplicated-names
                            duplicated-names-when-no-duplicatesp-equal
                            member-equal-of-type-var-list->name-when-member-equal
                            member-equal-of-ispace-var-list->name-when-member-equal
                            member-of-type-var->name-in-type-var-list->name
                            member-of-ispace-var->name-in-ispace-var-list->name
                            cdr-of-type-var-list->name
                            cdr-of-ispace-var-list->name
                            type-var-list->name-when-not-consp
                            ispace-var-list->name-when-not-consp
                            consp-of-type-var-list->name
                            consp-of-ispace-var-list->name
                            acl2::utf8-table36-length-lemmas
                            acl2::subsetp-car-member
                            acl2::subsetp-when-atom-right))
           :expand ((ll-expr x tenv tlets locals lmap used)
                    (:free (type?) (ll-lambda params body type? tenv tlets locals lmap used))
                    (ll-let-binds binds body-binders tenv tlets locals lmap used)
                    (ll-expr-list x tenv tlets locals lmap used)
                    (ll-atom x tenv tlets locals lmap used)
                    (ll-atom-list x tenv tlets locals lmap used)
                    (ll-bind x tenv tlets locals lmap used)
                    (:free (n) (expr-free-expr-vars (expr-var n)))
                    (:free (a) (expr-free-expr-vars (expr-atom a)))
                    (:free (ds as) (expr-free-expr-vars (expr-array ds as)))
                    (:free (ds es) (expr-free-expr-vars (expr-frame ds es)))
                    (:free (f a) (expr-free-expr-vars (expr-app f a)))
                    (:free (f as) (expr-free-expr-vars (expr-appn f as)))
                    (:free (f a) (expr-free-expr-vars (expr-tapp f a)))
                    (:free (f as) (expr-free-expr-vars (expr-tappn f as)))
                    (:free (f a) (expr-free-expr-vars (expr-iapp f a)))
                    (:free (f as) (expr-free-expr-vars (expr-iappn f as)))
                    (:free (f tg ig as) (expr-free-expr-vars (expr-capp f tg ig as)))
                    (:free (i w tg b ty) (expr-free-expr-vars (expr-unbox i w tg b ty)))
                    (:free (is w tg b ty) (expr-free-expr-vars (expr-unboxn is w tg b ty)))
                    (:free (es) (expr-free-expr-vars (expr-bracket es)))
                    (:free (bs b) (expr-free-expr-vars (expr-let bs b)))
                    (:free (p b ty) (atom-free-expr-vars (atom-lambda p b ty)))
                    (:free (ps b ty) (atom-free-expr-vars (atom-lambdan ps b ty)))
                    (:free (p b) (atom-free-expr-vars (atom-tlambda p b)))
                    (:free (ps b) (atom-free-expr-vars (atom-tlambdan ps b)))
                    (:free (p b) (atom-free-expr-vars (atom-ilambda p b)))
                    (:free (ps b) (atom-free-expr-vars (atom-ilambdan ps b)))
                    (:free (i a ty) (atom-free-expr-vars (atom-box i a ty)))
                    (:free (is a ty) (atom-free-expr-vars (atom-boxn is a ty)))
                    (:free (w ty e) (bind-free-expr-vars (bind-val w ty e)))
                    (:free (w ps ty e) (bind-free-expr-vars (bind-fun w ps ty e)))
                    (:free (w ps ty e) (bind-free-expr-vars (bind-tfun w ps ty e)))
                    (:free (w ps ty e) (bind-free-expr-vars (bind-ifun w ps ty e)))
                    (:free (w tp ip ps ty e) (bind-free-expr-vars (bind-cfun w tp ip ps ty e)))
                    (:free (a l) (expr-list-free-expr-vars (cons a l)))
                    (:free (a l) (atom-list-free-expr-vars (cons a l)))
                    (:free (a l) (bind-list-free-expr-vars (cons a l)))
                    (expr-free-expr-vars x)
                    (atom-free-expr-vars x)
                    (atom-free-expr-vars (expr-atom->atom x))
                    (bind-free-expr-vars x)
                    (expr-list-free-expr-vars x)
                    (atom-list-free-expr-vars x)
                    (bind-list-free-expr-vars binds)
                    (bind-list-free-expr-vars nil)))))


; Stage C: a variable free in the definitions lifted out of a node is free
; in the node and not local, or the name of a definition lifted before.

(defret-mutual lifted-free-vars-of-lambda-lift-exprs/atoms/binds
  (defret lifted-free-vars-of-ll-expr
    (implies (and (string-setp locals)
                  (string-setp used)
                  (string-expr-mapp lmap)
                  (placement-inv v v0 used locals lmap)
                  (set::in v (bind-list-free-expr-vars lifted)))
             (or (and (set::in v (expr-free-expr-vars x))
                      (not (set::in v locals)))
                 (and (set::in v used) (not (set::in v v0)))))
    :fn ll-expr)
  (defret lifted-free-vars-of-ll-lambda
    (implies (and (string-setp locals)
                  (string-setp used)
                  (string-expr-mapp lmap)
                  (placement-inv v v0 used locals lmap)
                  (set::in v (bind-list-free-expr-vars lifted)))
             (or (and (set::in v (expr-free-expr-vars body))
                      (not (member-equal v (var+type?-list->var params)))
                      (not (set::in v locals)))
                 (and (set::in v used) (not (set::in v v0)))))
    :fn ll-lambda)
  (defret lifted-free-vars-of-ll-let-binds
    (implies (and (string-setp locals)
                  (string-setp used)
                  (string-expr-mapp lmap)
                  (placement-inv v v0 used locals lmap)
                  (set::in v (bind-list-free-expr-vars lifted)))
             (or (and (set::in v (bind-list-free-expr-vars binds))
                      (not (set::in v locals)))
                 (and (set::in v used) (not (set::in v v0)))))
    :fn ll-let-binds)
  (defret lifted-free-vars-of-ll-expr-list
    (implies (and (string-setp locals)
                  (string-setp used)
                  (string-expr-mapp lmap)
                  (placement-inv v v0 used locals lmap)
                  (set::in v (bind-list-free-expr-vars lifted)))
             (or (and (set::in v (expr-list-free-expr-vars x))
                      (not (set::in v locals)))
                 (and (set::in v used) (not (set::in v v0)))))
    :fn ll-expr-list)
  (defret lifted-free-vars-of-ll-atom
    (implies (and (string-setp locals)
                  (string-setp used)
                  (string-expr-mapp lmap)
                  (placement-inv v v0 used locals lmap)
                  (set::in v (bind-list-free-expr-vars lifted)))
             (or (and (set::in v (atom-free-expr-vars x))
                      (not (set::in v locals)))
                 (and (set::in v used) (not (set::in v v0)))))
    :fn ll-atom)
  (defret lifted-free-vars-of-ll-atom-list
    (implies (and (string-setp locals)
                  (string-setp used)
                  (string-expr-mapp lmap)
                  (placement-inv v v0 used locals lmap)
                  (set::in v (bind-list-free-expr-vars lifted)))
             (or (and (set::in v (atom-list-free-expr-vars x))
                      (not (set::in v locals)))
                 (and (set::in v used) (not (set::in v v0)))))
    :fn ll-atom-list)
  (defret lifted-free-vars-of-ll-bind
    (implies (and (string-setp locals)
                  (string-setp used)
                  (string-expr-mapp lmap)
                  (placement-inv v v0 used locals lmap)
                  (set::in v (bind-list-free-expr-vars lifted)))
             (or (and (set::in v (bind-free-expr-vars x))
                      (not (set::in v locals)))
                 (and (set::in v used) (not (set::in v v0)))))
    :fn ll-bind)
  :mutual-recursion lambda-lift-exprs/atoms/binds
  :hints (("Goal"
           :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (e/d (bind-list-bound-expr-vars
                            placement-inv-when-more-used-and-locals
                            placement-inv-of-remove-keys-when-more-used-and-locals
                            placement-inv-of-hoisting-gen
                            in-used-when-placement-inv-and-in-fv
                            not-in-v0-when-placement-inv
                            not-in-used-when-in-lifted-of-ll-expr
                            not-in-used-when-in-lifted-of-ll-bind
                            not-in-used-when-in-lifted-of-ll-let-binds
                            not-in-used-when-in-lifted-of-ll-lambda
                            not-in-used-when-in-lifted-of-ll-expr-list
                            not-in-used-when-in-lifted-of-ll-atom
                            not-in-used-when-in-lifted-of-ll-atom-list
                            in-fv-of-remove-keys
                            in-keys-of-remove-keys
                            omap::assoc-to-in-of-keys
                            in-of-bind-list-free-expr-vars-of-append
                            in-free-of-lifted-of-emit-lifted-lambda
                            in-free-of-hoisted-of-hoist-local-fun
                            in-of-free-of-nested-lambda-body
                            bind-bound-expr-vars-when-ll-bind-hoisted
                            liftable-lambda-p)
                           (emit-lifted-lambda
                            hoist-local-fun
                            apply-to-names
                            bind-bound-expr-vars
                            bind-list-free-expr-vars-of-append
                            set::pick-a-point-subset-strategy
                            no-duplicatesp-equal-when-no-duplicatesp-equal-of-type-var-list->name
                            no-duplicatesp-equal-when-no-duplicatesp-equal-of-ispace-var-list->name
                            no-duplicatesp-equal-when-not-duplicated-names
                            duplicated-names-when-no-duplicatesp-equal
                            member-equal-of-type-var-list->name-when-member-equal
                            member-equal-of-ispace-var-list->name-when-member-equal
                            member-of-type-var->name-in-type-var-list->name
                            member-of-ispace-var->name-in-ispace-var-list->name
                            cdr-of-type-var-list->name
                            cdr-of-ispace-var-list->name
                            type-var-list->name-when-not-consp
                            ispace-var-list->name-when-not-consp
                            consp-of-type-var-list->name
                            consp-of-ispace-var-list->name
                            acl2::utf8-table36-length-lemmas
                            acl2::subsetp-car-member
                            acl2::subsetp-when-atom-right))
           :expand ((ll-expr x tenv tlets locals lmap used)
                    (:free (type?) (ll-lambda params body type? tenv tlets locals lmap used))
                    (ll-let-binds binds body-binders tenv tlets locals lmap used)
                    (ll-expr-list x tenv tlets locals lmap used)
                    (ll-atom x tenv tlets locals lmap used)
                    (ll-atom-list x tenv tlets locals lmap used)
                    (ll-bind x tenv tlets locals lmap used)
                    (:free (a) (expr-free-expr-vars (expr-atom a)))
                    (:free (bs b) (expr-free-expr-vars (expr-let bs b)))
                    (:free (w ps ty e) (bind-free-expr-vars (bind-fun w ps ty e)))
                    (:free (a l) (bind-list-free-expr-vars (cons a l)))
                    (expr-free-expr-vars x)
                    (atom-free-expr-vars x)
                    (atom-free-expr-vars (expr-atom->atom x))
                    (bind-free-expr-vars x)
                    (expr-list-free-expr-vars x)
                    (atom-list-free-expr-vars x)
                    (bind-list-free-expr-vars binds)
                    (bind-list-free-expr-vars nil)))
          (and (acl2::occur-lst '(acl2::flag-is 'll-lambda) clause)
               (acl2::occur-lst '(ll-lambda params body type? tenv tlets locals lmap used) clause)
               '(:use ((:instance rebuilt-free-vars-of-ll-expr
                                  (x body)
                                  (tenv (extend-tenv-with-params
                                         (var+type?-list-fix params) tenv))
                                  (tlets (tlets-without
                                          (var+type?-list->var params) tlets))
                                  (locals (locals-with-params
                                           (var+type?-list-fix params) locals))
                                  (lmap (string-expr-map-remove-keys
                                         (var+type?-list->var params) lmap))
                                  (used used)))))
          (and (acl2::occur-lst '(acl2::flag-is 'll-let-binds) clause)
               (acl2::occur-lst '(ll-let-binds binds body-binders tenv tlets locals lmap used) clause)
               '(:use ((:instance rebuilt-free-vars-of-ll-bind
                                  (x (bind-fix (car binds)))))))))


; The placement theorems.

; An expression: the lifted definitions are wrapped around the rebuilt
; expression, and the result has no free variable that the input does not
; have.  So each lifted definition is in the scope of the ones before it
; that it refers to, and the rebuilt expression in the scope of all of them.

(defruled in-free-of-lambda-lift-top-expr
  (implies (set::in v (expr-free-expr-vars (lambda-lift-top-expr x)))
           (set::in v (expr-free-expr-vars x)))
  :enable (lambda-lift-top-expr
           in-of-expr-free-expr-vars-of-nest-let-binds
           placement-inv-of-nil-map)
  :disable (expr-free-expr-vars-of-nest-let-binds)
  :use ((:instance rebuilt-free-vars-of-ll-expr
                   (tenv nil) (tlets nil) (locals nil) (lmap nil)
                   (used (expr-all-expr-vars x))
                   (v0 (expr-all-expr-vars x)))
        (:instance lifted-free-vars-of-ll-expr
                   (tenv nil) (tlets nil) (locals nil) (lmap nil)
                   (used (expr-all-expr-vars x))
                   (v0 (expr-all-expr-vars x)))
        (:instance in-new-used-of-ll-expr
                   (tenv nil) (tlets nil) (locals nil) (lmap nil)
                   (used (expr-all-expr-vars x))))
  :expand ((string-expr-map-free-expr-vars nil)))

(defrule expr-free-expr-vars-of-lambda-lift-top-expr
  (set::subset (expr-free-expr-vars (lambda-lift-top-expr x))
               (expr-free-expr-vars x))
  :enable (set::pick-a-point-subset-strategy
           in-free-of-lambda-lift-top-expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Top-level bindings, as a file's declarations become: the bindings of the
; result are scoped sequentially, and they have no free variable that the
; input does not have.  Since the free variables of a list of bindings are
; computed sequentially, this says that each definition lifted out of a
; binding refers only to bindings before it, in the result.

(defruled in-free-of-lambda-lift-top-binds
  (implies (and (string-setp used)
                (implies (set::in v v0) (set::in v used))
                (set::in v (bind-list-free-expr-vars
                            (lambda-lift-top-binds binds used))))
           (or (set::in v (bind-list-free-expr-vars binds))
               (and (set::in v used)
                    (not (set::in v v0)))))
  :induct (lambda-lift-top-binds binds used)
  :enable (lambda-lift-top-binds
           in-of-bind-list-free-expr-vars-of-append
           placement-inv-of-nil-map)
  :disable (bind-list-free-expr-vars-of-append)
  :expand ((:free (a l) (bind-list-free-expr-vars (cons a l)))
           (bind-list-free-expr-vars binds)
           (string-expr-map-free-expr-vars nil))
  :hints (("Subgoal *1/2"
           :use ((:instance rebuilt-free-vars-of-ll-bind
                            (x (car binds)) (tenv nil) (tlets nil) (locals nil) (lmap nil))
                 (:instance lifted-free-vars-of-ll-bind
                            (x (car binds)) (tenv nil) (tlets nil) (locals nil) (lmap nil))
                 (:instance in-new-used-of-ll-bind
                            (x (car binds)) (tenv nil) (tlets nil) (locals nil) (lmap nil))))))


(defruled in-free-of-lambda-lift-top-binds-when-in-output
  (implies (and (string-setp used)
                (set::in v (bind-list-free-expr-vars
                            (lambda-lift-top-binds binds used))))
           (set::in v (bind-list-free-expr-vars binds)))
  :use ((:instance in-free-of-lambda-lift-top-binds (v0 used))))

(defrule bind-list-free-expr-vars-of-lambda-lift-top-binds
  (implies (string-setp used)
           (set::subset (bind-list-free-expr-vars (lambda-lift-top-binds binds used))
                        (bind-list-free-expr-vars binds)))
  :enable (set::pick-a-point-subset-strategy
           in-free-of-lambda-lift-top-binds-when-in-output))

(defrule bind-list-free-expr-vars-of-lambda-lift-file
  (set::subset (bind-list-free-expr-vars
                (decl-list-to-binds (file->decls (lambda-lift-file f))))
               (bind-list-free-expr-vars
                (decl-list-to-binds (file->decls f))))
  :enable lambda-lift-file)

