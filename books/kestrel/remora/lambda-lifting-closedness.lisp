; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "lambda-lifting-placement")

(include-book "portcullis")

(local (include-book "osets"))
(local (include-book "std/osets/top" :dir :system))

(local (in-theory (disable (:e tau-system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lambda-lifting-closedness
  :parents (lambda-lifting)
  :short "Lifted definitions are closed in type and ispace variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "The definitions that lambda lifting adds are placed at the top level,
     outside all the binders of type and ispace variables, so they must not
     mention any.  That holds when the binders of the input bind distinct
     names, as the guards of @(tsee lambda-lift-top-expr) and @(tsee
     lambda-lift-file) require: @('binds-closed-p-of-lifted-of-lambda-lift-top-expr') says that every
     definition lifted out of an expression is closed in type and ispace
     variables (see @(tsee binds-closed-p)), so that lifting does not change
     the free type and ispace variables of the expression; and @('binds-closed-p-of-lambda-lift-file') says that if every declaration of a
     file is closed, so is every declaration of the result.")
   (xdoc::p
    (xdoc::b "Proof."))
   (xdoc::p
    "A lifted lambda or a hoisted local function takes the variables it
     captures as leading parameters, typed as the type environment types
     them.  A hoisted function checks the types of exactly those variables
     (see @(tsee hoist-local-fun)).  A lambda checks the types of the local
     variables free in it before its body is lifted out of (see @(tsee
     liftable-lambda-p)); afterwards the body may also refer to the
     variables captured by the hoisted functions it uses, through the
     expressions that replace their uses.  The invariant @(tsee closed-inv)
     says, of each variable, that the invariant of @(see
     lambda-lifting-placement) holds, that if it is local it is among the
     names @('v0') in use at the start, and that if it is local and free in
     a replacement its type is closed.  So the variables a lambda captures
     have closed types (@('cap-closed-p-of-ll-expr')): each is free in
     the original body, or local and free in a replacement, or the name of
     a lifted definition, which is not local.")
   (xdoc::p
    "Unique binder names keep the invariant as the environments grow: the
     name a binder binds is not local and is in @('v0'), so it is not free
     in a replacement, and binding it changes the type of no local variable
     free in a replacement.  The induction is @('closed-lifted-of-ll-expr'); a lambda is lifted with the environments
     extended with its parameters, and its hypotheses are stated for those,
     so that they are available where the body is lifted out of."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Whether the type the environment records for a variable, if any, is closed
; in type and ispace variables.

(define param-type-closed-p ((v stringp) (tenv string-type-mapp))
  :returns (yes/no booleanp)
  (b* ((type? (name-to-type-option v tenv)))
    (and (set::emptyp (type-option-free-type-vars type?))
         (set::emptyp (type-option-free-ispace-vars type?)))))

(define names-closed-p ((names string-listp) (tenv string-type-mapp))
  :returns (yes/no booleanp)
  (or (endp names)
      (and (param-type-closed-p (car names) tenv)
           (names-closed-p (cdr names) tenv))))

(defruled names-closed-p-when-captured-params-closed-p
  (implies (captured-params-closed-p names tenv)
           (names-closed-p names tenv))
  :induct (names-closed-p names tenv)
  :enable (captured-params-closed-p names-closed-p names-to-params
           param-type-closed-p)
  :expand ((:free (a l) (var+type?-list-free-type-vars (cons a l)))
           (:free (a l) (var+type?-list-free-ispace-vars (cons a l)))
           (:free (w ty) (var+type?-free-type-vars (var+type? w ty)))
           (:free (w ty) (var+type?-free-ispace-vars (var+type? w ty)))))

(defruled captured-params-closed-p-when-names-closed-p
  (implies (names-closed-p names tenv)
           (captured-params-closed-p names tenv))
  :induct (names-closed-p names tenv)
  :enable (captured-params-closed-p names-closed-p names-to-params
           param-type-closed-p)
  :expand ((:free (a l) (var+type?-list-free-type-vars (cons a l)))
           (:free (a l) (var+type?-list-free-ispace-vars (cons a l)))
           (:free (w ty) (var+type?-free-type-vars (var+type? w ty)))
           (:free (w ty) (var+type?-free-ispace-vars (var+type? w ty)))
           (var+type?-list-free-type-vars nil)
           (var+type?-list-free-ispace-vars nil)))

(defruled param-type-closed-p-when-member-names-closed-p
  (implies (and (names-closed-p names tenv)
                (member-equal v names))
           (param-type-closed-p v tenv))
  :induct (names-closed-p names tenv)
  :enable names-closed-p)

; The same for a set of variables, a variable at a time.

(acl2::defun-sk params-closed-on (s tenv)
  (forall (v)
          (implies (set::in v s)
                   (param-type-closed-p v tenv))))

(in-theory (disable params-closed-on))

;; The two forms agree on sets.

(defruled param-type-closed-p-when-member-params-closed-on
  (implies (and (set::setp s)
                (params-closed-on s tenv)
                (member-equal v s))
           (param-type-closed-p v tenv))
  :enable set::in-to-member
  :use params-closed-on-necc)

(defruled names-closed-p-when-params-closed-on-and-subsetp
  (implies (and (set::setp s)
                (params-closed-on s tenv)
                (subsetp-equal l s))
           (names-closed-p l tenv))
  :induct (len l)
  :enable (names-closed-p param-type-closed-p-when-member-params-closed-on)
  :expand ((subsetp-equal l s)))

(defrule params-closed-on-when-captured-params-closed-p
  (implies (and (set::setp s)
                (captured-params-closed-p s tenv))
           (params-closed-on s tenv))
  :enable (params-closed-on set::in-to-member)
  :use ((:instance names-closed-p-when-captured-params-closed-p (names s))
        (:instance param-type-closed-p-when-member-names-closed-p
                   (names s) (v (params-closed-on-witness s tenv)))))

(defrule captured-params-closed-p-when-params-closed-on
  (implies (and (set::setp s)
                (params-closed-on s tenv))
           (captured-params-closed-p s tenv))
  :use ((:instance names-closed-p-when-params-closed-on-and-subsetp (l s))
        (:instance captured-params-closed-p-when-names-closed-p (names s))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Extending the type environment leaves the types of other variables alone.

(defrule name-to-type-option-of-extend-tenv-with-var
  (implies (not (equal (str-fix v) (str-fix w)))
           (equal (name-to-type-option v (extend-tenv-with-var w ty tenv))
                  (name-to-type-option v tenv)))
  :enable (name-to-type-option extend-tenv-with-var omap::assoc-of-update))

(defrule name-to-type-option-of-extend-tenv-with-params
  (implies (and (stringp v)
                (not (member-equal v (var+type?-list->var params))))
           (equal (name-to-type-option v (extend-tenv-with-params params tenv))
                  (name-to-type-option v tenv)))
  :induct (extend-tenv-with-params params tenv)
  :enable (extend-tenv-with-params var+type?-list->var)
  :expand ((:free (tenv) (name-to-type-option v (string-type-map-fix tenv)))
           (name-to-type-option v tenv)))

(defrule assoc-of-restrict-to-keys-when-not-in
  (implies (not (set::in key (string-sfix keys)))
           (not (omap::assoc key (restrict-to-keys keys tenv))))
  :induct (restrict-to-keys keys tenv)
  :enable (restrict-to-keys omap::assoc-of-update))

(defrule name-to-type-option-of-extend-tenv-with-binds
  (implies (and (stringp v)
                (not (set::in v (bind-list-bound-expr-vars binds))))
           (equal (name-to-type-option v (extend-tenv-with-binds binds tenv))
                  (name-to-type-option v tenv)))
  :enable (extend-tenv-with-binds name-to-type-option)
  :use ((:instance assoc-of-restrict-to-keys-when-not-in
                   (key v)
                   (keys (bind-list-bound-expr-vars binds))
                   (tenv (expr-senv->exprs
                          (senvs+binds->eenv
                           (check-bind-list
                            binds
                            (ispace-senv nil)
                            (type-senv nil)
                            (tenv-to-expr-senv (string-type-map-fix tenv)))))))))

(defrule param-type-closed-p-of-extend-tenv-with-params
  (implies (and (stringp v)
                (not (member-equal v (var+type?-list->var params))))
           (equal (param-type-closed-p v (extend-tenv-with-params params tenv))
                  (param-type-closed-p v tenv)))
  :enable param-type-closed-p)

(defrule assoc-of-update*-of-restrict-to-keys-when-not-in
  (implies (not (set::in key (string-sfix keys)))
           (equal (omap::assoc key (omap::update* (restrict-to-keys keys m) tenv))
                  (omap::assoc key tenv)))
  :enable omap::assoc-of-update*)

(defrule name-to-type-option-of-extend-tenv-with-let-bind
  (implies (and (stringp v)
                (not (set::in v (bind-bound-expr-vars b))))
           (equal (name-to-type-option
                   v (mv-nth 0 (extend-tenv-with-let-bind b tenv tlets locals)))
                  (name-to-type-option v tenv)))
  :enable (extend-tenv-with-let-bind name-to-type-option))

(defrule param-type-closed-p-of-extend-tenv-with-let-bind
  (implies (and (stringp v)
                (not (set::in v (bind-bound-expr-vars b))))
           (equal (param-type-closed-p
                   v (mv-nth 0 (extend-tenv-with-let-bind b tenv tlets locals)))
                  (param-type-closed-p v tenv)))
  :enable param-type-closed-p)

(defrule param-type-closed-p-of-extend-tenv-with-binds
  (implies (and (stringp v)
                (not (set::in v (bind-list-bound-expr-vars binds))))
           (equal (param-type-closed-p v (extend-tenv-with-binds binds tenv))
                  (param-type-closed-p v tenv)))
  :enable param-type-closed-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lists of names: membership, overlap, and duplicates, in forms that
; decompose the binder names of a node into those of its parts.

(defrulel member-equal-of-append-local
  (iff (member-equal p (append a b))
       (or (member-equal p a)
           (member-equal p b))))

(defrulel intersectp-equal-of-cons-right
  (iff (intersectp-equal a (cons p b))
       (or (member-equal p a)
           (intersectp-equal a b)))
  :induct (len a)
  :enable intersectp-equal)

(defrulel intersectp-equal-of-nil
  (and (not (intersectp-equal nil a))
       (not (intersectp-equal a nil)))
  :induct (len a)
  :enable intersectp-equal)

(defrulel intersectp-equal-commute
  (equal (intersectp-equal a b)
         (intersectp-equal b a))
  :induct (len a)
  :enable intersectp-equal)

(defrulel intersectp-equal-of-append-left
  (equal (intersectp-equal (append a b) c)
         (or (intersectp-equal a c)
             (intersectp-equal b c)))
  :induct (len a)
  :enable intersectp-equal
  :disable intersectp-equal-commute)

(defrulel intersectp-equal-of-append-right
  (equal (intersectp-equal c (append a b))
         (or (intersectp-equal c a)
             (intersectp-equal c b)))
  :use ((:instance intersectp-equal-commute (a c) (b (append a b)))
        (:instance intersectp-equal-commute (a c) (b a))
        (:instance intersectp-equal-commute (a c) (b b)))
  :disable intersectp-equal-commute)

(defrulel no-duplicatesp-equal-of-append-local
  (equal (no-duplicatesp-equal (append a b))
         (and (no-duplicatesp-equal a)
              (no-duplicatesp-equal b)
              (not (intersectp-equal a b))))
  :induct (len a)
  :enable intersectp-equal
  :disable intersectp-equal-commute)

; None of the names is in a set.

(define none-in-p (names s)
  :verify-guards nil
  (or (not (consp names))
      (and (not (set::in (car names) s))
           (none-in-p (cdr names) s))))

(defrule none-in-p-when-atom
  (implies (not (consp names))
           (none-in-p names s))
  :enable none-in-p)

(defrule none-in-p-of-cons
  (equal (none-in-p (cons p names) s)
         (and (not (set::in p s))
              (none-in-p names s)))
  :enable none-in-p)

(defrule none-in-p-of-append
  (equal (none-in-p (append a b) s)
         (and (none-in-p a s)
              (none-in-p b s)))
  :induct (len a)
  :enable none-in-p)

(defruled not-in-when-member-and-none-in-p
  (implies (and (none-in-p names s)
                (member-equal p names))
           (not (set::in p s)))
  :induct (len names)
  :enable none-in-p)

(defrule none-in-p-of-union
  (equal (none-in-p names (set::union s1 s2))
         (and (none-in-p names s1)
              (none-in-p names s2)))
  :induct (len names)
  :enable none-in-p)

(defrule none-in-p-of-insert
  (equal (none-in-p names (set::insert p s))
         (and (not (member-equal p names))
              (none-in-p names s)))
  :induct (len names)
  :enable none-in-p)

(defrule none-in-p-of-mergesort
  (equal (none-in-p names (set::mergesort l))
         (not (intersectp-equal names l)))
  :induct (len names)
  :enable (none-in-p intersectp-equal)
  :disable intersectp-equal-commute)

(defrule none-in-p-of-nil
  (none-in-p names nil)
  :induct (len names)
  :enable none-in-p)

(defrule none-in-p-of-locals-with-params
  (equal (none-in-p names (locals-with-params params locals))
         (and (not (intersectp-equal names (var+type?-list->var params)))
              (none-in-p names (string-sfix locals))))
  :enable locals-with-params)

(defruled none-in-p-when-subset
  (implies (and (none-in-p names s1)
                (set::subset s2 s1))
           (none-in-p names s2))
  :induct (len names)
  :enable (none-in-p set::subset-in))

; All of the names are in a set.

(define all-in-p (names s)
  :verify-guards nil
  (or (not (consp names))
      (and (set::in (car names) s)
           (all-in-p (cdr names) s))))

(defrule all-in-p-when-atom
  (implies (not (consp names))
           (all-in-p names s))
  :enable all-in-p)

(defrule all-in-p-of-cons
  (equal (all-in-p (cons p names) s)
         (and (set::in p s)
              (all-in-p names s)))
  :enable all-in-p)

(defrule all-in-p-of-append
  (equal (all-in-p (append a b) s)
         (and (all-in-p a s)
              (all-in-p b s)))
  :induct (len a)
  :enable all-in-p)

(defruled in-when-member-and-all-in-p
  (implies (and (all-in-p names s)
                (member-equal p names))
           (set::in p s))
  :induct (len names)
  :enable all-in-p)

(defruled all-in-p-when-subsetp-and-subset-of-mergesort
  (implies (and (subsetp-equal l names)
                (set::subset (set::mergesort names) s))
           (all-in-p l s))
  :induct (len l)
  :enable (all-in-p subsetp-equal set::subset-in))

(defrule subset-of-mergesort-to-all-in-p
  (equal (set::subset (set::mergesort names) s)
         (all-in-p names s))
  :use ((:instance all-in-p-when-subsetp-and-subset-of-mergesort (l names))
        (:instance set::pick-a-point-subset-strategy
                   (set::x (set::mergesort names)) (set::y s)))
  :enable in-when-member-and-all-in-p)

; Which names a binding binds.

(defrule in-of-bind-bound-expr-vars
  (equal (set::in v (bind-bound-expr-vars b))
         (and (not (member-equal (bind-kind b) '(:ispace :type)))
              (equal v (bind-name b))))
  :enable (bind-bound-expr-vars bind-name))

(defrule in-of-bind-list-bound-expr-vars-when-not-member-names
  (implies (not (member-equal v (bind-list-names binds)))
           (not (set::in v (bind-list-bound-expr-vars binds))))
  :induct (len binds)
  :enable (bind-list-bound-expr-vars bind-list-names))

(defrule in-all-expr-vars-when-in-bind-bound-expr-vars
  (implies (set::in v (bind-bound-expr-vars b))
           (set::in v (bind-all-expr-vars b)))
  :enable (bind-bound-expr-vars bind-name)
  :disable in-of-bind-bound-expr-vars
  :expand ((bind-all-expr-vars b)))

; Lists of bindings each closed in type and ispace variables.

(define binds-closed-p ((binds bind-listp))
  :parents (lambda-lifting-closedness)
  :short "Check that each binding of a list
          is closed in type and ispace variables."
  :returns (yes/no booleanp)
  (or (endp binds)
      (and (set::emptyp (bind-free-type-vars (car binds)))
           (set::emptyp (bind-free-ispace-vars (car binds)))
           (binds-closed-p (cdr binds)))))

(defrule binds-closed-p-when-atom
  (implies (not (consp binds))
           (binds-closed-p binds))
  :enable binds-closed-p)

(defrule binds-closed-p-of-cons
  (equal (binds-closed-p (cons b binds))
         (and (set::emptyp (bind-free-type-vars b))
              (set::emptyp (bind-free-ispace-vars b))
              (binds-closed-p binds)))
  :enable binds-closed-p)

(defrule binds-closed-p-of-append
  (equal (binds-closed-p (append a b))
         (and (binds-closed-p a)
              (binds-closed-p b)))
  :induct (len a)
  :enable binds-closed-p)

(defrule free-vars-when-binds-closed-p
  (implies (binds-closed-p binds)
           (and (set::emptyp (bind-list-free-type-vars binds))
                (set::emptyp (bind-list-free-ispace-vars binds))))
  :induct (len binds)
  :enable binds-closed-p
  :expand ((bind-list-free-type-vars binds)
           (bind-list-free-ispace-vars binds)))

; The lists of parameters' free variables.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule stringp-when-in-string-expr-map-free-expr-vars
  (implies (set::in v (string-expr-map-free-expr-vars m))
           (stringp v))
  :use ((:instance acl2::stringp-when-in-string-setp-binds-free-x
                   (acl2::a v)
                   (acl2::x (string-expr-map-free-expr-vars m)))))

(defrule stringp-when-in-expr-free-expr-vars
  (implies (set::in v (expr-free-expr-vars e))
           (stringp v))
  :use ((:instance acl2::stringp-when-in-string-setp-binds-free-x
                   (acl2::a v)
                   (acl2::x (expr-free-expr-vars e)))))

(defrule param-type-closed-p-of-string-type-map-fix
  (equal (param-type-closed-p v (string-type-map-fix tenv))
         (param-type-closed-p v tenv))
  :enable (param-type-closed-p name-to-type-option))

; The invariant of the traversal, for one variable V: the placement
; invariant; a local variable is among the names V0 in use at the start;
; and a local variable free in the replacement of a hoisted function has a
; type closed in type and ispace variables.

(define closed-inv-at (v v0 tenv locals lmap used)
  :verify-guards nil
  (and (placement-inv v v0 used locals lmap)
       (implies (set::in v locals)
                (set::in v v0))
       (implies (and (set::in v (string-expr-map-free-expr-vars lmap))
                     (set::in v locals))
                (param-type-closed-p v tenv))))

(acl2::defun-sk closed-inv-all (v0 tenv locals lmap used)
  (forall (v) (closed-inv-at v v0 tenv locals lmap used)))

(in-theory (disable closed-inv-all))

(define closed-inv (v0 tenv locals lmap used)
  :parents (lambda-lifting-closedness)
  :short "The invariant of the closedness traversal:
          the lifted definitions are closed,
          and the per-variable invariant holds for every variable."
  :verify-guards nil
  (and (lmap-closed-p lmap)
       (closed-inv-all v0 tenv locals lmap used)))

(defruled closed-inv-at-when-closed-inv
  (implies (closed-inv v0 tenv locals lmap used)
           (closed-inv-at v v0 tenv locals lmap used))
  :enable closed-inv
  :use closed-inv-all-necc)

(defruled placement-inv-when-closed-inv
  (implies (closed-inv v0 tenv locals lmap used)
           (placement-inv v v0 used locals lmap))
  :enable closed-inv-at
  :use closed-inv-at-when-closed-inv)

(defruled lmap-closed-p-when-closed-inv
  (implies (closed-inv v0 tenv locals lmap used)
           (lmap-closed-p lmap))
  :enable closed-inv)

(defrule closed-inv-of-nil-map
  (implies (and (set::subset v0 used)
                (set::subset locals v0))
           (closed-inv v0 tenv locals nil used))
  :enable (closed-inv closed-inv-at placement-inv set::subset-in)
  :expand ((closed-inv-all v0 tenv locals nil used)
           (string-expr-map-free-expr-vars nil)))

; A binder whose name is not local but in V0 is not free in a replacement.

(defruled not-in-fv-when-closed-inv
  (implies (and (closed-inv v0 tenv locals lmap used)
                (not (set::in p locals))
                (set::in p v0))
           (not (set::in p (string-expr-map-free-expr-vars lmap))))
  :enable (closed-inv-at placement-inv)
  :use ((:instance closed-inv-at-when-closed-inv (v p))))

(defruled none-in-p-fv-when-closed-inv
  (implies (and (closed-inv v0 tenv locals lmap used)
                (none-in-p names locals)
                (all-in-p names v0))
           (none-in-p names (string-expr-map-free-expr-vars lmap)))
  :induct (len names)
  :enable (none-in-p all-in-p not-in-fv-when-closed-inv))

(defrule none-in-p-of-fv-of-remove-keys
  (implies (none-in-p names (string-expr-map-free-expr-vars lmap))
           (none-in-p names (string-expr-map-free-expr-vars
                             (string-expr-map-remove-keys keys lmap))))
  :use ((:instance none-in-p-when-subset
                   (s1 (string-expr-map-free-expr-vars lmap))
                   (s2 (string-expr-map-free-expr-vars
                        (string-expr-map-remove-keys keys lmap))))))

; The names in use only grow.

(defrule used-subset-of-ll-expr
  (implies (string-setp used)
           (set::subset used (mv-nth 2 (ll-expr x tenv tlets locals lmap used))))
  :use used-of-ll-expr)

(defrule used-subset-of-ll-lambda
  (implies (string-setp used)
           (set::subset used (mv-nth 2 (ll-lambda params body type? tenv tlets locals lmap used))))
  :use used-of-ll-lambda)

(defrule used-subset-of-ll-let-binds
  (implies (string-setp used)
           (set::subset used (mv-nth 5 (ll-let-binds binds body-binders
                                                     tenv tlets locals lmap used))))
  :use used-of-ll-let-binds)

(defrule used-subset-of-ll-expr-list
  (implies (string-setp used)
           (set::subset used (mv-nth 2 (ll-expr-list x tenv tlets locals lmap used))))
  :use used-of-ll-expr-list)

(defrule used-subset-of-ll-atom
  (implies (string-setp used)
           (set::subset used (mv-nth 2 (ll-atom x tenv tlets locals lmap used))))
  :use used-of-ll-atom)

(defrule used-subset-of-ll-atom-list
  (implies (string-setp used)
           (set::subset used (mv-nth 2 (ll-atom-list x tenv tlets locals lmap used))))
  :use used-of-ll-atom-list)

(defrule used-subset-of-ll-bind
  (implies (string-setp used)
           (set::subset used (mv-nth 2 (ll-bind x tenv tlets locals lmap used))))
  :use used-of-ll-bind)

; A variable not free in the values of a map is not free in them after
; keys are removed.

(defrule not-in-fv-of-remove-keys
  (implies (not (set::in v (string-expr-map-free-expr-vars m)))
           (not (set::in v (string-expr-map-free-expr-vars
                            (string-expr-map-remove-keys keys m)))))
  :use in-fv-of-remove-keys)

; The invariant carries over to more names in use.

(defruled closed-inv-when-more-used
  (implies (and (closed-inv v0 tenv locals lmap used)
                (set::subset used used2))
           (closed-inv v0 tenv locals lmap used2))
  :enable (closed-inv closed-inv-at set::subset-in)
  :expand ((closed-inv-all v0 tenv locals lmap used2))
  :use ((:instance closed-inv-at-when-closed-inv
                   (v (closed-inv-all-witness v0 tenv locals lmap used2)))
        (:instance placement-inv-when-more-used-and-locals
                   (v (closed-inv-all-witness v0 tenv locals lmap used2))
                   (locals2 locals))))

; Under parameters, which are not free in a replacement.

(defruled closed-inv-of-params
  (implies (and (closed-inv v0 tenv locals lmap used)
                (set::subset used used2)
                (string-setp locals)
                (none-in-p (var+type?-list->var params)
                           (string-expr-map-free-expr-vars lmap))
                (all-in-p (var+type?-list->var params) v0)
                (equal keys (var+type?-list->var params)))
           (closed-inv v0
                       (extend-tenv-with-params params tenv)
                       (locals-with-params params locals)
                       (string-expr-map-remove-keys keys lmap)
                       used2))
  :enable (closed-inv closed-inv-at set::subset-in in-fv-of-remove-keys
           not-in-when-member-and-none-in-p in-when-member-and-all-in-p)
  :expand ((closed-inv-all v0
                           (extend-tenv-with-params params tenv)
                           (locals-with-params params locals)
                           (string-expr-map-remove-keys
                            (var+type?-list->var params) lmap)
                           used2))
  :use ((:instance closed-inv-at-when-closed-inv
                   (v (closed-inv-all-witness
                       v0
                       (extend-tenv-with-params params tenv)
                       (locals-with-params params locals)
                       (string-expr-map-remove-keys
                        (var+type?-list->var params) lmap)
                       used2)))
        (:instance placement-inv-of-remove-keys-when-more-used-and-locals
                   (v (closed-inv-all-witness
                       v0
                       (extend-tenv-with-params params tenv)
                       (locals-with-params params locals)
                       (string-expr-map-remove-keys
                        (var+type?-list->var params) lmap)
                       used2))
                   (locals2 (locals-with-params params locals))
                   (keys (var+type?-list->var params)))
        (:instance in-fv-of-remove-keys
                   (v (closed-inv-all-witness
                       v0
                       (extend-tenv-with-params params tenv)
                       (locals-with-params params locals)
                       (string-expr-map-remove-keys
                        (var+type?-list->var params) lmap)
                       used2))
                   (keys (var+type?-list->var params))
                   (m lmap))
        (:instance not-in-when-member-and-none-in-p
                   (p (closed-inv-all-witness
                       v0
                       (extend-tenv-with-params params tenv)
                       (locals-with-params params locals)
                       (string-expr-map-remove-keys
                        (var+type?-list->var params) lmap)
                       used2))
                   (names (var+type?-list->var params))
                   (s (string-expr-map-free-expr-vars lmap)))))

; Under the variable of an unboxing, which is not free in a replacement.

(defruled closed-inv-of-unbox
  (implies (and (closed-inv v0 tenv locals lmap used)
                (set::subset used used2)
                (string-setp locals)
                (not (set::in var (string-expr-map-free-expr-vars lmap)))
                (set::in var v0))
           (closed-inv v0
                       tenv
                       (set::insert var locals)
                       (string-expr-map-remove-keys (list var) lmap)
                       used2))
  :enable (closed-inv closed-inv-at set::subset-in in-fv-of-remove-keys)
  :expand ((closed-inv-all v0
                           tenv
                           (set::insert var locals)
                           (string-expr-map-remove-keys (list var) lmap)
                           used2))
  :use ((:instance closed-inv-at-when-closed-inv
                   (v (closed-inv-all-witness
                       v0 tenv (set::insert var locals)
                       (string-expr-map-remove-keys (list var) lmap)
                       used2)))
        (:instance placement-inv-of-remove-keys-when-more-used-and-locals
                   (v (closed-inv-all-witness
                       v0 tenv (set::insert var locals)
                       (string-expr-map-remove-keys (list var) lmap)
                       used2))
                   (locals2 (set::insert var locals))
                   (keys (list var)))))

; The variable a binding binds, if its name is not local, is not free in a
; replacement.

(defruled not-in-fv-when-in-bind-bound-expr-vars
  (implies (and (closed-inv v0 tenv locals lmap used)
                (not (set::in (bind-name b) locals))
                (set::subset (bind-all-expr-vars b) v0)
                (set::in v (bind-bound-expr-vars b)))
           (not (set::in v (string-expr-map-free-expr-vars lmap))))
  :use ((:instance not-in-fv-when-closed-inv (p v))
        in-all-expr-vars-when-in-bind-bound-expr-vars
        (:instance set::subset-in
                   (set::a v) (set::x (bind-all-expr-vars b)) (set::y v0)))
  :disable in-all-expr-vars-when-in-bind-bound-expr-vars)

; After a binding of a :LET that is kept, whose name is not local.

(defruled closed-inv-of-kept-bind
  (implies (and (closed-inv v0 tenv locals lmap used)
                (set::subset used used2)
                (string-setp locals)
                (not (set::in (bind-name b) locals))
                (set::subset (bind-all-expr-vars b) v0))
           (closed-inv v0
                       (mv-nth 0 (extend-tenv-with-let-bind (bind-fix b) tenv tlets locals))
                       (set::union (bind-bound-expr-vars b) locals)
                       (string-expr-map-remove-keys (bind-bound-expr-vars b) lmap)
                       used2))
  :enable (closed-inv closed-inv-at set::subset-in)
  :expand ((closed-inv-all v0
                           (mv-nth 0 (extend-tenv-with-let-bind (bind-fix b) tenv tlets locals))
                           (set::union (bind-bound-expr-vars b) locals)
                           (string-expr-map-remove-keys (bind-bound-expr-vars b) lmap)
                           used2)
           (:free (x) (bind-list-bound-expr-vars (list x)))
           (bind-list-bound-expr-vars nil))
  :use ((:instance closed-inv-at-when-closed-inv
                   (v (closed-inv-all-witness
                       v0
                       (mv-nth 0 (extend-tenv-with-let-bind (bind-fix b) tenv tlets locals))
                       (set::union (bind-bound-expr-vars b) locals)
                       (string-expr-map-remove-keys (bind-bound-expr-vars b) lmap)
                       used2)))
        (:instance placement-inv-of-remove-keys-when-more-used-and-locals
                   (v (closed-inv-all-witness
                       v0
                       (mv-nth 0 (extend-tenv-with-let-bind (bind-fix b) tenv tlets locals))
                       (set::union (bind-bound-expr-vars b) locals)
                       (string-expr-map-remove-keys (bind-bound-expr-vars b) lmap)
                       used2))
                   (locals2 (set::union (bind-bound-expr-vars b) locals))
                   (keys (bind-bound-expr-vars b)))
        (:instance in-fv-of-remove-keys
                   (v (closed-inv-all-witness
                       v0
                       (mv-nth 0 (extend-tenv-with-let-bind (bind-fix b) tenv tlets locals))
                       (set::union (bind-bound-expr-vars b) locals)
                       (string-expr-map-remove-keys (bind-bound-expr-vars b) lmap)
                       used2))
                   (keys (bind-bound-expr-vars b))
                   (m lmap))
        (:instance not-in-fv-when-in-bind-bound-expr-vars
                   (v (closed-inv-all-witness
                       v0
                       (mv-nth 0 (extend-tenv-with-let-bind (bind-fix b) tenv tlets locals))
                       (set::union (bind-bound-expr-vars b) locals)
                       (string-expr-map-remove-keys (bind-bound-expr-vars b) lmap)
                       used2)))
        (:instance in-all-expr-vars-when-in-bind-bound-expr-vars
                   (v (closed-inv-all-witness
                       v0
                       (mv-nth 0 (extend-tenv-with-let-bind (bind-fix b) tenv tlets locals))
                       (set::union (bind-bound-expr-vars b) locals)
                       (string-expr-map-remove-keys (bind-bound-expr-vars b) lmap)
                       used2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The variables a hoisted function captures have closed types.

(defruled captured-params-closed-p-when-hoisted
  (implies (mv-nth 0 (hoist-local-fun b rebound tenv locals used))
           (captured-params-closed-p
            (set::intersect (bind-free-expr-vars b) locals) tenv))
  :enable hoist-local-fun)

(defruled param-type-closed-p-when-captured-by-hoisted
  (implies (and (mv-nth 0 (hoist-local-fun b rebound tenv locals used))
                (set::in v (bind-free-expr-vars b))
                (set::in v locals))
           (param-type-closed-p v tenv))
  :use (captured-params-closed-p-when-hoisted
        (:instance params-closed-on-necc
                   (s (set::intersect (bind-free-expr-vars b) locals)))))

; A hoisted definition is closed in type and ispace variables.

(defrule closed-of-hoisted-of-hoist-local-fun
  (implies (mv-nth 0 (hoist-local-fun b rebound tenv locals used))
           (and (set::emptyp (bind-free-type-vars
                              (mv-nth 2 (hoist-local-fun b rebound tenv locals used))))
                (set::emptyp (bind-free-ispace-vars
                              (mv-nth 2 (hoist-local-fun b rebound tenv locals used))))))
  :use (captured-params-closed-p-when-hoisted
        hoist-local-fun-when-hoisted-pieces)
  :enable (hoist-local-fun captured-params-closed-p)
  :disable hoist-local-fun-when-hoisted-pieces
  :expand ((:free (w ps ty e) (bind-free-type-vars (bind-fun w ps ty e)))
           (:free (w ps ty e) (bind-free-ispace-vars (bind-fun w ps ty e)))))

; The invariant after a binding is hoisted, first for one variable.

(defrule stringp-and-exprp-of-hoist-local-fun
  (and (stringp (mv-nth 1 (hoist-local-fun b rebound tenv locals used)))
       (exprp (mv-nth 3 (hoist-local-fun b rebound tenv locals used))))
  :enable hoist-local-fun)

(defruled replacement-closed-when-hoisted
  (implies (mv-nth 0 (hoist-local-fun b rebound tenv locals used))
           (and (equal (expr-free-type-vars
                        (mv-nth 3 (hoist-local-fun b rebound tenv locals used)))
                       nil)
                (equal (expr-free-ispace-vars
                        (mv-nth 3 (hoist-local-fun b rebound tenv locals used)))
                       nil)))
  :use hoist-local-fun-when-hoisted
  :disable hoist-local-fun-when-hoisted)

; A hoisted binding's function name is the binding's name.

(defruled bind-fun->var-of-ll-bind-when-hoisted
  (implies (mv-nth 0 (hoist-local-fun
                      (mv-nth 0 (ll-bind (bind-fix x) tenv tlets locals lmap used))
                      rebound tenv2 locals2 used2))
           (equal (bind-fun->var (mv-nth 0 (ll-bind (bind-fix x) tenv tlets locals lmap used)))
                  (bind-name x)))
  :use (bind-bound-expr-vars-when-ll-bind-hoisted
        (:instance in-of-bind-bound-expr-vars
                   (v (bind-fun->var (mv-nth 0 (ll-bind (bind-fix x) tenv tlets locals lmap used))))
                   (b x)))
  :disable in-of-bind-bound-expr-vars)

(defruled bind-name-in-bind-bound-expr-vars-when-hoisted
  (implies (mv-nth 0 (hoist-local-fun
                      (mv-nth 0 (ll-bind (bind-fix x) tenv tlets locals lmap used))
                      rebound tenv2 locals2 used2))
           (set::in (bind-name x) (bind-bound-expr-vars x)))
  :use (bind-bound-expr-vars-when-ll-bind-hoisted
        bind-fun->var-of-ll-bind-when-hoisted)
  :disable in-of-bind-bound-expr-vars)

(defruled closed-inv-at-of-hoisted-bind
  (b* ((new-b (mv-nth 0 (ll-bind (bind-fix x) tenv tlets locals lmap used)))
       (used1 (mv-nth 2 (ll-bind (bind-fix x) tenv tlets locals lmap used)))
       (var (bind-fun->var new-b))
       (val (mv-nth 3 (hoist-local-fun new-b rebound tenv locals used1))))
    (implies (and (closed-inv v0 tenv locals lmap used)
                  (string-setp used)
                  (string-setp locals)
                  (string-expr-mapp lmap)
                  (mv-nth 0 (hoist-local-fun new-b rebound tenv locals used1))
                  (not (set::in (bind-name x) locals))
                  (set::subset (bind-all-expr-vars x) v0))
             (closed-inv-at w v0
                            (mv-nth 0 (extend-tenv-with-let-bind (bind-fix x) tenv tlets locals))
                            (set::insert var locals)
                            (omap::update var val lmap)
                            (set::insert (fresh-expr-var var used1) used1))))
  :enable (closed-inv-at placement-inv set::subset-in
           bind-fun->var-of-ll-bind-when-hoisted
           in-free-of-replacement-of-hoist-local-fun-2
           in-fv-of-update-equal
           in-fv-when-in-fv-of-delete)
  :expand ((:free (y) (bind-list-bound-expr-vars (list y)))
           (bind-list-bound-expr-vars nil))
  :cases ((equal w (bind-name x)))
  :use ((:instance closed-inv-at-when-closed-inv (v w))
        (:instance placement-inv-of-hoisting-gen
                   (v w)
                   (b (bind-fix x))
                   (used2 (set::insert
                           (fresh-expr-var
                            (bind-fun->var
                             (mv-nth 0 (ll-bind (bind-fix x) tenv tlets locals lmap used)))
                            (mv-nth 2 (ll-bind (bind-fix x) tenv tlets locals lmap used)))
                           (mv-nth 2 (ll-bind (bind-fix x) tenv tlets locals lmap used))))
                   (locals2 (set::insert
                             (bind-fun->var
                              (mv-nth 0 (ll-bind (bind-fix x) tenv tlets locals lmap used)))
                             locals))
                   (k (bind-fun->var
                       (mv-nth 0 (ll-bind (bind-fix x) tenv tlets locals lmap used))))
                   (val (mv-nth 3 (hoist-local-fun
                                   (mv-nth 0 (ll-bind (bind-fix x) tenv tlets locals lmap used))
                                   rebound tenv locals
                                   (mv-nth 2 (ll-bind (bind-fix x) tenv tlets locals lmap used))))))
        (:instance bind-bound-expr-vars-when-ll-bind-hoisted
                   (tenv2 tenv) (locals2 locals)
                   (used2 (mv-nth 2 (ll-bind (bind-fix x) tenv tlets locals lmap used))))
        (:instance used-of-ll-bind (x (bind-fix x)))
        (:instance param-type-closed-p-when-captured-by-hoisted
                   (v w)
                   (b (mv-nth 0 (ll-bind (bind-fix x) tenv tlets locals lmap used)))
                   (used (mv-nth 2 (ll-bind (bind-fix x) tenv tlets locals lmap used))))
        (:instance not-in-fv-when-in-bind-bound-expr-vars
                   (v w) (b x))
        (:instance in-all-expr-vars-when-in-bind-bound-expr-vars
                   (v w) (b x))
        (:instance bind-name-in-bind-bound-expr-vars-when-hoisted
                   (tenv2 tenv) (locals2 locals)
                   (used2 (mv-nth 2 (ll-bind (bind-fix x) tenv tlets locals lmap used))))
        (:instance in-all-expr-vars-when-in-bind-bound-expr-vars
                   (v (bind-name x)) (b x)))
  :disable (used-of-ll-bind
            in-all-expr-vars-when-in-bind-bound-expr-vars))

(defruled closed-inv-of-hoisted-bind
  (b* ((new-b (mv-nth 0 (ll-bind (bind-fix x) tenv tlets locals lmap used)))
       (used1 (mv-nth 2 (ll-bind (bind-fix x) tenv tlets locals lmap used))))
    (implies (and (closed-inv v0 tenv locals lmap used)
                  (string-setp used)
                  (string-setp locals)
                  (string-expr-mapp lmap)
                  (mv-nth 0 (hoist-local-fun new-b rebound tenv locals used1))
                  (not (set::in (bind-name x) locals))
                  (set::subset (bind-all-expr-vars x) v0)
                  (equal used2
                         (set::insert (fresh-expr-var (bind-fun->var new-b) used1)
                                      used1))
                  (equal locals2 (set::insert (bind-fun->var new-b) locals))
                  (equal k (bind-fun->var new-b))
                  (equal val (mv-nth 3 (hoist-local-fun new-b rebound tenv locals used1))))
             (closed-inv v0 (mv-nth 0 (extend-tenv-with-let-bind (bind-fix x) tenv tlets locals)) locals2 (omap::update k val lmap) used2)))
  :enable closed-inv
  :expand ((closed-inv-all v0 (mv-nth 0 (extend-tenv-with-let-bind (bind-fix x) tenv tlets locals)) locals2 (omap::update k val lmap) used2))
  :use ((:instance closed-inv-at-of-hoisted-bind
                   (w (closed-inv-all-witness
                       v0 (mv-nth 0 (extend-tenv-with-let-bind (bind-fix x) tenv tlets locals)) locals2 (omap::update k val lmap) used2)))
        (:instance lmap-closed-p-of-update (name k) (e val))
        (:instance replacement-closed-when-hoisted
                   (b (mv-nth 0 (ll-bind (bind-fix x) tenv tlets locals lmap used)))
                   (used (mv-nth 2 (ll-bind (bind-fix x) tenv tlets locals lmap used))))))

; The invariant with the environments fixed.

(defruled closed-inv-of-string-type-map-fix
  (implies (closed-inv v0 tenv locals lmap used)
           (closed-inv v0 (string-type-map-fix tenv) locals lmap used))
  :enable (closed-inv closed-inv-at)
  :expand ((closed-inv-all v0 (string-type-map-fix tenv) locals lmap used))
  :use ((:instance closed-inv-at-when-closed-inv
                   (v (closed-inv-all-witness v0 (string-type-map-fix tenv)
                                              locals lmap used)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The variables a lambda would capture, among those free in BODY, have
; closed types.

(acl2::defun-sk cap-closed-p (params body locals tenv)
  (forall (v)
          (implies (and (set::in v (expr-free-expr-vars body))
                        (not (member-equal v (var+type?-list->var params)))
                        (set::in v locals))
                   (param-type-closed-p v tenv))))

(in-theory (disable cap-closed-p))

(defrule cap-closed-p-of-var+type?-list-fix
  (equal (cap-closed-p (var+type?-list-fix params) body locals tenv)
         (cap-closed-p params body locals tenv))
  :use ((:instance cap-closed-p-necc
                   (v (cap-closed-p-witness (var+type?-list-fix params)
                                            body locals tenv)))
        (:instance cap-closed-p-necc
                   (params (var+type?-list-fix params))
                   (v (cap-closed-p-witness params body locals tenv))))
  :expand ((cap-closed-p (var+type?-list-fix params) body locals tenv)
           (cap-closed-p params body locals tenv)))

; At the lifting of a lambda, from the check of LIFTABLE-LAMBDA-P.

(defrule cap-closed-p-when-lambda
  (implies (and (equal (atom-kind a) :lambda)
                (string-setp locals)
                (captured-params-closed-p
                 (set::intersect (atom-free-expr-vars a) (string-sfix locals))
                 tenv))
           (cap-closed-p (list (atom-lambda->param a))
                         (atom-lambda->body a)
                         locals tenv))
  :expand ((cap-closed-p (list (atom-lambda->param a))
                         (atom-lambda->body a)
                         locals tenv)
           (atom-free-expr-vars a))
  :use ((:instance params-closed-on-necc
                   (s (set::intersect (atom-free-expr-vars a) locals))
                   (v (cap-closed-p-witness (list (atom-lambda->param a))
                                            (atom-lambda->body a)
                                            locals tenv)))))

(defrule cap-closed-p-when-lambdan
  (implies (and (equal (atom-kind a) :lambdan)
                (string-setp locals)
                (captured-params-closed-p
                 (set::intersect (atom-free-expr-vars a) (string-sfix locals))
                 tenv))
           (cap-closed-p (atom-lambdan->params a)
                         (atom-lambdan->body a)
                         locals tenv))
  :expand ((cap-closed-p (atom-lambdan->params a)
                         (atom-lambdan->body a)
                         locals tenv)
           (atom-free-expr-vars a))
  :use ((:instance params-closed-on-necc
                   (s (set::intersect (atom-free-expr-vars a) locals))
                   (v (cap-closed-p-witness (atom-lambdan->params a)
                                            (atom-lambdan->body a)
                                            locals tenv)))))

; Under the parameters.

(defrule cap-closed-p-of-params
  (implies (and (cap-closed-p params body locals tenv)
                (string-setp locals))
           (cap-closed-p params body
                         (locals-with-params params locals)
                         (extend-tenv-with-params params tenv)))
  :expand ((cap-closed-p params body
                         (locals-with-params params locals)
                         (extend-tenv-with-params params tenv)))
  :use ((:instance cap-closed-p-necc
                   (v (cap-closed-p-witness params body
                                            (locals-with-params params locals)
                                            (extend-tenv-with-params params tenv))))))

; A nested lambda's parameters are added.

(defrule cap-closed-p-of-nested-lambda
  (implies (and (cap-closed-p params body locals tenv)
                (string-setp locals)
                (mv-nth 0 (nested-lambda body)))
           (cap-closed-p (append params (mv-nth 1 (nested-lambda body)))
                         (mv-nth 2 (nested-lambda body))
                         (locals-with-params params locals)
                         (extend-tenv-with-params params tenv)))
  :expand ((cap-closed-p (append params (mv-nth 1 (nested-lambda body)))
                         (mv-nth 2 (nested-lambda body))
                         (locals-with-params params locals)
                         (extend-tenv-with-params params tenv)))
  :enable in-of-free-of-nested-lambda-body
  :use ((:instance cap-closed-p-necc
                   (v (cap-closed-p-witness
                       (append params (mv-nth 1 (nested-lambda body)))
                       (mv-nth 2 (nested-lambda body))
                       (locals-with-params params locals)
                       (extend-tenv-with-params params tenv))))))

; After the body is lifted out of: a variable free in the rebuilt body is
; free in the body, or local and free in a replacement (and so has a
; closed type by the invariant), or the name of a lifted definition, which
; is not local.

(defrule cap-closed-p-of-ll-expr
  (implies (and (string-setp locals)
                (string-setp used)
                (string-expr-mapp lmap)
                (closed-inv v0 tenv locals lmap used)
                (cap-closed-p params body locals tenv))
           (cap-closed-p params
                         (mv-nth 0 (ll-expr body tenv tlets locals lmap used))
                         locals tenv))
  :expand ((cap-closed-p params
                         (mv-nth 0 (ll-expr body tenv tlets locals lmap used))
                         locals tenv))
  :enable closed-inv-at
  :use ((:instance cap-closed-p-necc
                   (v (cap-closed-p-witness
                       params
                       (mv-nth 0 (ll-expr body tenv tlets locals lmap used))
                       locals tenv)))
        (:instance closed-inv-at-when-closed-inv
                   (v (cap-closed-p-witness
                       params
                       (mv-nth 0 (ll-expr body tenv tlets locals lmap used))
                       locals tenv)))
        (:instance placement-inv-when-closed-inv
                   (v (cap-closed-p-witness
                       params
                       (mv-nth 0 (ll-expr body tenv tlets locals lmap used))
                       locals tenv)))
        (:instance rebuilt-free-vars-of-ll-expr
                   (x body)
                   (v (cap-closed-p-witness
                       params
                       (mv-nth 0 (ll-expr body tenv tlets locals lmap used))
                       locals tenv))))
  :disable rebuilt-free-vars-of-ll-expr)

; The definition of a lifted lambda is closed.

(defrule binds-closed-p-of-emit-lifted-lambda
  (implies (and (cap-closed-p params body locals tenv)
                (set::emptyp (var+type?-list-free-type-vars params))
                (set::emptyp (var+type?-list-free-ispace-vars params))
                (set::emptyp (expr-free-type-vars body))
                (set::emptyp (expr-free-ispace-vars body))
                (set::emptyp (type-option-free-type-vars type?))
                (set::emptyp (type-option-free-ispace-vars type?)))
           (binds-closed-p (mv-nth 1 (emit-lifted-lambda params body type? tenv locals used))))
  :enable (emit-lifted-lambda captured-params-closed-p)
  :expand ((:free (w ps ty e) (bind-free-type-vars (bind-fun w ps ty e)))
           (:free (w ps ty e) (bind-free-ispace-vars (bind-fun w ps ty e)))
           (params-closed-on
            (set::intersect (set::difference (expr-free-expr-vars body)
                                             (set::mergesort
                                              (var+type?-list->var params)))
                            locals)
            tenv))
  :use ((:instance captured-params-closed-p-when-params-closed-on
                   (s (set::intersect (set::difference (expr-free-expr-vars body)
                                                       (set::mergesort
                                                        (var+type?-list->var params)))
                                      locals)))
        (:instance cap-closed-p-necc
                   (v (params-closed-on-witness
                       (set::intersect (set::difference (expr-free-expr-vars body)
                                                        (set::mergesort
                                                         (var+type?-list->var params)))
                                       locals)
                       tenv))))
  :disable captured-params-closed-p-when-params-closed-on)

; A lambda whose body is a lambda: binder names, all variables, and free
; type and ispace variables.

(defrule expr-binder-names-of-nested-lambda-body
  (b* (((mv nestedp more inner &) (nested-lambda body)))
    (implies nestedp
             (equal (expr-binder-names body)
                    (append (var+type?-list->var more)
                            (expr-binder-names inner)))))
  :enable nested-lambda
  :expand ((expr-binder-names body)
           (atom-binder-names (expr-atom->atom body))))

(defrule subset-of-expr-all-expr-vars-of-nested-lambda-body
  (b* (((mv nestedp more inner &) (nested-lambda body)))
    (implies nestedp
             (equal (set::subset (expr-all-expr-vars body) s)
                    (and (all-in-p (var+type?-list->var more) s)
                         (set::subset (expr-all-expr-vars inner) s)))))
  :enable (nested-lambda subset-of-union)
  :expand ((expr-all-expr-vars body)
           (atom-all-expr-vars (expr-atom->atom body))))

(defrule free-vars-of-nested-lambda-body-when-closed
  (b* (((mv nestedp more inner type?) (nested-lambda body)))
    (implies (and nestedp
                  (set::emptyp (expr-free-type-vars body))
                  (set::emptyp (expr-free-ispace-vars body)))
             (and (set::emptyp (var+type?-list-free-type-vars more))
                  (set::emptyp (var+type?-list-free-ispace-vars more))
                  (set::emptyp (expr-free-type-vars inner))
                  (set::emptyp (expr-free-ispace-vars inner))
                  (set::emptyp (type-option-free-type-vars type?))
                  (set::emptyp (type-option-free-ispace-vars type?)))))
  :enable nested-lambda
  :expand ((expr-free-type-vars body)
           (expr-free-ispace-vars body)
           (atom-free-type-vars (expr-atom->atom body))
           (atom-free-ispace-vars (expr-atom->atom body))
           (:free (x y) (var+type?-list-free-type-vars (cons x y)))
           (:free (x y) (var+type?-list-free-ispace-vars (cons x y)))
           (var+type?-list-free-type-vars nil)
           (var+type?-list-free-ispace-vars nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The binders of the body of a :LET are not local after its bindings, if
; they are not local before and not bound by the bindings.

(defrule none-in-p-of-ll-let-binds-locals
  (implies (and (string-expr-mapp lmap)
                (none-in-p names (string-sfix locals))
                (not (intersectp-equal names (bind-list-names binds))))
           (none-in-p names (mv-nth 3 (ll-let-binds binds body-binders
                                                    tenv tlets locals lmap used))))
  :induct (len names)
  :enable (none-in-p intersectp-equal)
  :disable intersectp-equal-commute)

; Names other than a binding's name are not bound by it.

(defrule none-in-p-of-bind-bound-expr-vars
  (implies (not (member-equal (bind-name b) names))
           (none-in-p names (bind-bound-expr-vars b)))
  :induct (len names)
  :enable none-in-p)

; Stage D: the definitions lifted out of a node are closed in type and
; ispace variables, provided the binders of the node bind distinct names
; that are not local and are among the names V0 in use at the start, and
; the invariant holds.  A lambda is lifted with the environments extended
; with its parameters, for which the invariant is stated.

(defret-mutual closed-lifted-of-lambda-lift-exprs/atoms/binds
  (defret closed-lifted-of-ll-expr
    (implies (and (string-setp locals)
                  (string-setp used)
                  (string-expr-mapp lmap)
                  (closed-inv v0 tenv locals lmap used)
                  (no-duplicatesp-equal (expr-binder-names x))
                  (none-in-p (expr-binder-names x) locals)
                  (set::subset (expr-all-expr-vars x) v0))
             (binds-closed-p lifted))
    :fn ll-expr)
  (defret closed-lifted-of-ll-lambda
    (implies (and (string-setp locals)
                  (string-setp used)
                  (string-expr-mapp lmap)
                  (closed-inv v0
                              (extend-tenv-with-params (var+type?-list-fix params) tenv)
                              (locals-with-params (var+type?-list-fix params) locals)
                              (string-expr-map-remove-keys
                               (var+type?-list->var params) lmap)
                              used)
                  (none-in-p (var+type?-list->var params)
                             (string-expr-map-free-expr-vars
                              (string-expr-map-remove-keys
                               (var+type?-list->var params) lmap)))
                  (no-duplicatesp-equal (append (var+type?-list->var params)
                                                (expr-binder-names body)))
                  (none-in-p (expr-binder-names body) locals)
                  (all-in-p (var+type?-list->var params) v0)
                  (set::subset (expr-all-expr-vars body) v0)
                  (cap-closed-p params body locals tenv)
                  (set::emptyp (var+type?-list-free-type-vars params))
                  (set::emptyp (var+type?-list-free-ispace-vars params))
                  (set::emptyp (expr-free-type-vars body))
                  (set::emptyp (expr-free-ispace-vars body))
                  (set::emptyp (type-option-free-type-vars type?))
                  (set::emptyp (type-option-free-ispace-vars type?)))
             (binds-closed-p lifted))
    :fn ll-lambda)
  (defret closed-lifted-of-ll-let-binds
    (implies (and (string-setp locals)
                  (string-setp used)
                  (string-expr-mapp lmap)
                  (closed-inv v0 tenv locals lmap used)
                  (no-duplicatesp-equal (append (bind-list-names binds)
                                                (bind-list-binder-names binds)))
                  (none-in-p (append (bind-list-names binds)
                                     (bind-list-binder-names binds))
                             locals)
                  (set::subset (bind-list-all-expr-vars binds) v0))
             (and (binds-closed-p lifted)
                  (closed-inv v0 new-tenv new-locals new-lmap new-used)))
    :fn ll-let-binds)
  (defret closed-lifted-of-ll-expr-list
    (implies (and (string-setp locals)
                  (string-setp used)
                  (string-expr-mapp lmap)
                  (closed-inv v0 tenv locals lmap used)
                  (no-duplicatesp-equal (expr-list-binder-names x))
                  (none-in-p (expr-list-binder-names x) locals)
                  (set::subset (expr-list-all-expr-vars x) v0))
             (binds-closed-p lifted))
    :fn ll-expr-list)
  (defret closed-lifted-of-ll-atom
    (implies (and (string-setp locals)
                  (string-setp used)
                  (string-expr-mapp lmap)
                  (closed-inv v0 tenv locals lmap used)
                  (no-duplicatesp-equal (atom-binder-names x))
                  (none-in-p (atom-binder-names x) locals)
                  (set::subset (atom-all-expr-vars x) v0))
             (binds-closed-p lifted))
    :fn ll-atom)
  (defret closed-lifted-of-ll-atom-list
    (implies (and (string-setp locals)
                  (string-setp used)
                  (string-expr-mapp lmap)
                  (closed-inv v0 tenv locals lmap used)
                  (no-duplicatesp-equal (atom-list-binder-names x))
                  (none-in-p (atom-list-binder-names x) locals)
                  (set::subset (atom-list-all-expr-vars x) v0))
             (binds-closed-p lifted))
    :fn ll-atom-list)
  (defret closed-lifted-of-ll-bind
    (implies (and (string-setp locals)
                  (string-setp used)
                  (string-expr-mapp lmap)
                  (closed-inv v0 tenv locals lmap used)
                  (no-duplicatesp-equal (bind-binder-names x))
                  (none-in-p (bind-binder-names x) locals)
                  (set::subset (bind-all-expr-vars x) v0))
             (binds-closed-p lifted))
    :fn ll-bind)
  :mutual-recursion lambda-lift-exprs/atoms/binds
  :hints (("Goal"
           :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (e/d (liftable-lambda-p
                            subset-of-union
                            closed-inv-when-more-used
                            closed-inv-of-params
                            closed-inv-of-unbox
                            closed-inv-of-kept-bind
                            closed-inv-of-hoisted-bind
                            closed-inv-of-string-type-map-fix
                            not-in-fv-when-closed-inv
                            none-in-p-fv-when-closed-inv
                            lmap-closed-p-when-closed-inv
                            bind-bound-expr-vars-when-ll-bind-hoisted
                            bind-fun->var-of-ll-bind-when-hoisted)
                           (emit-lifted-lambda
                            hoist-local-fun
                            apply-to-names
                            bind-bound-expr-vars
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
                    (expr-binder-names x)
                    (atom-binder-names x)
                    (atom-binder-names (expr-atom->atom x))
                    (bind-binder-names x)
                    (expr-list-binder-names x)
                    (atom-list-binder-names x)
                    (bind-list-binder-names binds)
                    (bind-list-names binds)
                    (expr-all-expr-vars x)
                    (atom-all-expr-vars x)
                    (atom-all-expr-vars (expr-atom->atom x))
                    (bind-all-expr-vars x)
                    (expr-list-all-expr-vars x)
                    (atom-list-all-expr-vars x)
                    (bind-list-all-expr-vars binds)
                    (atom-free-type-vars (expr-atom->atom x))
                    (atom-free-ispace-vars (expr-atom->atom x))
                    (:free (p l) (var+type?-list-free-type-vars (cons p l)))
                    (:free (p l) (var+type?-list-free-ispace-vars (cons p l)))
                    (var+type?-list-free-type-vars nil)
                    (var+type?-list-free-ispace-vars nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The closedness theorems.

; An expression whose binders bind distinct names: the definitions lifted
; out of it are closed, so lifting adds no free type or ispace variables.

(defrule binds-closed-p-of-lifted-of-lambda-lift-top-expr
  (implies (not (expr-duplicate-names x))
           (binds-closed-p (mv-nth 1 (ll-expr x nil nil nil nil (expr-all-expr-vars x)))))
  :enable expr-duplicate-names
  :use ((:instance closed-lifted-of-ll-expr
                   (tenv nil) (tlets nil) (locals nil) (lmap nil)
                   (used (expr-all-expr-vars x))
                   (v0 (expr-all-expr-vars x)))))

(defrule expr-free-type-vars-of-lambda-lift-top-expr-when-unique
  (implies (not (expr-duplicate-names x))
           (equal (expr-free-type-vars (lambda-lift-top-expr x))
                  (expr-free-type-vars x)))
  :use binds-closed-p-of-lifted-of-lambda-lift-top-expr
  :disable binds-closed-p-of-lifted-of-lambda-lift-top-expr)

(defrule expr-free-ispace-vars-of-lambda-lift-top-expr-when-unique
  (implies (not (expr-duplicate-names x))
           (equal (expr-free-ispace-vars (lambda-lift-top-expr x))
                  (expr-free-ispace-vars x)))
  :use binds-closed-p-of-lifted-of-lambda-lift-top-expr
  :disable binds-closed-p-of-lifted-of-lambda-lift-top-expr)

; Top-level bindings whose binders bind distinct names: the definitions
; lifted out of each are closed, and so is each rebuilt binding if the
; original is.  So if every binding is closed, as the declarations of a
; well-formed file are, so is every binding of the result.

(defrule binds-closed-p-of-lambda-lift-top-binds
  (implies (and (binds-closed-p binds)
                (no-duplicatesp-equal (bind-list-binder-names binds))
                (string-setp used)
                (set::subset (bind-list-all-expr-vars binds) used))
           (binds-closed-p (lambda-lift-top-binds binds used)))
  :induct (lambda-lift-top-binds binds used)
  :enable (lambda-lift-top-binds binds-closed-p subset-of-union)
  :expand ((bind-list-binder-names binds)
           (bind-list-all-expr-vars binds))
  :hints (("Subgoal *1/2"
           :use ((:instance closed-lifted-of-ll-bind
                            (x (car binds)) (tenv nil) (tlets nil) (locals nil) (lmap nil)
                            (v0 used))
                 (:instance free-type/ispace-vars-of-ll-bind
                            (x (car binds)) (tenv nil) (tlets nil) (locals nil) (lmap nil))
                 (:instance used-subset-of-ll-bind
                            (x (car binds)) (tenv nil) (tlets nil) (locals nil) (lmap nil))
                 (:instance set::subset-transitive
                            (set::x (bind-list-all-expr-vars (cdr binds)))
                            (set::y used)
                            (set::z (mv-nth 2 (ll-bind (car binds) nil nil nil nil used)))))
           :in-theory (e/d (binds-closed-p subset-of-union)
                           (closed-lifted-of-ll-bind
                            free-type/ispace-vars-of-ll-bind
                            used-subset-of-ll-bind)))))

(defrule binds-closed-p-of-lambda-lift-file
  (implies (and (not (file-duplicate-names f))
                (binds-closed-p (decl-list-to-binds (file->decls f))))
           (binds-closed-p (decl-list-to-binds (file->decls (lambda-lift-file f)))))
  :enable (lambda-lift-file file-duplicate-names)
  :use ((:instance no-duplicatesp-equal-when-not-duplicated-names
                   (names (b* ((binds (decl-list-to-binds (file->decls f))))
                            (append (bind-list-names binds)
                                    (bind-list-binder-names binds)))))))
