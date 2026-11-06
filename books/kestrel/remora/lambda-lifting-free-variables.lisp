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
(include-book "bound-variable-operations")

(include-book "portcullis")

(local (include-book "osets"))
(local (include-book "std/osets/top" :dir :system))

(local (in-theory (disable (:e tau-system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lambda-lifting-free-variables
  :parents (lambda-lifting)
  :short "Free and bound variables under lambda lifting."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lambda lifting rebuilds an expression around references to the
     definitions it lifts out, and its correctness rests on two facts about
     names: the references introduce no type or ispace variables, and the
     names of the lifted definitions are fresh.  This book proves both, for
     the traversal @(tsee ll-expr) and its companions and for the entry
     point @(tsee lambda-lift-top-expr).")
   (xdoc::p
    (xdoc::b "Free type and ispace variables are preserved."))
   (xdoc::p
    "A lambda is lifted only when it is closed in type and ispace variables
     (see @(tsee liftable-lambda-p)), and the reference that replaces it is
     a variable applied to variables, which has none.  The same holds of a
     hoisted local function and of the expressions that replace its uses,
     which the traversal carries in the map @('lmap'); the hypothesis @('lmap-closed-p') says that the map's values have no free type or ispace
     variables, which holds of the empty map and is preserved as the map
     grows.  So the rebuilt node has exactly the free type and ispace
     variables of the original: @('free-type/ispace-vars-of-ll-expr').
     The lifted definitions themselves are meant to be closed as well ---
     the captured variables are given the types the environment @('tenv')
     assigns them, and the liftability checks require those to be closed
     (see @(tsee captured-params-closed-p)) --- but that is not proved here:
     for a lambda, it rests on the captured variables of the hoisted
     functions the lambda's body uses, which are checked when those are
     hoisted.  So the statements at the top level are that the free
     variables of the result are those of the input together with those of
     the lifted definitions
     (@('expr-free-type-vars-of-lambda-lift-top-expr')), and in
     particular that the input's are all still free
     (@('subset-of-expr-free-type-vars-of-lambda-lift-top-expr')).")
   (xdoc::p
    (xdoc::b "Lifted names are fresh."))
   (xdoc::p
    "The set of names in use only grows along the traversal, and the
     definitions lifted out of a node are bound to names that are in use
     afterwards and were not in use before: @('used-of-ll-expr').  Since
     @(tsee lambda-lift-top-expr) starts from every variable of the input,
     no lifted definition is named like any variable of the input: @('lifted-names-fresh-of-lambda-lift-top-expr').  The lifted definitions
     are all functions, so they bind no type or ispace variables, which is
     what lets the free variables of the nested @(':let') that the entry
     point builds (@(tsee nest-let-binds)) reduce to a union.")
   (xdoc::p
    (xdoc::b "Proof technique."))
   (xdoc::p
    "The free-variable folds of @(see free-variable-operations) do not open
     on a constructed node by themselves, since their recursive calls are on
     the accessors of the constructors; so the proofs expand the fold on
     each constructed form explicitly, and open the traversal on the head of
     a list uniformly."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Free variables of the syntax built by lambda lifting.  The free-variable
; folds do not open on constructed nodes by themselves (the recursive calls
; are on accessors of constructors), so the constructed forms are expanded
; explicitly.

(defrule expr-free-type-vars-of-names-to-exprs
  (equal (expr-list-free-type-vars (names-to-exprs names)) nil)
  :induct t
  :enable (names-to-exprs expr-list-free-type-vars)
  :expand ((:free (n) (expr-free-type-vars (expr-var n)))))

(defrule expr-free-ispace-vars-of-names-to-exprs
  (equal (expr-list-free-ispace-vars (names-to-exprs names)) nil)
  :induct t
  :enable (names-to-exprs expr-list-free-ispace-vars)
  :expand ((:free (n) (expr-free-ispace-vars (expr-var n)))))

(defrule expr-free-expr-vars-of-names-to-exprs
  (equal (expr-list-free-expr-vars (names-to-exprs names))
         (set::mergesort (str::string-list-fix names)))
  :induct t
  :enable (names-to-exprs expr-list-free-expr-vars mergesort-of-cons)
  :expand ((:free (n) (expr-free-expr-vars (expr-var n)))))

(defrule expr-free-type-vars-of-apply-to-names
  (equal (expr-free-type-vars (apply-to-names fun names))
         (expr-free-type-vars fun))
  :enable (apply-to-names len)
  :expand ((len names)
           (len (cdr names))
           (:free (f a) (expr-free-type-vars (expr-app f a)))
           (:free (f as) (expr-free-type-vars (expr-appn f as)))
           (:free (n) (expr-free-type-vars (expr-var n)))))

(defrule expr-free-ispace-vars-of-apply-to-names
  (equal (expr-free-ispace-vars (apply-to-names fun names))
         (expr-free-ispace-vars fun))
  :enable (apply-to-names len)
  :expand ((len names)
           (len (cdr names))
           (:free (f a) (expr-free-ispace-vars (expr-app f a)))
           (:free (f as) (expr-free-ispace-vars (expr-appn f as)))
           (:free (n) (expr-free-ispace-vars (expr-var n)))))

(defrule expr-free-expr-vars-of-apply-to-names
  (equal (expr-free-expr-vars (apply-to-names fun names))
         (set::union (expr-free-expr-vars fun)
                     (set::mergesort (str::string-list-fix names))))
  :enable (apply-to-names mergesort-of-cons len)
  :expand ((len names)
           (len (cdr names))
           (:free (f a) (expr-free-expr-vars (expr-app f a)))
           (:free (f as) (expr-free-expr-vars (expr-appn f as)))
           (:free (n) (expr-free-expr-vars (expr-var n)))))

; The captured variables are a set; as an argument list they are their own
; string-list fix, and their sorted form is themselves.

(defrule mergesort-of-string-list-fix-when-string-setp
  (implies (string-setp s)
           (equal (set::mergesort (str::string-list-fix s)) s))
  :enable (str::string-list-fix set::mergesort-set-identity)
  :use ((:instance acl2::string-listp-when-string-setp (acl2::x s))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The lifting step: the definition of a lambda and the reference that
; replaces it.  The reference has no type or ispace variables; its
; expression variables are the fresh name and the captured variables, which
; are free in the body and not among the parameters; the name is fresh.

; When the lambda is not lifted (see EMIT-LIFTED-LAMBDA), what is returned
; is the lambda itself, no definition, and the names in use unchanged.

(defrule emit-lifted-lambda-when-not-lifted
  (implies (not (consp (mv-nth 1 (emit-lifted-lambda params body type? tenv locals used))))
           (and (equal (mv-nth 0 (emit-lifted-lambda params body type? tenv locals used))
                       (if (consp params)
                           (expr-atom (make-atom-lambda/lambdan
                                       (var+type?-list-fix params)
                                       (expr-fix body)
                                       type?))
                         (expr-fix body)))
                (equal (mv-nth 1 (emit-lifted-lambda params body type? tenv locals used)) nil)
                (equal (mv-nth 2 (emit-lifted-lambda params body type? tenv locals used)) (string-sfix used))))
  :enable emit-lifted-lambda)

(defrule expr-free-type-vars-of-emit-lifted-lambda
  (implies (consp (mv-nth 1 (emit-lifted-lambda params body type? tenv locals used)))
           (equal (expr-free-type-vars (mv-nth 0 (emit-lifted-lambda params body type? tenv locals used)))
                  nil))
  :enable emit-lifted-lambda
  :expand ((:free (n) (expr-free-type-vars (expr-var n)))))

(defrule expr-free-ispace-vars-of-emit-lifted-lambda
  (implies (consp (mv-nth 1 (emit-lifted-lambda params body type? tenv locals used)))
           (equal (expr-free-ispace-vars (mv-nth 0 (emit-lifted-lambda params body type? tenv locals used)))
                  nil))
  :enable emit-lifted-lambda
  :expand ((:free (n) (expr-free-ispace-vars (expr-var n)))))

(defrulel expr-free-type-vars-when-emptyp
  (implies (set::emptyp (expr-free-type-vars x))
           (equal (expr-free-type-vars x) nil))
  :enable set::emptyp)

(defrulel expr-free-ispace-vars-when-emptyp
  (implies (set::emptyp (expr-free-ispace-vars x))
           (equal (expr-free-ispace-vars x) nil))
  :enable set::emptyp)

(defrulel var+type?-free-type-vars-when-emptyp
  (implies (set::emptyp (var+type?-free-type-vars x))
           (equal (var+type?-free-type-vars x) nil))
  :enable set::emptyp)

(defrulel var+type?-free-ispace-vars-when-emptyp
  (implies (set::emptyp (var+type?-free-ispace-vars x))
           (equal (var+type?-free-ispace-vars x) nil))
  :enable set::emptyp)

(defrulel var+type?-list-free-type-vars-when-emptyp
  (implies (set::emptyp (var+type?-list-free-type-vars x))
           (equal (var+type?-list-free-type-vars x) nil))
  :enable set::emptyp)

(defrulel var+type?-list-free-ispace-vars-when-emptyp
  (implies (set::emptyp (var+type?-list-free-ispace-vars x))
           (equal (var+type?-list-free-ispace-vars x) nil))
  :enable set::emptyp)

(defrulel type-option-free-type-vars-when-emptyp
  (implies (set::emptyp (type-option-free-type-vars x))
           (equal (type-option-free-type-vars x) nil))
  :enable set::emptyp)

(defrulel type-option-free-ispace-vars-when-emptyp
  (implies (set::emptyp (type-option-free-ispace-vars x))
           (equal (type-option-free-ispace-vars x) nil))
  :enable set::emptyp)

; Whether or not the lambda is lifted, what replaces it is closed if the
; lambda is.

(defrule free-type/ispace-vars-of-emit-lifted-lambda-when-closed
  (implies (and (set::emptyp (var+type?-list-free-type-vars params))
                (set::emptyp (var+type?-list-free-ispace-vars params))
                (set::emptyp (expr-free-type-vars body))
                (set::emptyp (expr-free-ispace-vars body))
                (set::emptyp (type-option-free-type-vars type?))
                (set::emptyp (type-option-free-ispace-vars type?)))
           (and (equal (expr-free-type-vars
                        (mv-nth 0 (emit-lifted-lambda params body type?
                                                      tenv locals used)))
                       nil)
                (equal (expr-free-ispace-vars
                        (mv-nth 0 (emit-lifted-lambda params body type?
                                                      tenv locals used)))
                       nil)))
  :cases ((consp (mv-nth 1 (emit-lifted-lambda params body type?
                                               tenv locals used))))
  :enable make-atom-lambda/lambdan
  :expand ((var+type?-list-free-type-vars params)
           (var+type?-list-free-ispace-vars params)
           (:free (a) (expr-free-type-vars (expr-atom a)))
           (:free (a) (expr-free-ispace-vars (expr-atom a)))
           (:free (p b ty) (atom-free-type-vars (atom-lambda p b ty)))
           (:free (p b ty) (atom-free-ispace-vars (atom-lambda p b ty)))
           (:free (ps b ty) (atom-free-type-vars (atom-lambdan ps b ty)))
           (:free (ps b ty) (atom-free-ispace-vars (atom-lambdan ps b ty)))
           (:free (x y) (var+type?-list-free-type-vars (cons x y)))
           (:free (x y) (var+type?-list-free-ispace-vars (cons x y)))))

(defrule bind-list-bound-expr-vars-of-emit-lifted-lambda
  (implies (consp (mv-nth 1 (emit-lifted-lambda params body type? tenv locals used)))
           (equal (bind-list-bound-expr-vars (mv-nth 1 (emit-lifted-lambda params body type? tenv locals used)))
                  (set::insert (fresh-expr-var "lam_" (string-sfix used)) nil)))
  :enable (emit-lifted-lambda bind-list-bound-expr-vars bind-bound-expr-vars))

(defrule new-used-of-emit-lifted-lambda
  (implies (consp (mv-nth 1 (emit-lifted-lambda params body type? tenv locals used)))
           (equal (mv-nth 2 (emit-lifted-lambda params body type? tenv locals used))
                  (set::insert (fresh-expr-var "lam_" (string-sfix used)) (string-sfix used))))
  :enable emit-lifted-lambda)

(defrule expr-free-expr-vars-of-emit-lifted-lambda
  (implies (consp (mv-nth 1 (emit-lifted-lambda params body type? tenv locals used)))
           (set::subset (expr-free-expr-vars (mv-nth 0 (emit-lifted-lambda params body type? tenv locals used)))
                        (set::insert (fresh-expr-var "lam_" (string-sfix used))
                                     (set::difference (expr-free-expr-vars body)
                                                      (set::mergesort (var+type?-list->var params))))))
  :enable (emit-lifted-lambda set::pick-a-point-subset-strategy)
  :expand ((:free (n) (expr-free-expr-vars (expr-var n)))))

; Hoisting of a local function.

(defrule hoist-local-fun-when-not-hoisted
  (implies (not (mv-nth 0 (hoist-local-fun b rebound tenv locals used)))
           (and (equal (mv-nth 2 (hoist-local-fun b rebound tenv locals used)) (bind-fix b))
                (equal (mv-nth 4 (hoist-local-fun b rebound tenv locals used)) (string-sfix used))))
  :enable hoist-local-fun)

(defrule hoist-local-fun-when-hoisted
  (implies (mv-nth 0 (hoist-local-fun b rebound tenv locals used))
           (and (equal (bind-kind b) :fun)
                (set::emptyp (bind-free-type-vars b))
                (set::emptyp (bind-free-ispace-vars b))
                (equal (mv-nth 1 (hoist-local-fun b rebound tenv locals used))
                       (bind-fun->var b))
                (equal (bind-bound-expr-vars (mv-nth 2 (hoist-local-fun b rebound tenv locals used)))
                       (set::insert (fresh-expr-var (bind-fun->var b) (string-sfix used)) nil))
                (equal (bind-bound-type-vars (mv-nth 2 (hoist-local-fun b rebound tenv locals used))) nil)
                (equal (bind-bound-ispace-vars (mv-nth 2 (hoist-local-fun b rebound tenv locals used))) nil)
                (equal (expr-free-type-vars (mv-nth 3 (hoist-local-fun b rebound tenv locals used))) nil)
                (equal (expr-free-ispace-vars (mv-nth 3 (hoist-local-fun b rebound tenv locals used))) nil)
                (set::subset (expr-free-expr-vars (mv-nth 3 (hoist-local-fun b rebound tenv locals used)))
                             (set::insert (fresh-expr-var (bind-fun->var b) (string-sfix used))
                                          (bind-free-expr-vars b)))
                (equal (mv-nth 4 (hoist-local-fun b rebound tenv locals used))
                       (set::insert (fresh-expr-var (bind-fun->var b) (string-sfix used))
                                    (string-sfix used)))))
  :enable (hoist-local-fun bind-bound-expr-vars bind-bound-type-vars bind-bound-ispace-vars
           set::pick-a-point-subset-strategy)
  :expand ((bind-free-type-vars b)
           (bind-free-ispace-vars b)
           (bind-free-expr-vars b)
           (:free (n) (expr-free-type-vars (expr-var n)))
           (:free (n) (expr-free-ispace-vars (expr-var n)))
           (:free (n) (expr-free-expr-vars (expr-var n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The pieces of a hoisted function binding are closed in type and ispace
; variables, in the form in which the flag proof meets them.

(defrule hoist-local-fun-when-hoisted-pieces
  (implies (mv-nth 0 (hoist-local-fun b rebound tenv locals used))
           (and (equal (var+type?-list-free-type-vars (bind-fun->params b)) nil)
                (equal (type-option-free-type-vars (bind-fun->type? b)) nil)
                (equal (expr-free-type-vars (bind-fun->expr b)) nil)
                (equal (var+type?-list-free-ispace-vars (bind-fun->params b)) nil)
                (equal (type-option-free-ispace-vars (bind-fun->type? b)) nil)
                (equal (expr-free-ispace-vars (bind-fun->expr b)) nil)))
  :use hoist-local-fun-when-hoisted
  :enable set::emptyp
  :expand ((bind-free-type-vars b)
           (bind-free-ispace-vars b)))

; The same, keyed on a function binding built from its pieces, which is how
; the traversal presents the binding it hoists.

(defrule hoist-local-fun-when-hoisted-fun-pieces
  (implies (mv-nth 0 (hoist-local-fun (bind-fun v ps ty e) rebound tenv locals used))
           (and (equal (var+type?-list-free-type-vars ps) nil)
                (equal (type-option-free-type-vars ty) nil)
                (equal (expr-free-type-vars e) nil)
                (equal (var+type?-list-free-ispace-vars ps) nil)
                (equal (type-option-free-ispace-vars ty) nil)
                (equal (expr-free-ispace-vars e) nil)))
  :use ((:instance hoist-local-fun-when-hoisted-pieces (b (bind-fun v ps ty e)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The map from hoisted local functions to the expressions that replace their
; uses: its values have no free type or ispace variables (they are variables
; applied to variables), and that is preserved as the map grows.

(acl2::defun-sk lmap-closed-p (lmap)
  (forall (name)
    (implies (omap::assoc name (string-expr-map-fix lmap))
             (and (equal (expr-free-type-vars
                          (cdr (omap::assoc name (string-expr-map-fix lmap))))
                         nil)
                  (equal (expr-free-ispace-vars
                          (cdr (omap::assoc name (string-expr-map-fix lmap))))
                         nil)))))

(in-theory (disable lmap-closed-p))

(defrule lmap-closed-p-of-nil
  (lmap-closed-p nil)
  :enable lmap-closed-p)

(defrule free-vars-of-assoc-when-lmap-closed-p
  (implies (and (lmap-closed-p lmap)
                (omap::assoc name (string-expr-map-fix lmap)))
           (and (equal (expr-free-type-vars
                        (cdr (omap::assoc name (string-expr-map-fix lmap))))
                       nil)
                (equal (expr-free-ispace-vars
                        (cdr (omap::assoc name (string-expr-map-fix lmap))))
                       nil)))
  :use lmap-closed-p-necc)

(defrule lmap-closed-p-of-string-expr-map-fix
  (implies (lmap-closed-p lmap)
           (lmap-closed-p (string-expr-map-fix lmap)))
  :expand ((lmap-closed-p (string-expr-map-fix lmap)))
  :use ((:instance lmap-closed-p-necc
                   (name (lmap-closed-p-witness (string-expr-map-fix lmap))))))

(defrule lmap-closed-p-of-update
  (implies (and (lmap-closed-p lmap)
                (stringp name)
                (exprp e)
                (equal (expr-free-type-vars e) nil)
                (equal (expr-free-ispace-vars e) nil))
           (lmap-closed-p (omap::update name e (string-expr-map-fix lmap))))
  :expand ((lmap-closed-p (omap::update name e (string-expr-map-fix lmap))))
  :enable omap::assoc-of-update
  :use ((:instance lmap-closed-p-necc
                   (name (lmap-closed-p-witness
                          (omap::update name e (string-expr-map-fix lmap)))))))

(defrule lmap-closed-p-of-string-expr-map-remove-keys
  (implies (lmap-closed-p lmap)
           (lmap-closed-p (string-expr-map-remove-keys keys lmap)))
  :expand ((lmap-closed-p (string-expr-map-remove-keys keys lmap)))
  :use ((:instance lmap-closed-p-necc
                   (name (lmap-closed-p-witness
                          (string-expr-map-remove-keys keys lmap))))))

; The list folds on empty lists.

(defrule expr-list-free-type-vars-when-not-consp
  (implies (not (consp x)) (equal (expr-list-free-type-vars x) nil))
  :expand ((expr-list-free-type-vars x)))
(defrule expr-list-free-ispace-vars-when-not-consp
  (implies (not (consp x)) (equal (expr-list-free-ispace-vars x) nil))
  :expand ((expr-list-free-ispace-vars x)))
(defrule atom-list-free-type-vars-when-not-consp
  (implies (not (consp x)) (equal (atom-list-free-type-vars x) nil))
  :expand ((atom-list-free-type-vars x)))
(defrule atom-list-free-ispace-vars-when-not-consp
  (implies (not (consp x)) (equal (atom-list-free-ispace-vars x) nil))
  :expand ((atom-list-free-ispace-vars x)))
(defrule bind-list-free-type-vars-when-not-consp
  (implies (not (consp x)) (equal (bind-list-free-type-vars x) nil))
  :expand ((bind-list-free-type-vars x)))
(defrule bind-list-free-ispace-vars-when-not-consp
  (implies (not (consp x)) (equal (bind-list-free-ispace-vars x) nil))
  :expand ((bind-list-free-ispace-vars x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lifting preserves the free type variables and the free ispace variables
; of the rebuilt node: a lifted lambda is closed in both, and so is a
; hoisted local function, and the references that replace them are
; variables applied to variables.  The bound variables of a rebuilt binding
; are those of the original (its kind and variable are kept).

(defrule var+type?-list-free-type-vars-of-append
  (equal (var+type?-list-free-type-vars (append a b))
         (set::union (var+type?-list-free-type-vars a)
                     (var+type?-list-free-type-vars b)))
  :induct (len a)
  :expand ((var+type?-list-free-type-vars a)
           (:free (x y) (var+type?-list-free-type-vars (cons x y)))))

(defrule var+type?-list-free-ispace-vars-of-append
  (equal (var+type?-list-free-ispace-vars (append a b))
         (set::union (var+type?-list-free-ispace-vars a)
                     (var+type?-list-free-ispace-vars b)))
  :induct (len a)
  :expand ((var+type?-list-free-ispace-vars a)
           (:free (x y) (var+type?-list-free-ispace-vars (cons x y)))))

;; The parameters, body, and result type a lambda is flattened into are
;; closed when the lambda is.

(defrule free-vars-of-nested-lambda-when-closed
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

(defret-mutual free-type/ispace-vars-of-lambda-lift-exprs/atoms/binds
  (defret free-type/ispace-vars-of-ll-expr
    (implies (lmap-closed-p lmap)
             (and (equal (expr-free-type-vars new-x) (expr-free-type-vars x))
                  (equal (expr-free-ispace-vars new-x) (expr-free-ispace-vars x))))
    :fn ll-expr)
  (defret free-type/ispace-vars-of-ll-lambda
    (implies (and (lmap-closed-p lmap)
                  (set::emptyp (var+type?-list-free-type-vars params))
                  (set::emptyp (var+type?-list-free-ispace-vars params))
                  (set::emptyp (expr-free-type-vars body))
                  (set::emptyp (expr-free-ispace-vars body))
                  (set::emptyp (type-option-free-type-vars type?))
                  (set::emptyp (type-option-free-ispace-vars type?)))
             (and (equal (expr-free-type-vars e) nil)
                  (equal (expr-free-ispace-vars e) nil)))
    :fn ll-lambda)
  (defret free-type/ispace-vars-of-ll-let-binds
    (implies (lmap-closed-p lmap)
             (and (equal (bind-list-free-type-vars kept) (bind-list-free-type-vars binds))
                  (equal (bind-list-free-ispace-vars kept) (bind-list-free-ispace-vars binds))
                  (equal (bind-list-bound-type-vars kept) (bind-list-bound-type-vars binds))
                  (equal (bind-list-bound-ispace-vars kept) (bind-list-bound-ispace-vars binds))
                  (lmap-closed-p new-lmap)))
    :fn ll-let-binds)
  (defret free-type/ispace-vars-of-ll-expr-list
    (implies (lmap-closed-p lmap)
             (and (equal (expr-list-free-type-vars new-x) (expr-list-free-type-vars x))
                  (equal (expr-list-free-ispace-vars new-x) (expr-list-free-ispace-vars x))))
    :fn ll-expr-list)
  (defret free-type/ispace-vars-of-ll-atom
    (implies (lmap-closed-p lmap)
             (and (equal (atom-free-type-vars new-x) (atom-free-type-vars x))
                  (equal (atom-free-ispace-vars new-x) (atom-free-ispace-vars x))))
    :fn ll-atom)
  (defret free-type/ispace-vars-of-ll-atom-list
    (implies (lmap-closed-p lmap)
             (and (equal (atom-list-free-type-vars new-x) (atom-list-free-type-vars x))
                  (equal (atom-list-free-ispace-vars new-x) (atom-list-free-ispace-vars x))))
    :fn ll-atom-list)
  (defret free-type/ispace-vars-of-ll-bind
    (implies (lmap-closed-p lmap)
     (and (equal (bind-kind new-x) (bind-kind x))
         (equal (bind-free-type-vars new-x) (bind-free-type-vars x))
         (equal (bind-free-ispace-vars new-x) (bind-free-ispace-vars x))
         (equal (bind-bound-type-vars new-x) (bind-bound-type-vars x))
         (equal (bind-bound-ispace-vars new-x) (bind-bound-ispace-vars x))
         (equal (bind-bound-expr-vars new-x) (bind-bound-expr-vars x))))
    :fn ll-bind)
  :mutual-recursion lambda-lift-exprs/atoms/binds
  :hints (("Goal" :in-theory (e/d (ll-lambda
                                    make-atom-lambda/lambdan
                                     ll-let-binds
                                     ll-expr-list
                                     ll-atom
                                     ll-atom-list
                                     ll-bind
                                     liftable-lambda-p
                                     bind-bound-type-vars
                                     bind-bound-ispace-vars
                                     bind-bound-expr-vars
                                     bind-list-bound-type-vars
                                     bind-list-bound-ispace-vars
                                     hoist-local-fun-when-hoisted-pieces
                                     hoist-local-fun-when-hoisted-fun-pieces
                                     difference-of-nil-right
                                     consp-when-positive-len
                                     positive-len-when-consp
                                     set::emptyp)
                                    (emit-lifted-lambda hoist-local-fun apply-to-names
                                     binary-append
                                     acl2::utf8-table36-length-lemmas
                                     acl2::consp-when-member-equal-of-cons-listp
                                     assoc-of-string-expr-map-remove-keys
                                     default-+-2
                                     default-cdr
                                     member-equal
                                     acl2::emptyp-string-sfix
                                     acl2::member-when-atom
                                     consp-of-var+type?-list->var
                                     set::insert-when-emptyp))
           :expand ((ll-expr x tenv tlets locals lmap used)
                    (atom-free-type-vars (expr-atom->atom x))
                    (atom-free-ispace-vars (expr-atom->atom x))
                    (:free (y z) (var+type?-list-free-type-vars (cons y z)))
                    (:free (y z) (var+type?-list-free-ispace-vars (cons y z)))
                    (var+type?-list-free-type-vars nil)
                    (var+type?-list-free-ispace-vars nil)
                    (bind-free-type-vars (car binds))
                    (bind-free-ispace-vars (car binds))
                    (ll-bind (bind-fix (car binds)) tenv tlets locals lmap used)
                    (ll-expr (car x) tenv tlets locals lmap used)
                    (ll-atom (car x) tenv tlets locals lmap used)
                    (:free (n) (expr-free-type-vars (expr-var n)))
                    (:free (a) (expr-free-type-vars (expr-atom a)))
                    (:free (ds as) (expr-free-type-vars (expr-array ds as)))
                    (:free (ds es) (expr-free-type-vars (expr-frame ds es)))
                    (:free (f a) (expr-free-type-vars (expr-app f a)))
                    (:free (f as) (expr-free-type-vars (expr-appn f as)))
                    (:free (f as) (expr-free-type-vars (expr-tapp f as)))
                    (:free (f as) (expr-free-type-vars (expr-tappn f as)))
                    (:free (f as) (expr-free-type-vars (expr-iapp f as)))
                    (:free (f as) (expr-free-type-vars (expr-iappn f as)))
                    (:free (f tg ig as) (expr-free-type-vars (expr-capp f tg ig as)))
                    (:free (i v tg b ty) (expr-free-type-vars (expr-unbox i v tg b ty)))
                    (:free (is v tg b ty) (expr-free-type-vars (expr-unboxn is v tg b ty)))
                    (:free (es) (expr-free-type-vars (expr-bracket es)))
                    (:free (bs b) (expr-free-type-vars (expr-let bs b)))
                    (:free (p b ty) (atom-free-type-vars (atom-lambda p b ty)))
                    (:free (ps b ty) (atom-free-type-vars (atom-lambdan ps b ty)))
                    (:free (p b) (atom-free-type-vars (atom-tlambda p b)))
                    (:free (ps b) (atom-free-type-vars (atom-tlambdan ps b)))
                    (:free (p b) (atom-free-type-vars (atom-ilambda p b)))
                    (:free (ps b) (atom-free-type-vars (atom-ilambdan ps b)))
                    (:free (i a ty) (atom-free-type-vars (atom-box i a ty)))
                    (:free (is a ty) (atom-free-type-vars (atom-boxn is a ty)))
                    (:free (v ty e) (bind-free-type-vars (bind-val v ty e)))
                    (:free (v ps ty e) (bind-free-type-vars (bind-fun v ps ty e)))
                    (:free (v ps ty e) (bind-free-type-vars (bind-tfun v ps ty e)))
                    (:free (v ps ty e) (bind-free-type-vars (bind-ifun v ps ty e)))
                    (:free (v tp ip ps ty e) (bind-free-type-vars (bind-cfun v tp ip ps ty e)))
                    (:free (a l) (expr-list-free-type-vars (cons a l)))
                    (:free (a l) (atom-list-free-type-vars (cons a l)))
                    (:free (a l) (bind-list-free-type-vars (cons a l)))
                    (expr-free-type-vars x)
                    (atom-free-type-vars x)
                    (bind-free-type-vars x)
                    (expr-list-free-type-vars x)
                    (atom-list-free-type-vars x)
                    (bind-list-free-type-vars x)
                    (bind-list-free-type-vars binds)
                    (:free (n) (expr-free-ispace-vars (expr-var n)))
                    (:free (a) (expr-free-ispace-vars (expr-atom a)))
                    (:free (ds as) (expr-free-ispace-vars (expr-array ds as)))
                    (:free (ds es) (expr-free-ispace-vars (expr-frame ds es)))
                    (:free (f a) (expr-free-ispace-vars (expr-app f a)))
                    (:free (f as) (expr-free-ispace-vars (expr-appn f as)))
                    (:free (f as) (expr-free-ispace-vars (expr-tapp f as)))
                    (:free (f as) (expr-free-ispace-vars (expr-tappn f as)))
                    (:free (f as) (expr-free-ispace-vars (expr-iapp f as)))
                    (:free (f as) (expr-free-ispace-vars (expr-iappn f as)))
                    (:free (f tg ig as) (expr-free-ispace-vars (expr-capp f tg ig as)))
                    (:free (i v tg b ty) (expr-free-ispace-vars (expr-unbox i v tg b ty)))
                    (:free (is v tg b ty) (expr-free-ispace-vars (expr-unboxn is v tg b ty)))
                    (:free (es) (expr-free-ispace-vars (expr-bracket es)))
                    (:free (bs b) (expr-free-ispace-vars (expr-let bs b)))
                    (:free (p b ty) (atom-free-ispace-vars (atom-lambda p b ty)))
                    (:free (ps b ty) (atom-free-ispace-vars (atom-lambdan ps b ty)))
                    (:free (p b) (atom-free-ispace-vars (atom-tlambda p b)))
                    (:free (ps b) (atom-free-ispace-vars (atom-tlambdan ps b)))
                    (:free (p b) (atom-free-ispace-vars (atom-ilambda p b)))
                    (:free (ps b) (atom-free-ispace-vars (atom-ilambdan ps b)))
                    (:free (i a ty) (atom-free-ispace-vars (atom-box i a ty)))
                    (:free (is a ty) (atom-free-ispace-vars (atom-boxn is a ty)))
                    (:free (v ty e) (bind-free-ispace-vars (bind-val v ty e)))
                    (:free (v ps ty e) (bind-free-ispace-vars (bind-fun v ps ty e)))
                    (:free (v ps ty e) (bind-free-ispace-vars (bind-tfun v ps ty e)))
                    (:free (v ps ty e) (bind-free-ispace-vars (bind-ifun v ps ty e)))
                    (:free (v tp ip ps ty e) (bind-free-ispace-vars (bind-cfun v tp ip ps ty e)))
                    (:free (a l) (expr-list-free-ispace-vars (cons a l)))
                    (:free (a l) (atom-list-free-ispace-vars (cons a l)))
                    (:free (a l) (bind-list-free-ispace-vars (cons a l)))
                    (expr-free-ispace-vars x)
                    (atom-free-ispace-vars x)
                    (bind-free-ispace-vars x)
                    (expr-list-free-ispace-vars x)
                    (atom-list-free-ispace-vars x)
                    (bind-list-free-ispace-vars x)
                    (bind-list-free-ispace-vars binds)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The names in use grow along the traversal, and the definitions lifted out
; of a node are named freshly: their names are among the names in use
; afterwards and were not in use before.

(defruledl emptyp-intersect-of-union-left
  (implies (and (set::emptyp (set::intersect a c))
                (set::emptyp (set::intersect b c)))
           (set::emptyp (set::intersect (set::union a b) c)))
  :use ((:instance set::in-head (x (set::intersect (set::union a b) c)))
        (:instance set::never-in-empty (set::a (set::head (set::intersect (set::union a b) c)))
                   (set::x (set::intersect a c)))
        (:instance set::never-in-empty (set::a (set::head (set::intersect (set::union a b) c)))
                   (set::x (set::intersect b c)))))

(defruledl emptyp-intersect-when-subset-right
  (implies (and (set::emptyp (set::intersect a c1))
                (set::subset c c1))
           (set::emptyp (set::intersect a c)))
  :use ((:instance set::in-head (x (set::intersect a c)))
        (:instance set::never-in-empty (set::a (set::head (set::intersect a c)))
                   (set::x (set::intersect a c1)))
        (:instance set::subset-in (set::a (set::head (set::intersect a c)))
                   (set::x c) (set::y c1))))

(defruledl emptyp-intersect-of-insert-left
  (implies (and (not (set::in x c))
                (set::emptyp (set::intersect a c)))
           (set::emptyp (set::intersect (set::insert x a) c)))
  :use ((:instance set::in-head (x (set::intersect (set::insert x a) c)))
        (:instance set::never-in-empty (set::a (set::head (set::intersect (set::insert x a) c)))
                   (set::x (set::intersect a c)))))

(defrule hoist-local-fun-when-not-fun
  (implies (not (equal (bind-kind b) :fun))
           (equal (mv-nth 0 (hoist-local-fun b rebound tenv locals used)) nil))
  :enable hoist-local-fun)

(defrule bind-list-bound-type-vars-of-emit-lifted-lambda
  (equal (bind-list-bound-type-vars (mv-nth 1 (emit-lifted-lambda params body type? tenv locals used)))
         nil)
  :enable (emit-lifted-lambda bind-list-bound-type-vars bind-bound-type-vars))

(defrule bind-list-bound-ispace-vars-of-emit-lifted-lambda
  (equal (bind-list-bound-ispace-vars (mv-nth 1 (emit-lifted-lambda params body type? tenv locals used)))
         nil)
  :enable (emit-lifted-lambda bind-list-bound-ispace-vars bind-bound-ispace-vars))

(defruledl emptyp-of-intersect-of-union
  (equal (set::emptyp (set::intersect (set::union a b) c))
         (and (set::emptyp (set::intersect a c))
              (set::emptyp (set::intersect b c))))
  :use (emptyp-intersect-of-union-left
        (:instance set::in-head (x (set::intersect a c)))
        (:instance set::in-head (x (set::intersect b c)))
        (:instance set::never-in-empty (set::a (set::head (set::intersect a c)))
                   (set::x (set::intersect (set::union a b) c)))
        (:instance set::never-in-empty (set::a (set::head (set::intersect b c)))
                   (set::x (set::intersect (set::union a b) c)))))

(defrule not-in-of-fresh-expr-var-when-subset
  (implies (set::subset s (string-sfix used))
           (not (set::in (fresh-expr-var prefix used) s)))
  :use ((:instance set::subset-in (set::a (fresh-expr-var prefix used))
                   (set::x s) (set::y (string-sfix used)))))

(defrulel emptyp-intersect-of-nil-left
  (set::emptyp (set::intersect nil c)))

(defrulel emptyp-intersect-of-singleton-when-not-in
  (implies (not (set::in a s))
           (set::emptyp (set::intersect (set::insert a nil) s)))
  :use ((:instance set::in-head
                   (set::x (set::intersect (set::insert a nil) s)))))

; Whether or not the lambda is lifted, the names in use only grow, and the
; definitions emitted, if any, bind fresh names among them.

(defrule used-of-emit-lifted-lambda
  (b* (((mv & lifted new-used)
        (emit-lifted-lambda params body type? tenv locals used)))
    (and (implies (set::subset x (string-sfix used))
                  (and (set::subset x new-used)
                       (set::emptyp
                        (set::intersect (bind-list-bound-expr-vars lifted) x))))
         (set::subset (bind-list-bound-expr-vars lifted) new-used)))
  :cases ((consp (mv-nth 1 (emit-lifted-lambda params body type?
                                               tenv locals used))))
  :enable (set::subset-insert set::subset-transitive)
  :use ((:instance not-in-of-fresh-expr-var-when-subset
                   (prefix "lam_") (s x))))

(defret-mutual used-of-lambda-lift-exprs/atoms/binds
  (defret used-of-ll-expr
    (and (set::subset (string-sfix used) new-used)
         (set::subset (bind-list-bound-expr-vars lifted) new-used)
         (set::emptyp (set::intersect (bind-list-bound-expr-vars lifted) (string-sfix used)))
         (set::emptyp (bind-list-bound-type-vars lifted))
         (set::emptyp (bind-list-bound-ispace-vars lifted)))
    :fn ll-expr)
  (defret used-of-ll-lambda
    (and (set::subset (string-sfix used) new-used)
         (set::subset (bind-list-bound-expr-vars lifted) new-used)
         (set::emptyp (set::intersect (bind-list-bound-expr-vars lifted) (string-sfix used)))
         (set::emptyp (bind-list-bound-type-vars lifted))
         (set::emptyp (bind-list-bound-ispace-vars lifted)))
    :fn ll-lambda)
  (defret used-of-ll-let-binds
    (and (set::subset (string-sfix used) new-used)
         (set::subset (bind-list-bound-expr-vars lifted) new-used)
         (set::emptyp (set::intersect (bind-list-bound-expr-vars lifted) (string-sfix used)))
         (set::emptyp (bind-list-bound-type-vars lifted))
         (set::emptyp (bind-list-bound-ispace-vars lifted)))
    :fn ll-let-binds)
  (defret used-of-ll-expr-list
    (and (set::subset (string-sfix used) new-used)
         (set::subset (bind-list-bound-expr-vars lifted) new-used)
         (set::emptyp (set::intersect (bind-list-bound-expr-vars lifted) (string-sfix used)))
         (set::emptyp (bind-list-bound-type-vars lifted))
         (set::emptyp (bind-list-bound-ispace-vars lifted)))
    :fn ll-expr-list)
  (defret used-of-ll-atom
    (and (set::subset (string-sfix used) new-used)
         (set::subset (bind-list-bound-expr-vars lifted) new-used)
         (set::emptyp (set::intersect (bind-list-bound-expr-vars lifted) (string-sfix used)))
         (set::emptyp (bind-list-bound-type-vars lifted))
         (set::emptyp (bind-list-bound-ispace-vars lifted)))
    :fn ll-atom)
  (defret used-of-ll-atom-list
    (and (set::subset (string-sfix used) new-used)
         (set::subset (bind-list-bound-expr-vars lifted) new-used)
         (set::emptyp (set::intersect (bind-list-bound-expr-vars lifted) (string-sfix used)))
         (set::emptyp (bind-list-bound-type-vars lifted))
         (set::emptyp (bind-list-bound-ispace-vars lifted)))
    :fn ll-atom-list)
  (defret used-of-ll-bind
    (and (set::subset (string-sfix used) new-used)
         (set::subset (bind-list-bound-expr-vars lifted) new-used)
         (set::emptyp (set::intersect (bind-list-bound-expr-vars lifted) (string-sfix used)))
         (set::emptyp (bind-list-bound-type-vars lifted))
         (set::emptyp (bind-list-bound-ispace-vars lifted)))
    :fn ll-bind)
  :mutual-recursion lambda-lift-exprs/atoms/binds
  :hints (("Goal" :in-theory (e/d (bind-list-bound-expr-vars
                                   emptyp-intersect-of-union-left
                                   emptyp-of-intersect-of-union
                                   subset-of-insert-right
                                   emptyp-intersect-when-subset-right
                                   emptyp-intersect-of-insert-left
                                   set::subset-transitive
                                   set::subset-insert-x
                                   subset-of-union
                                   subset-of-union-right-1
                                   subset-of-union-right-2
                                   bind-list-bound-type-vars
                                   bind-list-bound-ispace-vars)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Top-level corollaries.

(defrule expr-free-type-vars-of-lambda-lift-top-expr
  (equal (expr-free-type-vars (lambda-lift-top-expr x))
         (set::union (bind-list-free-type-vars
                      (mv-nth 1 (ll-expr x nil nil nil nil (expr-all-expr-vars x))))
                     (expr-free-type-vars x)))
  :enable lambda-lift-top-expr)

(defrule expr-free-ispace-vars-of-lambda-lift-top-expr
  (equal (expr-free-ispace-vars (lambda-lift-top-expr x))
         (set::union (bind-list-free-ispace-vars
                      (mv-nth 1 (ll-expr x nil nil nil nil (expr-all-expr-vars x))))
                     (expr-free-ispace-vars x)))
  :enable lambda-lift-top-expr)

(defrule subset-of-expr-free-type-vars-of-lambda-lift-top-expr
  (set::subset (expr-free-type-vars x)
               (expr-free-type-vars (lambda-lift-top-expr x))))

(defrule subset-of-expr-free-ispace-vars-of-lambda-lift-top-expr
  (set::subset (expr-free-ispace-vars x)
               (expr-free-ispace-vars (lambda-lift-top-expr x))))

(defrule lifted-names-fresh-of-lambda-lift-top-expr
  (set::emptyp (set::intersect (bind-list-bound-expr-vars
                                (mv-nth 1 (ll-expr x nil nil nil nil (expr-all-expr-vars x))))
                               (expr-all-expr-vars x)))
  :use ((:instance used-of-ll-expr
                   (tenv nil) (tlets nil) (locals nil) (lmap nil) (used (expr-all-expr-vars x)))))
