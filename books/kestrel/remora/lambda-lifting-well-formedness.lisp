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
(include-book "abstract-syntax-well-formedness")
(include-book "well-formedness-support")

(include-book "std/util/define-sk" :dir :system)

(include-book "portcullis")

(local (include-book "std/osets/top" :dir :system))

(local (in-theory (disable (:e tau-system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lambda-lifting-well-formedness
  :parents (lambda-lifting)
  :short "Well-formedness of lambda lifting."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lambda lifting preserves @(tsee expr-wfp) and @(tsee file-wfp).")
   (xdoc::p
    "Most of the traversal rebuilds each node from the results for its
     components, so those cases follow from the induction hypotheses and the
     length theorems that the traversal is defined with.  What has to be
     shown beyond that is that a lifted definition is well formed, and that
     is where the two constraints of @(tsee ast-wfp) meet: the definition's
     name must be a legal identifier, and so must the names of the
     parameters it abstracts over.")
   (xdoc::p
    "The name comes from @(tsee fresh-expr-var), which yields a legal
     identifier when its prefix is one.  The parameters are the lambda's free
     expression variables, so what is needed is that the free variables of a
     well-formed AST are themselves legal identifiers.  That is the first
     section below: @(tsee valid-identifier-string-set-p), a quantified
     predicate in the style of @(tsee renaming-wfp), and its preservation by
     the set operations the free-variable fold performs."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Sets of legal identifiers.

(define-sk valid-identifier-string-set-p ((vars string-setp))
  :returns (yes/no booleanp)
  :short "Check that every name in a set is a legal Remora identifier."
  (forall (var)
          (implies (set::in var (string-sfix vars))
                   (valid-identifier-string-p var))))

(defsection valid-identifier-string-set-p-lemmas
  :short "The set operations the free-variable fold performs
          preserve being a set of legal identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are stated on unfixed arguments, with @(tsee string-setp)
     hypotheses, because that is the form the goals arise in: the sets are
     results of the fold, which returns a @(tsee string-setp)."))

  (local (in-theory (enable acl2::string-sfix-when-string-setp)))

  (defrule valid-identifier-string-p-when-in-valid-identifier-string-set-p
    (implies (and (valid-identifier-string-set-p vars)
                  (string-setp vars)
                  (set::in var vars))
             (valid-identifier-string-p var))
    :use valid-identifier-string-set-p-necc)

  (defrule valid-identifier-string-set-p-of-nil
    (valid-identifier-string-set-p nil)
    :expand ((valid-identifier-string-set-p nil)))

  (defrule valid-identifier-string-set-p-of-insert
    (implies (and (valid-identifier-string-set-p vars)
                  (string-setp vars)
                  (stringp var)
                  (valid-identifier-string-p var))
             (valid-identifier-string-set-p (set::insert var vars)))
    :expand ((valid-identifier-string-set-p (set::insert var vars)))
    :use ((:instance valid-identifier-string-set-p-necc
                     (var (valid-identifier-string-set-p-witness
                           (set::insert var vars))))))

  (defrule valid-identifier-string-set-p-of-union
    (implies (and (valid-identifier-string-set-p vars1)
                  (valid-identifier-string-set-p vars2)
                  (string-setp vars1)
                  (string-setp vars2))
             (valid-identifier-string-set-p (set::union vars1 vars2)))
    :expand ((valid-identifier-string-set-p (set::union vars1 vars2)))
    :use ((:instance valid-identifier-string-set-p-necc
                     (vars vars1)
                     (var (valid-identifier-string-set-p-witness
                           (set::union vars1 vars2))))
          (:instance valid-identifier-string-set-p-necc
                     (vars vars2)
                     (var (valid-identifier-string-set-p-witness
                           (set::union vars1 vars2))))))

  (defrule valid-identifier-string-set-p-of-delete
    (implies (and (valid-identifier-string-set-p vars)
                  (string-setp vars))
             (valid-identifier-string-set-p (set::delete var vars)))
    :expand ((valid-identifier-string-set-p (set::delete var vars)))
    :use ((:instance valid-identifier-string-set-p-necc
                     (var (valid-identifier-string-set-p-witness
                           (set::delete var vars))))))

      (defrule valid-identifier-string-set-p-of-difference
    (implies (and (valid-identifier-string-set-p vars1)
                  (string-setp vars1))
             (valid-identifier-string-set-p (set::difference vars1 vars2)))
    :expand ((valid-identifier-string-set-p (set::difference vars1 vars2)))
    :use ((:instance valid-identifier-string-set-p-necc
                     (vars vars1)
                     (var (valid-identifier-string-set-p-witness
                           (set::difference vars1 vars2)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The free expression variables of a well-formed AST are legal identifiers.
; They enter the set only at a :VAR expression, whose name AST-WFP
; constrains; every other case builds from the sub-results by the operations
; above, all of which preserve the property.

(defret-mutual valid-identifier-string-set-p-of-free-expr-vars
  (defret valid-identifier-string-set-p-of-expr-free-expr-vars
    (implies (expr-wfp expr) (valid-identifier-string-set-p result))
    :fn expr-free-expr-vars)
  (defret valid-identifier-string-set-p-of-expr-list-free-expr-vars
    (implies (expr-list-wfp expr-list) (valid-identifier-string-set-p result))
    :fn expr-list-free-expr-vars)
  (defret valid-identifier-string-set-p-of-atom-free-expr-vars
    (implies (atom-wfp atom) (valid-identifier-string-set-p result))
    :fn atom-free-expr-vars)
  (defret valid-identifier-string-set-p-of-atom-list-free-expr-vars
    (implies (atom-list-wfp atom-list) (valid-identifier-string-set-p result))
    :fn atom-list-free-expr-vars)
  (defret valid-identifier-string-set-p-of-bind-free-expr-vars
    (implies (bind-wfp bind) (valid-identifier-string-set-p result))
    :fn bind-free-expr-vars)
  (defret valid-identifier-string-set-p-of-bind-list-free-expr-vars
    (implies (bind-list-wfp bind-list) (valid-identifier-string-set-p result))
    :fn bind-list-free-expr-vars)
  :skip-others t
  :mutual-recursion exprs/atoms/binds-free-expr-vars
  :hints (("Goal" :in-theory (enable expr-free-expr-vars
                                     expr-list-free-expr-vars
                                     atom-free-expr-vars
                                     atom-list-free-expr-vars
                                     bind-free-expr-vars
                                     bind-list-free-expr-vars
                                     expr-wfp expr-list-wfp
                                     atom-wfp atom-list-wfp
                                     bind-wfp bind-list-wfp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The free variables are consumed as a list, so the set property is
; transferred to the list form the constructors take.

(define valid-identifier-string-list-p ((names string-listp))
  :returns (yes/no booleanp)
  :short "Check that every name in a list is a legal Remora identifier."
  (or (endp names)
      (and (valid-identifier-string-p (car names))
           (valid-identifier-string-list-p (cdr names)))))

; An oset is a list, and on a non-empty one HEAD and TAIL are CAR and CDR;
; these connect the set reasoning above to the list recursion below.

(defsection oset-as-list
  :short "Osets, viewed as the lists they are."

  (defruled head-is-car-when-setp
    (implies (set::setp x)
             (equal (set::head x) (car x)))
    :enable (set::head set::sfix))

  (defruled tail-is-cdr-when-setp
    (implies (set::setp x)
             (equal (set::tail x) (cdr x)))
    :enable (set::tail set::sfix))

  (defruled string-setp-of-cdr-when-string-setp
    (implies (string-setp x)
             (string-setp (cdr x)))
    :enable (string-setp tail-is-cdr-when-setp)
    :use ((:instance set::tail-produces-set (set::x x))))

    (defruled in-cdr-implies-in-when-setp
    (implies (and (set::setp x)
                  (set::in a (cdr x)))
             (set::in a x))
    :use ((:instance set::in-tail (set::a a) (set::x x)))
    :enable tail-is-cdr-when-setp)

  (defruled in-car-when-string-setp
    (implies (and (string-setp x)
                  (consp x))
             (set::in (car x) x))
    :use ((:instance set::in-head (set::x x)))
    :enable (head-is-car-when-setp set::emptyp)))

(defruled valid-identifier-string-list-p-when-valid-identifier-string-set-p
  :short "A set of legal identifiers is a list of them."
  (implies (and (string-setp vars)
                (valid-identifier-string-set-p vars))
           (valid-identifier-string-list-p vars))
  :induct (valid-identifier-string-list-p vars)
  :enable (valid-identifier-string-list-p
           acl2::string-listp-when-string-setp
           string-setp-of-cdr-when-string-setp
           in-car-when-string-setp
           in-cdr-implies-in-when-setp)
  :hints (("Subgoal *1/2"
           :use ((:instance valid-identifier-string-set-p-necc
                            (var (car vars)))
                 (:instance valid-identifier-string-set-p-necc
                            (var (valid-identifier-string-set-p-witness
                                  (cdr vars)))))
           :expand ((valid-identifier-string-set-p (cdr vars))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The pieces a lifted definition is built from.

; The constructors fix their string arguments, and being a legal identifier
; is insensitive to that fixing.

(defruled valid-identifier-string-p-of-str-fix
  (equal (valid-identifier-string-p (str-fix x))
         (valid-identifier-string-p x))
  :enable valid-identifier-string-p)

(defrule type-option-wfp-of-name-to-type-option
  (implies (type-map-wfp tenv)
           (type-option-wfp (name-to-type-option name tenv)))
  :enable (name-to-type-option type-option-wfp)
  :use ((:instance type-wfp-of-cdr-of-assoc-when-type-map-wfp
                   (tmap tenv)
                   (key (str-fix name)))))

(defrule var+type?-list-wfp-of-names-to-params
  (implies (and (valid-identifier-string-list-p names)
                (type-map-wfp tenv))
           (var+type?-list-wfp (names-to-params names tenv)))
  :induct (names-to-params names tenv)
  :enable (names-to-params
           valid-identifier-string-list-p
           valid-identifier-string-p-of-str-fix
           var+type?-list-wfp
           var+type?-wfp
           type-option-wfp))

(defrule expr-list-wfp-of-names-to-exprs
  (implies (valid-identifier-string-list-p names)
           (expr-list-wfp (names-to-exprs names)))
  :induct (names-to-exprs names)
  :enable (names-to-exprs
           valid-identifier-string-list-p
           valid-identifier-string-p-of-str-fix
           expr-list-wfp)
  :expand ((:free (n) (expr-wfp (expr-var n)))))

(defrule expr-wfp-of-apply-to-names
  (implies (and (expr-wfp fun)
                (valid-identifier-string-list-p names))
           (expr-wfp (apply-to-names fun names)))
  :enable (apply-to-names
           valid-identifier-string-list-p
           valid-identifier-string-p-of-str-fix
           expr-list-wfp-of-names-to-exprs
           len-of-names-to-exprs
           consp-when-positive-len
           positive-len-when-consp)
  :expand ((:free (f a) (expr-wfp (expr-app f a)))
           (:free (f as) (expr-wfp (expr-appn f as)))
           (:free (n) (expr-wfp (expr-var n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The environment starts as the primitive operations, whose types are well
; formed, and each way it is extended preserves that.

(defrule type-map-wfp-of-extend-tenv-with-var
  (implies (and (type-map-wfp tenv)
                (type-option-wfp type?))
           (type-map-wfp (extend-tenv-with-var var type? tenv)))
  :enable (extend-tenv-with-var type-option-wfp))

(defrule type-map-wfp-of-extend-tenv-with-params
  (implies (and (type-map-wfp tenv)
                (var+type?-list-wfp params))
           (type-map-wfp (extend-tenv-with-params params tenv)))
  :induct (extend-tenv-with-params params tenv)
  :enable (extend-tenv-with-params var+type?-list-wfp var+type?-wfp))

; The environment is extended by the checker only through values that pass
; the executable check, or not at all.

(defrule type-map-wfp-of-update*
  (implies (and (type-map-wfp new)
                (type-map-wfp old)
                (string-type-mapp new)
                (string-type-mapp old))
           (type-map-wfp (omap::update* new old)))
  :expand ((type-map-wfp (omap::update* new old)))
  :use ((:instance type-map-wfp-necc
                   (tmap new)
                   (key (type-map-wfp-witness (omap::update* new old))))
        (:instance type-map-wfp-necc
                   (tmap old)
                   (key (type-map-wfp-witness (omap::update* new old))))))

(defrule type-map-wfp-of-extend-tenv-with-binds
  (implies (type-map-wfp tenv)
           (type-map-wfp (extend-tenv-with-binds binds tenv)))
  :enable (extend-tenv-with-binds
           type-map-wfp-when-type-map-all-wfp))

(defrule type-map-wfp-of-primop-types
  :short "The primitive operations' types are well formed."
  (type-map-wfp (primop-types))
  :use ((:instance type-map-wfp-when-type-map-all-wfp (tenv (primop-types))))
  :enable ((:e type-map-all-wfp) (:e primop-types)))

; The environment the entry points start from is empty.

; A lifted definition is well formed: its name comes from FRESH-EXPR-VAR,
; whose prefix is a legal identifier, and its parameters are the lambda's
; free expression variables, which are legal identifiers by the section
; above.

(defrule wfp-of-nested-lambda
  :short "The parameters and body a lambda is flattened into are well formed."
  (b* (((mv nestedp params inner) (nested-lambda body)))
    (implies (and (expr-wfp body)
                  nestedp)
             (and (var+type?-list-wfp params)
                  (expr-wfp inner))))
  :enable (nested-lambda var+type?-list-wfp)
  :expand ((expr-wfp body)
           (atom-wfp (expr-atom->atom body))))

(defrule valid-identifier-string-set-p-of-intersect
  :short "The intersection of a set of legal identifiers with any set
          is a set of legal identifiers."
  (implies (and (valid-identifier-string-set-p vars)
                (string-setp vars))
           (valid-identifier-string-set-p (set::intersect vars locals)))
  :expand ((valid-identifier-string-set-p (set::intersect vars locals)))
  :use ((:instance valid-identifier-string-set-p-necc
                   (vars vars)
                   (var (valid-identifier-string-set-p-witness
                         (set::intersect vars locals))))))

(defrule wfp-of-emit-lifted-lambda
  :short "Lifting a lambda yields a well-formed expression
          and a well-formed definition."
  (implies (and (var+type?-list-wfp params)
                (expr-wfp body)
                (type-map-wfp tenv))
           (b* (((mv e lifted &)
                 (emit-lifted-lambda params body tenv locals used)))
             (and (expr-wfp e)
                  (bind-list-wfp lifted))))
  :enable (emit-lifted-lambda
           bind-list-wfp
           bind-wfp
           type-option-wfp
           var+type?-list-wfp-of-append
           valid-identifier-string-p-of-fresh-expr-var
           valid-identifier-string-set-p-of-expr-free-expr-vars
           valid-identifier-string-set-p-of-difference
           valid-identifier-string-set-p-of-intersect
           valid-identifier-string-list-p-when-valid-identifier-string-set-p
           (:e valid-identifier-string-p))
  :expand ((:free (n) (expr-wfp (expr-var n)))
           (:free (v ps ty e) (bind-wfp (bind-fun v ps ty e)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The map from hoisted local functions to the expressions replacing their
; uses must hold well-formed expressions, since a use becomes one of them.
; Like TYPE-MAP-WFP, this is quantified, and every operation on the map has
; a rule about ASSOC.

(define-sk expr-map-wfp ((emap string-expr-mapp))
  :returns (yes/no booleanp)
  :short "Check that every expression in a map is well formed."
  (forall (key)
          (b* ((emap (string-expr-map-fix emap))
               (pair (omap::assoc key emap)))
            (implies pair
                     (expr-wfp (cdr pair))))))

(defsection expr-map-wfp-lemmas
  :short "The invariant on the replacement map is preserved by
          the operations on it."

  (defrule expr-wfp-of-cdr-of-assoc-when-expr-map-wfp
    (implies (and (expr-map-wfp emap)
                  (string-expr-mapp emap)
                  (omap::assoc key emap))
             (expr-wfp (cdr (omap::assoc key emap))))
    :use expr-map-wfp-necc)

  (defrule expr-map-wfp-of-string-expr-map-fix
    (equal (expr-map-wfp (string-expr-map-fix emap))
           (expr-map-wfp emap))
    :expand ((expr-map-wfp (string-expr-map-fix emap))
             (expr-map-wfp emap))
    :use ((:instance expr-map-wfp-necc
                     (key (expr-map-wfp-witness (string-expr-map-fix emap))))
          (:instance expr-map-wfp-necc
                     (emap (string-expr-map-fix emap))
                     (key (expr-map-wfp-witness emap)))))

  (defrule expr-map-wfp-of-update
    (implies (and (expr-map-wfp emap)
                  (stringp key)
                  (exprp val)
                  (expr-wfp val))
             (expr-map-wfp (omap::update key val (string-expr-map-fix emap))))
    :expand ((expr-map-wfp (omap::update key val (string-expr-map-fix emap))))
    :use ((:instance expr-map-wfp-necc
                     (key (expr-map-wfp-witness
                           (omap::update key val (string-expr-map-fix emap)))))))

  (defrule expr-map-wfp-of-nil
    (expr-map-wfp nil)
    :expand ((expr-map-wfp nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Hoisting a local function is well-formedness-preserving in the same way
; lifting a lambda is: the fresh name is a legal identifier, made from the
; function's own, and the captured variables are.

(defrule wfp-of-hoist-local-fun
  :short "Hoisting a local function yields a well-formed definition
          and a well-formed replacement."
  (implies (and (bind-wfp b)
                (type-map-wfp tenv))
           (b* (((mv hoistedp & hoisted replacement &)
                 (hoist-local-fun b tenv locals used)))
             (and (bind-wfp hoisted)
                  (implies hoistedp (expr-wfp replacement)))))
  :enable (hoist-local-fun
           bind-wfp
           var+type?-list-wfp-of-append
           valid-identifier-string-p-of-fresh-expr-var
           valid-identifier-string-set-p-of-bind-free-expr-vars
           valid-identifier-string-set-p-of-intersect
           valid-identifier-string-list-p-when-valid-identifier-string-set-p)
  :expand ((:free (n) (expr-wfp (expr-var n)))
           (:free (v ps ty e) (bind-wfp (bind-fun v ps ty e)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The traversal preserves well-formedness, of the rebuilt node and of the
; definitions lifted out of it.

(defret-mutual wfp-of-lambda-lift-exprs/atoms/binds
  (defret expr-wfp-of-ll-expr
    (implies (and (expr-wfp x)
                  (type-map-wfp tenv)
                  (expr-map-wfp lmap))
             (and (expr-wfp new-x) (bind-list-wfp lifted)))
    :fn ll-expr)
  (defret wfp-of-ll-lambda
    (implies (and (var+type?-list-wfp params)
                  (expr-wfp body)
                  (type-map-wfp tenv)
                  (expr-map-wfp lmap))
             (and (expr-wfp e) (bind-list-wfp lifted)))
    :fn ll-lambda)
  (defret wfp-of-ll-let-binds
    (implies (and (bind-list-wfp binds)
                  (type-map-wfp tenv)
                  (expr-map-wfp lmap))
             (and (bind-list-wfp kept)
                  (bind-list-wfp lifted)
                  (type-map-wfp new-tenv)
                  (expr-map-wfp new-lmap)))
    :fn ll-let-binds)
  (defret expr-list-wfp-of-ll-expr-list
    (implies (and (expr-list-wfp x)
                  (type-map-wfp tenv)
                  (expr-map-wfp lmap))
             (and (expr-list-wfp new-x) (bind-list-wfp lifted)))
    :fn ll-expr-list)
  (defret atom-wfp-of-ll-atom
    (implies (and (atom-wfp x)
                  (type-map-wfp tenv)
                  (expr-map-wfp lmap))
             (and (atom-wfp new-x) (bind-list-wfp lifted)))
    :fn ll-atom)
  (defret atom-list-wfp-of-ll-atom-list
    (implies (and (atom-list-wfp x)
                  (type-map-wfp tenv)
                  (expr-map-wfp lmap))
             (and (atom-list-wfp new-x) (bind-list-wfp lifted)))
    :fn ll-atom-list)
  (defret bind-wfp-of-ll-bind
    (implies (and (bind-wfp x)
                  (type-map-wfp tenv)
                  (expr-map-wfp lmap))
             (and (bind-wfp new-x) (bind-list-wfp lifted)))
    :fn ll-bind)
  (defret bind-list-wfp-of-ll-bind-list
    (implies (and (bind-list-wfp x)
                  (type-map-wfp tenv)
                  (expr-map-wfp lmap))
             (and (bind-list-wfp new-x) (bind-list-wfp lifted)))
    :fn ll-bind-list)
  :mutual-recursion lambda-lift-exprs/atoms/binds
  :hints (("Goal" :in-theory (enable type-map-wfp-of-extend-tenv-with-var
                                     type-map-wfp-of-extend-tenv-with-params
                                     type-map-wfp-of-extend-tenv-with-binds
                                     ll-expr
                                     ll-lambda
                                     ll-let-binds
                                     liftable-lambda-p
                                     var+type?-list-wfp-of-append
                                     ll-expr-list
                                     ll-atom
                                     ll-atom-list
                                     ll-bind
                                     ll-bind-list
                                     expr-wfp expr-list-wfp
                                     atom-wfp atom-list-wfp
                                     bind-wfp bind-list-wfp
                                     var+type?-wfp var+type?-list-wfp
                                     bind-list-wfp-of-append
                                     consp-when-positive-len
                                     positive-len-when-consp)
           :expand ((:free (n) (expr-wfp (expr-var n)))
                    (:free (a) (expr-wfp (expr-atom a)))
                    (:free (ds as) (expr-wfp (expr-array ds as)))
                    (:free (ds es) (expr-wfp (expr-frame ds es)))
                    (:free (f a) (expr-wfp (expr-app f a)))
                    (:free (f as) (expr-wfp (expr-appn f as)))
                    (:free (f as) (expr-wfp (expr-tapp f as)))
                    (:free (f as) (expr-wfp (expr-tappn f as)))
                    (:free (f as) (expr-wfp (expr-iapp f as)))
                    (:free (f as) (expr-wfp (expr-iappn f as)))
                    (:free (f tg ig as) (expr-wfp (expr-capp f tg ig as)))
                    (:free (i v tg b ty) (expr-wfp (expr-unbox i v tg b ty)))
                    (:free (is v tg b ty) (expr-wfp (expr-unboxn is v tg b ty)))
                    (:free (es) (expr-wfp (expr-bracket es)))
                    (:free (bs b) (expr-wfp (expr-let bs b)))
                    (:free (p b ty) (atom-wfp (atom-lambda p b ty)))
                    (:free (ps b ty) (atom-wfp (atom-lambdan ps b ty)))
                    (:free (p b) (atom-wfp (atom-tlambda p b)))
                    (:free (ps b) (atom-wfp (atom-tlambdan ps b)))
                    (:free (p b) (atom-wfp (atom-ilambda p b)))
                    (:free (ps b) (atom-wfp (atom-ilambdan ps b)))
                    (:free (i a ty) (atom-wfp (atom-box i a ty)))
                    (:free (is a ty) (atom-wfp (atom-boxn is a ty)))
                    (:free (v ty e) (bind-wfp (bind-val v ty e)))
                    (:free (v ps ty e) (bind-wfp (bind-fun v ps ty e)))
                    (:free (v ps ty e) (bind-wfp (bind-tfun v ps ty e)))
                    (:free (v ps ty e) (bind-wfp (bind-ifun v ps ty e)))
                    (:free (v tp ip ps ty e)
                           (bind-wfp (bind-cfun v tp ip ps ty e)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule expr-wfp-of-lambda-lift-top-expr
  :short "Lambda-lifting a well-formed expression
          yields a well-formed expression."
  (implies (expr-wfp expr)
           (expr-wfp (lambda-lift-top-expr expr)))
  :enable lambda-lift-top-expr)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The file entry point converts between declarations and bindings, in both
; directions.  A definition is a binding already, and an entry point has the
; same components as a function binding, so both directions preserve
; well-formedness componentwise.

(defrule bind-wfp-of-decl-to-bind
  (implies (decl-wfp decl)
           (bind-wfp (decl-to-bind decl)))
  :enable (decl-to-bind decl-wfp)
  :expand ((:free (v ps ty e) (bind-wfp (bind-fun v ps ty e)))))

(defrule bind-list-wfp-of-decl-list-to-binds
  (implies (decl-list-wfp decls)
           (bind-list-wfp (decl-list-to-binds decls)))
  :induct (decl-list-to-binds decls)
  :enable (decl-list-to-binds decl-list-wfp bind-list-wfp))

(defrule decl-wfp-of-bind-to-decl
  (implies (bind-wfp bind)
           (decl-wfp (bind-to-decl bind entry-names)))
  :enable (bind-to-decl bind-wfp)
  :expand ((:free (v ps ty e) (decl-wfp (decl-entry v ps ty e)))
           (:free (b) (decl-wfp (decl-def b)))))

(defrule decl-list-wfp-of-bind-list-to-decls
  (implies (bind-list-wfp binds)
           (decl-list-wfp (bind-list-to-decls binds entry-names)))
  :induct (bind-list-to-decls binds entry-names)
  :enable (bind-list-to-decls bind-list-wfp decl-list-wfp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule file-wfp-of-lambda-lift-file
  :short "Lambda-lifting a well-formed file yields a well-formed file."
  (implies (file-wfp f)
           (file-wfp (lambda-lift-file f)))
  :enable (lambda-lift-file
           bind-list-wfp-of-append)
  :expand ((file-wfp f)
           (:free (i d) (file-wfp (file i d)))))
