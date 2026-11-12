; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "lambda-lifting-typing")
(include-book "lambda-lifting-free-variables")

(include-book "portcullis")

(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "omaps"))

(local (in-theory (disable (:e tau-system))))

(local (in-theory (disable expr-value-groundp
                           expr-value-list-groundp
                           primop-value-groundp
                           string-expr-value-map-groundp
                           expr-denv-groundp
                           type-value-groundp
                           type-value-list-groundp)))

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
           ispace-var-list->name-when-not-consp)))

;; Further rules that profiling showed useless here and costly.
(local
 (in-theory
  (disable acl2::ustring-true-list
           acl2::cdr-preserves-ustring
           acl2::true-listp-when-utf8-partition
           acl2::utf8-partition-successful-when-any-valid-partitioning-exists
           acl2::utf8-table36-length-lemmas
           acl2::uchar-range
           acl2::integerp-of-car-when-integer-listp
           acl2::rationalp-of-car-when-rational-listp
           acl2::integer-listp-of-cdr-when-integer-listp
           acl2::rational-listp-of-cdr-when-rational-listp
           set::sets-are-true-lists-cheap
           str::consp-of-explode
           (:t omap::assoc-when-emptyp)
           (:t omap::head-key-when-emptyp)
           (:t omap::head-value-when-emptyp)
           (:t omap::tail-when-emptyp)
           omap::assoc-when-assoc-tail
           omap::assoc-when-assoc-of-tail-cheap
           omap::mapp-non-nil-implies-not-emptyp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lambda-lifting-relations
  :parents (lambda-lifting-validation)
  :short "The simulation relations between the values of a program and
          those of its lambda-lifted form."
  :long
  (xdoc::topstring
   (xdoc::p
    "The proof of @(tsee lambda-lift-validation-claim-p) is a simulation:
     evaluating an expression in an environment, and evaluating what
     @(tsee ll-expr) rebuilds it into in a related environment, give
     related values.  This book defines the relations.")
   (xdoc::p
    "Lambda lifting renames nothing and changes no type, so most values
     are related by equality.  What it changes is closures.  A lambda that
     is lifted evaluates, in the lifted program, to the partial application
     of its definition to the values of the variables it captures: a
     closure over the lambda's first parameter, whose body is the rest of
     the definition (the lambda over the remaining parameters, see @(tsee
     lambda-curried-body)), and whose environment binds the captured
     variables and the definitions it refers to.  A chain of unannotated
     lambdas is flattened into one definition (see @(tsee ll-lambda)), so
     the remaining parameters of the lifted closure are those of the whole
     chain (see @(tsee lambda-chain)).  A hoisted local function is the
     same, without the flattening.  A lambda that is kept evaluates to a
     closure whose body is what lifting rebuilds the original body into.
     In all cases the closure is related to the original one by the
     context of the traversal at the body --- the arguments of @(tsee
     ll-expr) there, see @(tsee ll-context) --- which a witness supplies,
     as the renamings do for @(tsee expr-value-alpha-related-via-p).")
   (xdoc::p
    "The environments of the two closures are related at that body, by
     @(tsee expr-denv-ll-related-p): each variable free in the original
     body is bound in the lifted environment to a related value, except
     that a hoisted local function is not bound, but its replacement
     evaluates to a related value; the variables of the lifted body that
     are not local --- the definitions it refers to, and the primitive
     operations --- are bound as they are at the top of the lifted
     program, in the environment @('genv') that the relations are
     parameterized by, where the definitions lifted out of the body are
     bound to their values (see @(tsee ll-defs-bound-p)); and the values
     meet what the transform relied on from the types
     it was given: a variable whose type is flat, closed, and evaluable
     has a value of matching dimensions, and a variable whose type was
     inferred from its binding has a value of that type (see @(tsee
     check-sound-p)).")
   (xdoc::p
    "On ground values the relation is equality (@(tsee
     expr-value-ll-related-p-when-groundp)), which is what the final
     theorem compares."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ll-context
  :short "Fixtype of the contexts of the lifting traversal."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the arguments of @(tsee ll-expr) other than the expression:
     the type environment, the variables whose types were inferred from
     their bindings, the local names, the map from the hoisted local
     functions to their replacements, and the names in use."))
  ((tenv string-type-map)
   (tlets acl2::string-set)
   (locals acl2::string-set)
   (lmap string-expr-map)
   (used acl2::string-set))
  :pred ll-context-p)

(define ll-context-new-expr ((x exprp) (ctx ll-context-p))
  :returns (new-x exprp)
  :short "What lifting rebuilds an expression into, in a context."
  (b* (((ll-context ctx) ctx)
       ((mv new-x & &)
        (ll-expr x ctx.tenv ctx.tlets ctx.locals ctx.lmap ctx.used)))
    new-x))

(define ll-context-lifted ((x exprp) (ctx ll-context-p))
  :returns (lifted bind-listp)
  :short "The definitions lifted out of an expression, in a context."
  (b* (((ll-context ctx) ctx)
       ((mv & lifted &)
        (ll-expr x ctx.tenv ctx.tlets ctx.locals ctx.lmap ctx.used)))
    lifted))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The shapes of closure bodies.

(define lambda-chain ((body exprp) (type? type-optionp))
  :returns (mv (params var+type?-listp)
               (inner exprp)
               (inner-type? type-optionp))
  :short "The parameters, body, and result type annotation that a chain of
          unannotated lambdas is flattened into."
  :long
  (xdoc::topstring
   (xdoc::p
    "The body and annotation are those of a lambda.  If the annotation is
     absent and the body is itself a lambda, it is absorbed, as by @(tsee
     ll-lambda) (see also @(tsee lambda-chain-result-type)): the result
     is the parameters absorbed, in order, and the body and annotation of
     the innermost lambda absorbed.  Otherwise nothing is absorbed."))
  (b* (((mv nestedp more inner inner-type?) (nested-lambda body))
       ((unless (and nestedp (type-option-case type? :none)))
        (mv nil (expr-fix body) (type-option-fix type?)))
       ((mv params inner inner-type?) (lambda-chain inner inner-type?)))
    (mv (append more params) inner inner-type?))
  :measure (expr-count body)
  :guard-hints (("Goal" :in-theory (enable nested-lambda)))
  :verify-guards :after-returns)

(define lifted-closure-body ((prest var+type?-listp)
                             (inner exprp)
                             (inner-type? type-optionp))
  :returns (body exprp)
  :short "The body of a closure over a parameter followed by others."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is @(tsee lambda-curried-body) for the parameter list that
     starts with the closure's own parameter, as a function of the rest."))
  (if (endp prest)
      (expr-fix inner)
    (expr-atom (make-atom-lambda/lambdan prest inner inner-type?))))

(define closure-body-parts ((body exprp)
                            (type? type-value-optionp)
                            (prest var+type?-listp)
                            (flat booleanp))
  :returns (mv (okp booleanp)
               (inner exprp)
               (inner-type? type-optionp))
  :short "Split the body of an original closure into the lambda over the
          remaining parameters @('prest') and the body of that lambda."
  :long
  (xdoc::topstring
   (xdoc::p
    "Without flattening, the body must be @(tsee lifted-closure-body) of
     the remaining parameters, as for the closure of a lambda over several
     parameters or of a local function.  With flattening, the remaining
     parameters must be those of the chain of unannotated lambdas that
     starts at the closure (see @(tsee lambda-chain)); the closure itself
     is unannotated exactly when it stores no result type, and then it
     has nothing to flatten."))
  (b* ((body (expr-fix body))
       (prest (var+type?-list-fix prest)))
    (cond (flat (if type?
                    (mv (endp prest) body (type-option-none))
                  (b* (((mv params inner inner-type?)
                        (lambda-chain body (type-option-none))))
                    (mv (equal params prest) inner inner-type?))))
          ((endp prest) (mv t body (type-option-none)))
          (t (b* (((mv & & inner inner-type?) (nested-lambda body)))
               (mv (equal body (lifted-closure-body prest inner inner-type?))
                   inner
                   inner-type?))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; What the transform relies on from the types of variables.

(define type-closed-p ((type typep))
  :returns (yes/no booleanp)
  :short "Whether a type has no free type or ispace variables."
  (and (set::emptyp (type-free-type-vars type))
       (set::emptyp (type-free-ispace-vars type))))

(define var-required-type ((name stringp) (tenv string-type-mapp))
  :short "The type value a variable's value must match the dimensions of,
          if any."
  :long
  (xdoc::topstring
   (xdoc::p
    "A variable may become a parameter of a lifted definition only if the
     type environment gives it a flat, closed type that evaluates (see
     @(tsee captured-params-typed-p)): its value is then checked against
     the value of that type, which this returns.  Otherwise this returns
     @('nil'), and there is no requirement."))
  (b* ((type? (name-to-type-option name tenv))
       ((unless (type-option-case type? :some)) nil)
       (type (type-option-some->val type?))
       ((unless (and (type-flat-syntax-p type)
                     (type-closed-p type)))
        nil)
       (tval (eval-type type (type-denv (ispace-denv nil) nil))))
    (if (reserrp tval) nil tval)))

(define value-meets-required-type-p ((val expr-valuep)
                                     (name stringp)
                                     (tenv string-type-mapp))
  :returns (yes/no booleanp)
  :short "Whether the value of a variable has the dimensions of its type,
          if that is required (see @(tsee var-required-type))."
  (b* ((tval (var-required-type name tenv)))
    (or (not tval)
        (expr-values-match-type-values-p (list val) (list tval))))
  :verify-guards nil)

(define value-has-inferred-type-p ((val expr-valuep)
                                   (name stringp)
                                   (tenv string-type-mapp))
  :returns (yes/no booleanp)
  :short "Whether the value of a variable whose type was inferred from its
          binding has that type."
  :long
  (xdoc::topstring
   (xdoc::p
    "Inferred types are closed (see @(tsee extend-tenv-with-let-bind)), so
     they are evaluated in the empty environment; the type is required to be
     closed, so that it evaluates alike in any environment."))
  (b* ((type? (name-to-type-option name tenv))
       ((unless (type-option-case type? :some)) nil)
       (type (type-option-some->val type?))
       (tval (eval-type type (type-denv (ispace-denv nil) nil))))
    (and (type-closed-p type)
         (not (reserrp tval))
         (expr-value-typed-p val tval)))
  :verify-guards nil)

(define param-type-consistent-p ((param var+typevalue-p)
                                 (tenv string-type-mapp))
  :returns (yes/no booleanp)
  :short "Whether the evaluated parameter of a closure has the type value
          required of the parameter's variable, if any."
  :long
  (xdoc::topstring
   (xdoc::p
    "Applying a closure checks the dimensions of the argument against the
     type value of its parameter, which then meets the requirement of
     @(tsee value-meets-required-type-p)."))
  (b* ((tval (var-required-type (var+typevalue->var param) tenv)))
    (or (not tval)
        (equal tval (var+typevalue->type param)))))

(define prest-tenv-consistent-p ((prest var+type?-listp)
                                 (tenv string-type-mapp))
  :returns (yes/no booleanp)
  :short "Whether the type environment gives the typed parameters in a list
          their own types."
  (b* (((when (endp prest)) t)
       ((var+type? p) (car prest)))
    (and (or (type-option-case p.type? :none)
             (equal (name-to-type-option p.var tenv) p.type?))
         (prest-tenv-consistent-p (cdr prest) tenv))))

(define names-in-context-p ((names string-listp) (ctx ll-context-p))
  :returns (yes/no booleanp)
  :short "Whether the names of parameters are local, and neither hoisted
          functions nor variables with inferred types, in a context."
  (b* (((when (endp names)) t)
       ((ll-context ctx) ctx)
       (name (str-fix (car names))))
    (and (set::in name ctx.locals)
         (not (omap::assoc name ctx.lmap))
         (not (set::in name ctx.tlets))
         (names-in-context-p (cdr names) ctx))))

(define names-bound-as-in-p ((names string-setp)
                             (new-denv expr-denvp)
                             (genv expr-denvp))
  :returns (yes/no booleanp)
  :short "Whether an environment binds some names as another one does,
          where that one binds them."
  :long
  (xdoc::topstring
   (xdoc::p
    "This says that the definitions and the primitive operations referred
     to by an expression of the lifted program are bound to what they are
     bound to at its top.  Names that @('genv') does not bind are
     unconstrained: the original program may refer to an unbound variable
     in code that it never evaluates."))
  (or (set::emptyp names)
      (b* ((name (set::head names))
           (gval (expr-denv-lookup-expr name genv)))
        (and (or (reserrp gval)
                 (equal (expr-denv-lookup-expr name new-denv) gval))
             (names-bound-as-in-p (set::tail names) new-denv genv))))
  :measure (acl2-count names)
  :verify-guards nil)

(define new-values-meet-types-p ((names string-setp)
                                 (new-denv expr-denvp)
                                 (tenv string-type-mapp))
  :returns (yes/no booleanp)
  :short "Whether an environment of the lifted program binds some local
          variables, to values that meet the requirements of their types."
  :long
  (xdoc::topstring
   (xdoc::p
    "A local variable that the lifted expression refers to may be captured
     by a lifted definition, whose application checks its value against
     the type of its parameter (see @(tsee value-meets-required-type-p)).
     The variables captured through the replacement of a hoisted function
     need not be free in the original expression, so this is required of
     the values in the lifted environment, not of the original ones."))
  (or (set::emptyp names)
      (b* ((name (set::head names))
           (val (expr-denv-lookup-expr name new-denv)))
        (and (not (reserrp val))
             (value-meets-required-type-p val name tenv)
             (new-values-meet-types-p (set::tail names) new-denv tenv))))
  :measure (acl2-count names)
  :verify-guards nil)

(define expr-denv-with-names-from ((names string-setp)
                                   (denv expr-denvp)
                                   (genv expr-denvp))
  :returns (new-denv expr-denvp)
  :short "Bind some names in an environment as another one binds them."
  :long
  (xdoc::topstring
   (xdoc::p
    "The names that @('genv') does not bind are left as they are.  This is
     how the replacement of a hoisted local function is evaluated by the
     relations: its function is a definition, bound at the top of the
     lifted program, and the environment at hand need not bind it, if the
     expression evaluated there does not refer to it."))
  (b* (((when (set::emptyp names)) (expr-denv-fix denv))
       (name (set::head names))
       (val (expr-denv-lookup-expr name genv))
       (denv (if (reserrp val) denv (expr-denv-add-expr name val denv))))
    (expr-denv-with-names-from (set::tail names) denv genv))
  :measure (acl2-count names)
  :verify-guards nil)

(define ll-defs-bound-p ((defs bind-listp) (genv expr-denvp))
  :returns (yes/no booleanp)
  :short "Whether definitions are bound at the top of the lifted program to
          what their bindings give them there."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each definition is a function binding, and @('genv') binds its name to
     the value that evaluating the binding in @('genv') would: a closure
     over @('genv') restricted to the variables the definition refers to.
     That is the fixed point that evaluating the definitions at the top
     reaches, since their names are fresh and distinct, and each refers only
     to the primitive operations and to definitions before it."))
  (b* (((when (endp defs)) t)
       (def (car defs))
       ((unless (bind-case def :fun)) nil)
       (name (bind-fun->var def))
       (ext (eval-bind def genv 1)))
    (and (not (reserrp ext))
         (equal (expr-denv-lookup-expr name genv)
                (expr-denv-lookup-expr name ext))
         (ll-defs-bound-p (cdr defs) genv)))
  :verify-guards nil)

(define genv-agrees-with-init-p ((genv expr-denvp))
  :returns (yes/no booleanp)
  :short "Whether an environment binds the primitive operations as the
          initial one does."
  (names-bound-as-in-p (omap::keys (expr-denv->exprs (init-expr-denv)))
                       genv
                       (init-expr-denv))
  :verify-guards nil)

; The shape of the replacement of a hoisted function: its definition's
; name, bound at the top and neither local nor among some names, applied to
; local variables that are not among those names.



(define var-expr-names ((es expr-listp))
  :returns (mv (okp booleanp) (names string-listp))
  :short "The names of a list of variable expressions, if they all are."
  (b* (((when (endp es)) (mv t nil))
       (e (car es))
       ((unless (expr-case e :var)) (mv nil nil))
       ((mv okp names) (var-expr-names (cdr es))))
    (mv okp (cons (expr-var->name e) names))))

(define replacement-parts ((repl exprp))
  :returns (mv (okp booleanp) (h stringp) (hns string-listp))
  :short "The name and the arguments of a replacement that applies a name to
          variables (see @(tsee apply-to-names)), if it is one."
  (expr-case
   repl
   :var (mv t repl.name nil)
   :app (if (and (expr-case repl.fun :var)
                 (expr-case repl.arg :var))
            (mv t (expr-var->name repl.fun) (list (expr-var->name repl.arg)))
          (mv nil "" nil))
   :appn (b* (((unless (expr-case repl.fun :var)) (mv nil "" nil))
              ((mv okp names) (var-expr-names repl.args))
              ((unless (and okp (consp (cdr names)))) (mv nil "" nil)))
           (mv t (expr-var->name repl.fun) names))
   :otherwise (mv nil "" nil))
  :verify-guards nil)

(define ll-replacement-ok-p ((repl exprp)
                             (locals string-setp)
                             (pnames string-listp)
                             (genv expr-denvp))
  :returns (yes/no booleanp)
  :short "Whether a replacement of a hoisted function has the expected
          shape."
  (b* (((mv okp h hns) (replacement-parts repl)))
    (and okp
         (not (set::in h (string-sfix locals)))
         (not (member-equal h (str::string-list-fix pnames)))
         (not (reserrp (expr-denv-lookup-expr h genv)))
         (subsetp-equal hns (string-sfix locals))
         (not (intersectp-equal hns (str::string-list-fix pnames)))))
  :verify-guards nil)

(define string-expr-map-closed-p ((lmap string-expr-mapp))
  :returns (yes/no booleanp)
  :short "Whether the expressions in a map are closed in type and ispace
          variables (an executable form of @(tsee lmap-closed-p))."
  (b* ((lmap (string-expr-map-fix lmap))
       ((when (omap::emptyp lmap)) t))
    (and (equal (expr-free-type-vars (omap::head-val lmap)) nil)
         (equal (expr-free-ispace-vars (omap::head-val lmap)) nil)
         (string-expr-map-closed-p (omap::tail lmap))))
  :measure (acl2-count (string-expr-map-fix lmap)))

(define lmap-replacements-ok-p ((lmap string-expr-mapp)
                                (locals string-setp)
                                (pnames string-listp)
                                (genv expr-denvp))
  :returns (yes/no booleanp)
  :verify-guards nil
  (b* ((lmap (string-expr-map-fix lmap))
       ((when (omap::emptyp lmap)) t))
    (and (ll-replacement-ok-p (omap::head-val lmap) locals pnames genv)
         (lmap-replacements-ok-p (omap::tail lmap) locals pnames genv)))
  :measure (acl2-count (string-expr-map-fix lmap)))

(define ll-context-ok-p ((x exprp) (ctx ll-context-p) (genv expr-denvp))
  :returns (yes/no booleanp)
  :short "The invariants of the lifting traversal that the simulation relies
          on, at an expression in a context."
  :long
  (xdoc::topstring
   (xdoc::p
    "The local names are in use, so that the fresh names of the
     definitions are not local; and the definitions lifted out of the
     expression are bound in @('genv') to their values (see @(tsee
     ll-defs-bound-p)).  The relations require this of the bodies of
     closures, so that the simulation can be applied to them when the
     closures are.  Besides, @('genv') is well formed and binds the
     primitive operations as the initial environment does, since the
     definitions' names are not theirs.  The replacements of the hoisted
     functions are closed in type and ispace variables, the hoisted
     functions are local, and each replacement is its definition's name,
     bound at the top, applied to local variables, neither of which is
     bound again in the expression.  The binders of the expression bind
     distinct names, which are in use and not local: a binder does not
     shadow a variable bound around the expression.  The type environment
     types only local variables, so a binder's name has no type there."))
  (b* (((ll-context c) ctx))
    (and (set::subset c.locals c.used)
         (ll-defs-bound-p (ll-context-lifted x ctx) genv)
         (genv-agrees-with-init-p genv)
         (expr-denv-wfp genv)
         (string-expr-map-closed-p c.lmap)
         (set::subset (omap::keys c.lmap) c.locals)
         (lmap-replacements-ok-p c.lmap c.locals (expr-binder-names x) genv)
         (not (expr-duplicate-names x))
         (subsetp-equal (expr-binder-names x) c.used)
         (not (intersectp-equal (expr-binder-names x) c.locals))
         (set::subset (omap::keys c.tenv) c.locals)))
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes ll-value-witnesses
  :short "Fixtypes of the witnesses of the relations."
  (fty::deftagsum ll-value-witness
    :short "Fixtype of the witnesses of @(tsee expr-value-ll-related-p)."
    :long
    (xdoc::topstring
     (xdoc::p
      "A ground value is related to itself.  A primitive operation, box,
       or vector is related componentwise.  A lambda value is related via
       the context at its body, the parameters that remain after its own,
       whether it flattens a chain, and a witness for its environment.
       A type or ispace lambda value is related via the context at its
       body and a witness for its environment."))
    (:ground ())
    (:primop ((ws ll-value-witness-list)))
    (:lambda ((ctx ll-context)
              (prest var+type?-list)
              (flat bool)
              (denv ll-denv-witness)))
    (:tlambda ((ctx ll-context)
               (denv ll-denv-witness)))
    (:box ((array ll-value-witness)))
    (:vector ((elems ll-value-witness-list)))
    :pred ll-value-witness-p
    :measure (two-nats-measure (acl2-count x) 0))
  (fty::deflist ll-value-witness-list
    :elt-type ll-value-witness
    :true-listp t
    :pred ll-value-witness-listp
    :measure (two-nats-measure (acl2-count x) 0))
  (fty::defomap string-ll-value-witness-map
    :key-type acl2::string
    :val-type ll-value-witness
    :pred string-ll-value-witness-mapp
    :measure (two-nats-measure (acl2-count x) 0))
  (fty::defprod ll-denv-witness
    :short "Fixtype of the witnesses of @(tsee expr-denv-ll-related-p)."
    :long
    (xdoc::topstring
     (xdoc::p
      "These are witnesses for the values of the variables (those not in
       the map are related as ground values), and a limit at which the
       replacements of the hoisted local functions evaluate."))
    ((vals string-ll-value-witness-map)
     (limit nat))
    :pred ll-denv-witness-p
    :measure (two-nats-measure (acl2-count x) 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines expr-value-ll-related-p
  :flag-local nil
  :verify-guards nil
  ;; The return types are boolean type prescriptions of the definitions.
  :returns-no-induct t

  (define expr-value-ll-related-p ((new-val expr-valuep)
                                   (val expr-valuep)
                                   (w ll-value-witness-p)
                                   (genv expr-denvp))
    :returns (yes/no booleanp)
    :short "Relatedness of a value of the lifted program
            to one of the original program, via a witness."
    :long
    (xdoc::topstring
     (xdoc::p
      "A lambda value is related to a lambda value with the same
       parameter and stored result type, whose body is the lambda over
       the remaining parameters (see @(tsee lifted-closure-body)) of what
       lifting rebuilds the original body into, in the context of the
       witness (see @(tsee closure-body-parts) for how the original body
       is split).  The parameters are distinct and local, and neither
       hoisted nor with inferred types, there, and the replacements of the
       hoisted functions there do not refer to them (see @(tsee
       ll-replacement-ok-p)), so that binding them leaves the replacements'
       values alone; the parameter's type value is the one its variable
       requires, if any, and the remaining ones are typed as the context
       types them.  The environments are related at the body (see @(tsee
       expr-denv-ll-related-p)), excluding the parameters.")
     (xdoc::p
      "A type or ispace lambda value is related to one with the same
       parameter, whose body is what lifting rebuilds the original body
       into in the context of the witness, with environments related at
       the body.")
     (xdoc::p
      "Ground values are related to themselves, and boxes, vectors, and
       primitive operations componentwise.  An empty vector is related to
       itself even if it is not ground: its element type value may be that
       of functions, which lifting does not change."))
    :measure (expr-value-count val)
    (b* (((when (ll-value-witness-case w :ground))
          (and (equal (expr-value-fix new-val) (expr-value-fix val))
               (expr-value-groundp val))))
      (expr-value-case
       val
       :base nil
       :vector-empty (equal (expr-value-fix new-val) (expr-value-fix val))
       :primop (and (expr-value-case new-val :primop)
                    (ll-value-witness-case w :primop)
                    (primop-value-ll-related-p
                     (expr-value-primop->val new-val)
                     val.val
                     (ll-value-witness-primop->ws w)
                     genv))
       :lambda
       (b* (((unless (expr-value-case new-val :lambda)) nil)
            ((unless (ll-value-witness-case w :lambda)) nil)
            ((ll-value-witness-lambda w-) w)
            ((ll-context c) w-.ctx)
            ((expr-value-lambda u) new-val)
            ((mv okp inner inner-type?)
             (closure-body-parts val.body val.type? w-.prest w-.flat))
            (pnames (cons (var+typevalue->var val.param)
                          (var+type?-list->var w-.prest))))
         (and okp
              (equal u.param val.param)
              (equal u.type? val.type?)
              (equal u.body
                     (lifted-closure-body w-.prest
                                          (ll-context-new-expr inner w-.ctx)
                                          inner-type?))
              (no-duplicatesp-equal pnames)
              (names-in-context-p pnames w-.ctx)
              (lmap-replacements-ok-p c.lmap c.locals pnames genv)
              (param-type-consistent-p val.param c.tenv)
              (prest-tenv-consistent-p w-.prest c.tenv)
              (ll-context-ok-p inner w-.ctx genv)
              (expr-denv-ll-related-p u.denv val.denv inner w-.ctx pnames
                                      w-.denv genv)))
       :tlambda
       (b* (((unless (expr-value-case new-val :tlambda)) nil)
            ((unless (ll-value-witness-case w :tlambda)) nil)
            ((ll-value-witness-tlambda w-) w)
            ((expr-value-tlambda u) new-val))
         (and (equal u.param val.param)
              (equal u.body (ll-context-new-expr val.body w-.ctx))
              (ll-context-ok-p val.body w-.ctx genv)
              (expr-denv-ll-related-p u.denv val.denv val.body w-.ctx nil
                                      w-.denv genv)))
       :ilambda
       (b* (((unless (expr-value-case new-val :ilambda)) nil)
            ((unless (ll-value-witness-case w :tlambda)) nil)
            ((ll-value-witness-tlambda w-) w)
            ((expr-value-ilambda u) new-val))
         (and (equal u.param val.param)
              (equal u.body (ll-context-new-expr val.body w-.ctx))
              (ll-context-ok-p val.body w-.ctx genv)
              (expr-denv-ll-related-p u.denv val.denv val.body w-.ctx nil
                                      w-.denv genv)))
       :box (and (expr-value-case new-val :box)
                 (ll-value-witness-case w :box)
                 (equal (expr-value-box->ispace new-val) val.ispace)
                 (equal (expr-value-box->type new-val) val.type)
                 (expr-value-ll-related-p (expr-value-box->array new-val)
                                          val.array
                                          (ll-value-witness-box->array w)
                                          genv))
       :vector (and (expr-value-case new-val :vector)
                    (ll-value-witness-case w :vector)
                    (expr-value-list-ll-related-p
                     (expr-value-vector->elems new-val)
                     val.elems
                     (ll-value-witness-vector->elems w)
                     genv)))))

  (define expr-value-list-ll-related-p ((new-vals expr-value-listp)
                                        (vals expr-value-listp)
                                        (ws ll-value-witness-listp)
                                        (genv expr-denvp))
    :returns (yes/no booleanp)
    :short "Pointwise relatedness of lists of values."
    :measure (expr-value-list-count vals)
    (if (endp vals)
        (endp new-vals)
      (and (consp new-vals)
           (expr-value-ll-related-p (car new-vals) (car vals) (car ws) genv)
           (expr-value-list-ll-related-p (cdr new-vals) (cdr vals) (cdr ws)
                                         genv))))

  (define expr-denv-ll-related-p ((new-denv expr-denvp)
                                  (denv expr-denvp)
                                  (x exprp)
                                  (ctx ll-context-p)
                                  (excl string-listp)
                                  (dw ll-denv-witness-p)
                                  (genv expr-denvp))
    :returns (yes/no booleanp)
    :short "Relatedness of an environment of the lifted program to one of
            the original program, at an expression in a context."
    :long
    (xdoc::topstring
     (xdoc::p
      "The expression is the one evaluated in the original environment;
       what lifting rebuilds it into in the context is evaluated in the
       lifted one.  The type environments are equal.  The variables free
       in the expression, other than those in @('excl') (the parameters
       of a closure, not yet bound), are related as described in @(tsee
       string-expr-value-map-ll-related-p).  The variables free in the
       rebuilt expression that are not local in the context are bound as
       in @('genv'), where it binds them: they are the definitions lifted
       before or out of the expression, and the primitive operations."))
    :measure (expr-denv-count denv)
    (b* (((ll-context c) ctx)
         (fv (set::difference (expr-free-expr-vars x)
                              (set::mergesort (str::string-list-fix excl))))
         (nfv (expr-free-expr-vars (ll-context-new-expr x ctx))))
      (and (equal (expr-denv->tenv new-denv) (expr-denv->tenv denv))
           (string-expr-value-map-ll-related-p new-denv
                                               (expr-denv->exprs denv)
                                               fv nfv ctx dw genv)
           (names-bound-as-in-p (set::difference nfv c.locals) new-denv genv)
           (new-values-meet-types-p
            (set::difference (set::intersect nfv c.locals)
                             (set::mergesort (str::string-list-fix excl)))
            new-denv c.tenv))))

  (define string-expr-value-map-ll-related-p ((new-denv expr-denvp)
                                              (map string-expr-value-mapp)
                                              (fv string-setp)
                                              (nfv string-setp)
                                              (ctx ll-context-p)
                                              (dw ll-denv-witness-p)
                                              (genv expr-denvp))
    :returns (yes/no booleanp)
    :short "Relatedness of the variables of an environment of the original
            program, as far as they are in a set, to the lifted program's
            environment."
    :long
    (xdoc::topstring
     (xdoc::p
      "Each variable of the map that is in @('fv') is bound in the lifted
       environment to a value related to its value in the map, via its
       witness, unless it is a hoisted local function: then its
       replacement evaluates, at the limit of the witness, to a related
       value, in the lifted environment with the replacement's function
       bound as in @('genv') (see @(tsee expr-denv-with-names-from)).
       This is required only if the rebuilt expression refers to the
       variable, or to all the local variables of its replacement (which
       @('nfv') has): a variable used only in lambdas that are lifted out
       is not referred to, unless it is local, when they capture it; the
       function of a replacement is not local, and the lifted lambdas that
       use it refer to it themselves.  Its value meets the requirement
       of its type (see @(tsee value-meets-required-type-p)); if its type
       was inferred from its binding, its value has that type; and if it
       is not local, it is a primitive operation, bound as at the top."))
    :measure (string-expr-value-map-count map)
    (b* ((map (string-expr-value-map-fix map))
         ((when (omap::emptyp map)) t)
         ((mv var val) (omap::head map))
         ((ll-context c) ctx)
         ((ll-denv-witness d) dw)
         (wpair (omap::assoc var d.vals))
         (w (if wpair (cdr wpair) (ll-value-witness-ground)))
         (lpair (omap::assoc var c.lmap))
         (rvars (and lpair (expr-free-expr-vars (cdr lpair))))
         (referredp (if lpair
                        (set::subset (set::intersect rvars c.locals) nfv)
                      (set::in var nfv)))
         (new-val (if lpair
                      (eval-expr (cdr lpair)
                                 (expr-denv-with-names-from
                                  (set::difference rvars c.locals)
                                  new-denv
                                  genv)
                                 d.limit)
                    (expr-denv-lookup-expr var new-denv))))
      (and (or (not (set::in var fv))
               (and (or (not referredp)
                        (and (not (reserrp new-val))
                             (expr-value-ll-related-p new-val val w genv)))
                    (value-meets-required-type-p val var c.tenv)
                    (or (not (set::in var c.tlets))
                        (value-has-inferred-type-p val var c.tenv))
                    (or (set::in var c.locals)
                        (equal val (expr-denv-lookup-expr var
                                                          (init-expr-denv))))))
           (string-expr-value-map-ll-related-p new-denv
                                               (omap::tail map)
                                               fv nfv ctx dw genv))))

  (define primop-value-ll-related-p ((new-op primop-valuep)
                                     (op primop-valuep)
                                     (ws ll-value-witness-listp)
                                     (genv expr-denvp))
    :returns (yes/no booleanp)
    :short "Relatedness of primitive-operation values, via witnesses for
            the embedded expression values (in order)."
    :long
    (xdoc::topstring
     (xdoc::p
      "The two values must be at the same stage of the same operation,
       with equal components other than expression values, which are
       related via the corresponding witnesses."))
    :measure (primop-value-count op)
    (b* ((ws (ll-value-witness-list-fix ws)))
      (primop-value-case
       op
       :int-unary (and (primop-value-case new-op :int-unary)
                       (equal (primop-value-int-unary->op new-op) op.op))
       :int-binary (and (primop-value-case new-op :int-binary)
                        (equal (primop-value-int-binary->op new-op) op.op))
       :int-binary-x (and (primop-value-case new-op :int-binary-x)
                          (equal (primop-value-int-binary-x->op new-op) op.op)
                          (expr-value-ll-related-p (primop-value-int-binary-x->xval new-op) op.xval (car ws) genv))
       :int-rel (and (primop-value-case new-op :int-rel)
                     (equal (primop-value-int-rel->op new-op) op.op))
       :int-rel-x (and (primop-value-case new-op :int-rel-x)
                       (equal (primop-value-int-rel-x->op new-op) op.op)
                       (expr-value-ll-related-p (primop-value-int-rel-x->xval new-op) op.xval (car ws) genv))
       :int-to-float (primop-value-case new-op :int-to-float)
       :int-to-bool (primop-value-case new-op :int-to-bool)
       :float-unary (and (primop-value-case new-op :float-unary)
                         (equal (primop-value-float-unary->op new-op) op.op))
       :float-binary (and (primop-value-case new-op :float-binary)
                          (equal (primop-value-float-binary->op new-op) op.op))
       :float-binary-x (and (primop-value-case new-op :float-binary-x)
                            (equal (primop-value-float-binary-x->op new-op) op.op)
                            (expr-value-ll-related-p (primop-value-float-binary-x->xval new-op) op.xval (car ws) genv))
       :float-rel (and (primop-value-case new-op :float-rel)
                       (equal (primop-value-float-rel->op new-op) op.op))
       :float-rel-x (and (primop-value-case new-op :float-rel-x)
                         (equal (primop-value-float-rel-x->op new-op) op.op)
                         (expr-value-ll-related-p (primop-value-float-rel-x->xval new-op) op.xval (car ws) genv))
       :float-truncate (primop-value-case new-op :float-truncate)
       :float-round (primop-value-case new-op :float-round)
       :float-ceiling (primop-value-case new-op :float-ceiling)
       :float-floor (primop-value-case new-op :float-floor)
       :bool-unary (and (primop-value-case new-op :bool-unary)
                        (equal (primop-value-bool-unary->op new-op) op.op))
       :bool-binary (and (primop-value-case new-op :bool-binary)
                         (equal (primop-value-bool-binary->op new-op) op.op))
       :bool-binary-x (and (primop-value-case new-op :bool-binary-x)
                           (equal (primop-value-bool-binary-x->op new-op) op.op)
                           (expr-value-ll-related-p (primop-value-bool-binary-x->xval new-op) op.xval (car ws) genv))
       :bool-rel (and (primop-value-case new-op :bool-rel)
                      (equal (primop-value-bool-rel->op new-op) op.op))
       :bool-rel-x (and (primop-value-case new-op :bool-rel-x)
                        (equal (primop-value-bool-rel-x->op new-op) op.op)
                        (expr-value-ll-related-p (primop-value-bool-rel-x->xval new-op) op.xval (car ws) genv))
       :bool-to-int (primop-value-case new-op :bool-to-int)
       :bool-to-float (primop-value-case new-op :bool-to-float)
       :head (primop-value-case new-op :head)
       :head-t (and (primop-value-case new-op :head-t)
                    (equal (primop-value-head-t->tval new-op) op.tval))
       :head-t-d (and (primop-value-case new-op :head-t-d)
                      (equal (primop-value-head-t-d->tval new-op) op.tval)
                      (equal (primop-value-head-t-d->dval new-op) op.dval))
       :head-t-d-s (and (primop-value-case new-op :head-t-d-s)
                        (equal (primop-value-head-t-d-s->tval new-op) op.tval)
                        (equal (primop-value-head-t-d-s->dval new-op) op.dval)
                        (equal (primop-value-head-t-d-s->sval new-op) op.sval))
       :tail (primop-value-case new-op :tail)
       :tail-t (and (primop-value-case new-op :tail-t)
                    (equal (primop-value-tail-t->tval new-op) op.tval))
       :tail-t-d (and (primop-value-case new-op :tail-t-d)
                      (equal (primop-value-tail-t-d->tval new-op) op.tval)
                      (equal (primop-value-tail-t-d->dval new-op) op.dval))
       :tail-t-d-s (and (primop-value-case new-op :tail-t-d-s)
                        (equal (primop-value-tail-t-d-s->tval new-op) op.tval)
                        (equal (primop-value-tail-t-d-s->dval new-op) op.dval)
                        (equal (primop-value-tail-t-d-s->sval new-op) op.sval))
       :length (primop-value-case new-op :length)
       :length-t (and (primop-value-case new-op :length-t)
                      (equal (primop-value-length-t->tval new-op) op.tval))
       :length-t-d (and (primop-value-case new-op :length-t-d)
                        (equal (primop-value-length-t-d->tval new-op) op.tval)
                        (equal (primop-value-length-t-d->dval new-op) op.dval))
       :length-t-d-s (and (primop-value-case new-op :length-t-d-s)
                          (equal (primop-value-length-t-d-s->tval new-op) op.tval)
                          (equal (primop-value-length-t-d-s->dval new-op) op.dval)
                          (equal (primop-value-length-t-d-s->sval new-op) op.sval))
       :append (primop-value-case new-op :append)
       :append-t (and (primop-value-case new-op :append-t)
                      (equal (primop-value-append-t->tval new-op) op.tval))
       :append-t-m (and (primop-value-case new-op :append-t-m)
                        (equal (primop-value-append-t-m->tval new-op) op.tval)
                        (equal (primop-value-append-t-m->mval new-op) op.mval))
       :append-t-m-n (and (primop-value-case new-op :append-t-m-n)
                          (equal (primop-value-append-t-m-n->tval new-op) op.tval)
                          (equal (primop-value-append-t-m-n->mval new-op) op.mval)
                          (equal (primop-value-append-t-m-n->nval new-op) op.nval))
       :append-t-m-n-s (and (primop-value-case new-op :append-t-m-n-s)
                            (equal (primop-value-append-t-m-n-s->tval new-op) op.tval)
                            (equal (primop-value-append-t-m-n-s->mval new-op) op.mval)
                            (equal (primop-value-append-t-m-n-s->nval new-op) op.nval)
                            (equal (primop-value-append-t-m-n-s->sval new-op) op.sval))
       :append-t-m-n-s-x (and (primop-value-case new-op :append-t-m-n-s-x)
                              (equal (primop-value-append-t-m-n-s-x->tval new-op) op.tval)
                              (equal (primop-value-append-t-m-n-s-x->mval new-op) op.mval)
                              (equal (primop-value-append-t-m-n-s-x->nval new-op) op.nval)
                              (equal (primop-value-append-t-m-n-s-x->sval new-op) op.sval)
                              (expr-value-ll-related-p (primop-value-append-t-m-n-s-x->xval new-op) op.xval (car ws) genv))
       :reverse (primop-value-case new-op :reverse)
       :reverse-t (and (primop-value-case new-op :reverse-t)
                       (equal (primop-value-reverse-t->tval new-op) op.tval))
       :reverse-t-d (and (primop-value-case new-op :reverse-t-d)
                         (equal (primop-value-reverse-t-d->tval new-op) op.tval)
                         (equal (primop-value-reverse-t-d->dval new-op) op.dval))
       :reverse-t-d-s (and (primop-value-case new-op :reverse-t-d-s)
                           (equal (primop-value-reverse-t-d-s->tval new-op) op.tval)
                           (equal (primop-value-reverse-t-d-s->dval new-op) op.dval)
                           (equal (primop-value-reverse-t-d-s->sval new-op) op.sval))
       :index (primop-value-case new-op :index)
       :index-t (and (primop-value-case new-op :index-t)
                     (equal (primop-value-index-t->tval new-op) op.tval))
       :index-t-m (and (primop-value-case new-op :index-t-m)
                       (equal (primop-value-index-t-m->tval new-op) op.tval)
                       (equal (primop-value-index-t-m->mval new-op) op.mval))
       :index-t-m-x (and (primop-value-case new-op :index-t-m-x)
                         (equal (primop-value-index-t-m-x->tval new-op) op.tval)
                         (equal (primop-value-index-t-m-x->mval new-op) op.mval)
                         (expr-value-ll-related-p (primop-value-index-t-m-x->xval new-op) op.xval (car ws) genv))
       :index2d (primop-value-case new-op :index2d)
       :index2d-t (and (primop-value-case new-op :index2d-t)
                       (equal (primop-value-index2d-t->tval new-op) op.tval))
       :index2d-t-m (and (primop-value-case new-op :index2d-t-m)
                         (equal (primop-value-index2d-t-m->tval new-op) op.tval)
                         (equal (primop-value-index2d-t-m->mval new-op) op.mval))
       :index2d-t-m-n (and (primop-value-case new-op :index2d-t-m-n)
                           (equal (primop-value-index2d-t-m-n->tval new-op) op.tval)
                           (equal (primop-value-index2d-t-m-n->mval new-op) op.mval)
                           (equal (primop-value-index2d-t-m-n->nval new-op) op.nval))
       :index2d-t-m-n-x (and (primop-value-case new-op :index2d-t-m-n-x)
                             (equal (primop-value-index2d-t-m-n-x->tval new-op) op.tval)
                             (equal (primop-value-index2d-t-m-n-x->mval new-op) op.mval)
                             (equal (primop-value-index2d-t-m-n-x->nval new-op) op.nval)
                             (expr-value-ll-related-p (primop-value-index2d-t-m-n-x->xval new-op) op.xval (car ws) genv))
       :sum (primop-value-case new-op :sum)
       :sum-s (and (primop-value-case new-op :sum-s)
                   (equal (primop-value-sum-s->sval new-op) op.sval))
       :reshape (primop-value-case new-op :reshape)
       :reshape-t (and (primop-value-case new-op :reshape-t)
                       (equal (primop-value-reshape-t->tval new-op) op.tval))
       :reshape-t-s1 (and (primop-value-case new-op :reshape-t-s1)
                          (equal (primop-value-reshape-t-s1->tval new-op) op.tval)
                          (equal (primop-value-reshape-t-s1->s1val new-op) op.s1val))
       :reshape-t-s1-s2 (and (primop-value-case new-op :reshape-t-s1-s2)
                             (equal (primop-value-reshape-t-s1-s2->tval new-op) op.tval)
                             (equal (primop-value-reshape-t-s1-s2->s1val new-op) op.s1val)
                             (equal (primop-value-reshape-t-s1-s2->s2val new-op) op.s2val))
       :flatten (primop-value-case new-op :flatten)
       :flatten-t (and (primop-value-case new-op :flatten-t)
                       (equal (primop-value-flatten-t->tval new-op) op.tval))
       :flatten-t-m (and (primop-value-case new-op :flatten-t-m)
                         (equal (primop-value-flatten-t-m->tval new-op) op.tval)
                         (equal (primop-value-flatten-t-m->mval new-op) op.mval))
       :flatten-t-m-n (and (primop-value-case new-op :flatten-t-m-n)
                           (equal (primop-value-flatten-t-m-n->tval new-op) op.tval)
                           (equal (primop-value-flatten-t-m-n->mval new-op) op.mval)
                           (equal (primop-value-flatten-t-m-n->nval new-op) op.nval))
       :flatten-t-m-n-s (and (primop-value-case new-op :flatten-t-m-n-s)
                             (equal (primop-value-flatten-t-m-n-s->tval new-op) op.tval)
                             (equal (primop-value-flatten-t-m-n-s->mval new-op) op.mval)
                             (equal (primop-value-flatten-t-m-n-s->nval new-op) op.nval)
                             (equal (primop-value-flatten-t-m-n-s->sval new-op) op.sval))
       :transpose2d (primop-value-case new-op :transpose2d)
       :transpose2d-t (and (primop-value-case new-op :transpose2d-t)
                           (equal (primop-value-transpose2d-t->tval new-op) op.tval))
       :transpose2d-t-m (and (primop-value-case new-op :transpose2d-t-m)
                             (equal (primop-value-transpose2d-t-m->tval new-op) op.tval)
                             (equal (primop-value-transpose2d-t-m->mval new-op) op.mval))
       :transpose2d-t-m-n (and (primop-value-case new-op :transpose2d-t-m-n)
                               (equal (primop-value-transpose2d-t-m-n->tval new-op) op.tval)
                               (equal (primop-value-transpose2d-t-m-n->mval new-op) op.mval)
                               (equal (primop-value-transpose2d-t-m-n->nval new-op) op.nval))
       :iota/static (primop-value-case new-op :iota/static)
       :reduce (primop-value-case new-op :reduce)
       :reduce-t (and (primop-value-case new-op :reduce-t)
                      (equal (primop-value-reduce-t->tval new-op) op.tval))
       :reduce-t-d (and (primop-value-case new-op :reduce-t-d)
                        (equal (primop-value-reduce-t-d->tval new-op) op.tval)
                        (equal (primop-value-reduce-t-d->dval new-op) op.dval))
       :reduce-t-d-s (and (primop-value-case new-op :reduce-t-d-s)
                          (equal (primop-value-reduce-t-d-s->tval new-op) op.tval)
                          (equal (primop-value-reduce-t-d-s->dval new-op) op.dval)
                          (equal (primop-value-reduce-t-d-s->sval new-op) op.sval))
       :reduce-t-d-s-f (and (primop-value-case new-op :reduce-t-d-s-f)
                            (equal (primop-value-reduce-t-d-s-f->tval new-op) op.tval)
                            (equal (primop-value-reduce-t-d-s-f->dval new-op) op.dval)
                            (equal (primop-value-reduce-t-d-s-f->sval new-op) op.sval)
                            (expr-value-ll-related-p (primop-value-reduce-t-d-s-f->fval new-op) op.fval (car ws) genv))
       :fold (primop-value-case new-op :fold)
       :fold-t (and (primop-value-case new-op :fold-t)
                    (equal (primop-value-fold-t->tval new-op) op.tval))
       :fold-t-t2 (and (primop-value-case new-op :fold-t-t2)
                       (equal (primop-value-fold-t-t2->tval new-op) op.tval)
                       (equal (primop-value-fold-t-t2->t2val new-op) op.t2val))
       :fold-t-t2-d (and (primop-value-case new-op :fold-t-t2-d)
                         (equal (primop-value-fold-t-t2-d->tval new-op) op.tval)
                         (equal (primop-value-fold-t-t2-d->t2val new-op) op.t2val)
                         (equal (primop-value-fold-t-t2-d->dval new-op) op.dval))
       :fold-t-t2-d-s (and (primop-value-case new-op :fold-t-t2-d-s)
                           (equal (primop-value-fold-t-t2-d-s->tval new-op) op.tval)
                           (equal (primop-value-fold-t-t2-d-s->t2val new-op) op.t2val)
                           (equal (primop-value-fold-t-t2-d-s->dval new-op) op.dval)
                           (equal (primop-value-fold-t-t2-d-s->sval new-op) op.sval))
       :fold-t-t2-d-s-s2 (and (primop-value-case new-op :fold-t-t2-d-s-s2)
                              (equal (primop-value-fold-t-t2-d-s-s2->tval new-op) op.tval)
                              (equal (primop-value-fold-t-t2-d-s-s2->t2val new-op) op.t2val)
                              (equal (primop-value-fold-t-t2-d-s-s2->dval new-op) op.dval)
                              (equal (primop-value-fold-t-t2-d-s-s2->sval new-op) op.sval)
                              (equal (primop-value-fold-t-t2-d-s-s2->s2val new-op) op.s2val))
       :fold-t-t2-d-s-s2-f (and (primop-value-case new-op :fold-t-t2-d-s-s2-f)
                                (equal (primop-value-fold-t-t2-d-s-s2-f->tval new-op) op.tval)
                                (equal (primop-value-fold-t-t2-d-s-s2-f->t2val new-op) op.t2val)
                                (equal (primop-value-fold-t-t2-d-s-s2-f->dval new-op) op.dval)
                                (equal (primop-value-fold-t-t2-d-s-s2-f->sval new-op) op.sval)
                                (equal (primop-value-fold-t-t2-d-s-s2-f->s2val new-op) op.s2val)
                                (expr-value-ll-related-p (primop-value-fold-t-t2-d-s-s2-f->fval new-op) op.fval (car ws) genv))
       :fold-t-t2-d-s-s2-f-z (and (primop-value-case new-op :fold-t-t2-d-s-s2-f-z)
                                  (equal (primop-value-fold-t-t2-d-s-s2-f-z->tval new-op) op.tval)
                                  (equal (primop-value-fold-t-t2-d-s-s2-f-z->t2val new-op) op.t2val)
                                  (equal (primop-value-fold-t-t2-d-s-s2-f-z->dval new-op) op.dval)
                                  (equal (primop-value-fold-t-t2-d-s-s2-f-z->sval new-op) op.sval)
                                  (equal (primop-value-fold-t-t2-d-s-s2-f-z->s2val new-op) op.s2val)
                                  (expr-value-ll-related-p (primop-value-fold-t-t2-d-s-s2-f-z->fval new-op) op.fval (car ws) genv)
                                  (expr-value-ll-related-p (primop-value-fold-t-t2-d-s-s2-f-z->zval new-op) op.zval (cadr ws) genv))
       :reify-dim (primop-value-case new-op :reify-dim)
       :reify-shape (primop-value-case new-op :reify-shape)
       :iota (primop-value-case new-op :iota)
       :iota-d (and (primop-value-case new-op :iota-d)
                    (equal (primop-value-iota-d->dval new-op) op.dval))
       :trace (primop-value-case new-op :trace)
       :trace-t (and (primop-value-case new-op :trace-t)
                     (equal (primop-value-trace-t->tval new-op) op.tval))
       :trace-t-r (and (primop-value-case new-op :trace-t-r)
                       (equal (primop-value-trace-t-r->tval new-op) op.tval)
                       (equal (primop-value-trace-t-r->rval new-op) op.rval))
       :trace-t-r-s (and (primop-value-case new-op :trace-t-r-s)
                         (equal (primop-value-trace-t-r-s->tval new-op) op.tval)
                         (equal (primop-value-trace-t-r-s->rval new-op) op.rval)
                         (equal (primop-value-trace-t-r-s->sval new-op) op.sval))
       :trace-t-r-s-q (and (primop-value-case new-op :trace-t-r-s-q)
                           (equal (primop-value-trace-t-r-s-q->tval new-op) op.tval)
                           (equal (primop-value-trace-t-r-s-q->rval new-op) op.rval)
                           (equal (primop-value-trace-t-r-s-q->sval new-op) op.sval)
                           (equal (primop-value-trace-t-r-s-q->qval new-op) op.qval))
       :trace-t-r-s-q-x (and (primop-value-case new-op :trace-t-r-s-q-x)
                             (equal (primop-value-trace-t-r-s-q-x->tval new-op) op.tval)
                             (equal (primop-value-trace-t-r-s-q-x->rval new-op) op.rval)
                             (equal (primop-value-trace-t-r-s-q-x->sval new-op) op.sval)
                             (equal (primop-value-trace-t-r-s-q-x->qval new-op) op.qval)
                             (expr-value-ll-related-p (primop-value-trace-t-r-s-q-x->xval new-op) op.xval (car ws) genv))
       :undefined (primop-value-case new-op :undefined)
       :undefined-t (and (primop-value-case new-op :undefined-t)
                         (equal (primop-value-undefined-t->tval new-op) op.tval))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Every ground value is related to itself.

(defrule expr-value-ll-related-p-of-ground
  (implies (expr-value-groundp val)
           (expr-value-ll-related-p val val (ll-value-witness-ground) genv))
  :expand ((:free (w) (expr-value-ll-related-p val val w genv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; On ground values the relation is equality, by induction on the relation;
; the lambda cases do not arise, so neither do the environment ones.
;
; The local lemmas supply the final step of each case: two values of the
; same kind with equal components have equal fixes.  They are stated as
; conditional equalities of fixes (rather than by enabling the generated
; EXPR-VALUE-FIX-WHEN-* rules) because those rules loop with the enabled
; EXPR-VALUE-*-OF-FIELDS rules.

(defruledl equal-of-expr-value-fix-when-both-base
  (implies (and (equal (expr-value-kind x) :base)
                (equal (expr-value-kind y) :base)
                (equal (expr-value-base->val x) (expr-value-base->val y)))
           (equal (equal (expr-value-fix x) (expr-value-fix y)) t))
  :use ((:instance expr-value-fix-when-base (x x))
        (:instance expr-value-fix-when-base (x y))))

(defruledl equal-of-expr-value-fix-when-both-primop
  (implies (and (equal (expr-value-kind x) :primop)
                (equal (expr-value-kind y) :primop)
                (equal (expr-value-primop->val x) (expr-value-primop->val y)))
           (equal (equal (expr-value-fix x) (expr-value-fix y)) t))
  :use ((:instance expr-value-fix-when-primop (x x))
        (:instance expr-value-fix-when-primop (x y))))

(defruledl equal-of-expr-value-fix-when-both-box
  (implies (and (equal (expr-value-kind x) :box)
                (equal (expr-value-kind y) :box)
                (equal (expr-value-box->ispace x) (expr-value-box->ispace y))
                (equal (expr-value-box->array x) (expr-value-box->array y))
                (equal (expr-value-box->type x) (expr-value-box->type y)))
           (equal (equal (expr-value-fix x) (expr-value-fix y)) t))
  :use ((:instance expr-value-fix-when-box (x x))
        (:instance expr-value-fix-when-box (x y))))

(defruledl equal-of-expr-value-fix-when-both-vector
  (implies (and (equal (expr-value-kind x) :vector)
                (equal (expr-value-kind y) :vector)
                (equal (expr-value-vector->elems x) (expr-value-vector->elems y)))
           (equal (equal (expr-value-fix x) (expr-value-fix y)) t))
  :use ((:instance expr-value-fix-when-vector (x x))
        (:instance expr-value-fix-when-vector (x y))))

(defruledl equal-of-expr-value-fix-when-both-vector-empty
  (implies (and (equal (expr-value-kind x) :vector-empty)
                (equal (expr-value-kind y) :vector-empty)
                (equal (expr-value-vector-empty->dims x)
                       (expr-value-vector-empty->dims y))
                (equal (expr-value-vector-empty->elem x)
                       (expr-value-vector-empty->elem y)))
           (equal (equal (expr-value-fix x) (expr-value-fix y)) t))
  :use ((:instance expr-value-fix-when-vector-empty (x x))
        (:instance expr-value-fix-when-vector-empty (x y))))

;; An induction scheme for the theorem below.  It makes the recursive calls
;; of the relation, with the same arguments, but only under the tests on the
;; original value; the relation's own scheme also splits on the kind and
;; fields of the new value, making 316 cases (instead of 21), each of which
;; re-expands the large case splits of the primitive operation values.

(local
 (defun ll-groundp-ind (flag new-val val w new-vals vals ws new-op op)
   (declare (xargs :measure (case flag
                              (expr-value-ll-related-p (expr-value-count val))
                              (expr-value-list-ll-related-p
                               (expr-value-list-count vals))
                              ((expr-denv-ll-related-p
                                string-expr-value-map-ll-related-p)
                               0)
                              (otherwise (primop-value-count op)))
                   :verify-guards nil)
            (irrelevant new-val w new-vals ws new-op))
   (case flag
     (expr-value-ll-related-p
      (expr-value-case
       val
       :primop (ll-groundp-ind 'primop-value-ll-related-p
                               new-val val w new-vals vals
                               (ll-value-witness-primop->ws w)
                               (expr-value-primop->val new-val)
                               (expr-value-primop->val val))
       :box (ll-groundp-ind 'expr-value-ll-related-p
                            (expr-value-box->array new-val)
                            (expr-value-box->array val)
                            (ll-value-witness-box->array w)
                            new-vals vals ws new-op op)
       :vector (ll-groundp-ind 'expr-value-list-ll-related-p
                               new-val val w
                               (expr-value-vector->elems new-val)
                               (expr-value-vector->elems val)
                               (ll-value-witness-vector->elems w)
                               new-op op)
       :otherwise nil))
     (expr-value-list-ll-related-p
      (if (endp vals)
          nil
        (list (ll-groundp-ind 'expr-value-ll-related-p
                              (car new-vals) (car vals) (car ws)
                              new-vals vals ws new-op op)
              (ll-groundp-ind 'expr-value-list-ll-related-p
                              new-val val w
                              (cdr new-vals) (cdr vals) (cdr ws)
                              new-op op))))
     ((expr-denv-ll-related-p string-expr-value-map-ll-related-p) nil)
     (otherwise
      ;; The relation fixes the witnesses before taking them apart.
      (let ((ws (ll-value-witness-list-fix ws)))
        (primop-value-case
         op
         :int-binary-x
         (ll-groundp-ind 'expr-value-ll-related-p
                         (primop-value-int-binary-x->xval new-op)
                         (primop-value-int-binary-x->xval op)
                         (car ws)
                         new-vals vals ws new-op op)
         :int-rel-x
         (ll-groundp-ind 'expr-value-ll-related-p
                         (primop-value-int-rel-x->xval new-op)
                         (primop-value-int-rel-x->xval op)
                         (car ws)
                         new-vals vals ws new-op op)
         :float-binary-x
         (ll-groundp-ind 'expr-value-ll-related-p
                         (primop-value-float-binary-x->xval new-op)
                         (primop-value-float-binary-x->xval op)
                         (car ws)
                         new-vals vals ws new-op op)
         :float-rel-x
         (ll-groundp-ind 'expr-value-ll-related-p
                         (primop-value-float-rel-x->xval new-op)
                         (primop-value-float-rel-x->xval op)
                         (car ws)
                         new-vals vals ws new-op op)
         :bool-binary-x
         (ll-groundp-ind 'expr-value-ll-related-p
                         (primop-value-bool-binary-x->xval new-op)
                         (primop-value-bool-binary-x->xval op)
                         (car ws)
                         new-vals vals ws new-op op)
         :bool-rel-x
         (ll-groundp-ind 'expr-value-ll-related-p
                         (primop-value-bool-rel-x->xval new-op)
                         (primop-value-bool-rel-x->xval op)
                         (car ws)
                         new-vals vals ws new-op op)
         :append-t-m-n-s-x
         (ll-groundp-ind 'expr-value-ll-related-p
                         (primop-value-append-t-m-n-s-x->xval new-op)
                         (primop-value-append-t-m-n-s-x->xval op)
                         (car ws)
                         new-vals vals ws new-op op)
         :index-t-m-x
         (ll-groundp-ind 'expr-value-ll-related-p
                         (primop-value-index-t-m-x->xval new-op)
                         (primop-value-index-t-m-x->xval op)
                         (car ws)
                         new-vals vals ws new-op op)
         :index2d-t-m-n-x
         (ll-groundp-ind 'expr-value-ll-related-p
                         (primop-value-index2d-t-m-n-x->xval new-op)
                         (primop-value-index2d-t-m-n-x->xval op)
                         (car ws)
                         new-vals vals ws new-op op)
         :reduce-t-d-s-f
         (ll-groundp-ind 'expr-value-ll-related-p
                         (primop-value-reduce-t-d-s-f->fval new-op)
                         (primop-value-reduce-t-d-s-f->fval op)
                         (car ws)
                         new-vals vals ws new-op op)
         :fold-t-t2-d-s-s2-f
         (ll-groundp-ind 'expr-value-ll-related-p
                         (primop-value-fold-t-t2-d-s-s2-f->fval new-op)
                         (primop-value-fold-t-t2-d-s-s2-f->fval op)
                         (car ws)
                         new-vals vals ws new-op op)
         :trace-t-r-s-q-x
         (ll-groundp-ind 'expr-value-ll-related-p
                         (primop-value-trace-t-r-s-q-x->xval new-op)
                         (primop-value-trace-t-r-s-q-x->xval op)
                         (car ws)
                         new-vals vals ws new-op op)
         :fold-t-t2-d-s-s2-f-z
         (list
          (ll-groundp-ind 'expr-value-ll-related-p
                          (primop-value-fold-t-t2-d-s-s2-f-z->fval new-op)
                          (primop-value-fold-t-t2-d-s-s2-f-z->fval op)
                          (car ws)
                          new-vals vals ws new-op op)
          (ll-groundp-ind 'expr-value-ll-related-p
                          (primop-value-fold-t-t2-d-s-s2-f-z->zval new-op)
                          (primop-value-fold-t-t2-d-s-s2-f-z->zval op)
                          (cadr ws)
                          new-vals vals ws new-op op))
         :otherwise nil))))))

(defret-mutual expr-value-ll-related-p-when-groundp
  (defret expr-value-ll-related-p-when-groundp
    (implies (and yes/no
                  (expr-value-groundp val))
             (equal (expr-value-fix new-val) (expr-value-fix val)))
    :fn expr-value-ll-related-p)
  (defret expr-value-list-ll-related-p-when-groundp
    (implies (and yes/no
                  (expr-value-list-groundp vals))
             (equal (expr-value-list-fix new-vals)
                    (expr-value-list-fix vals)))
    :fn expr-value-list-ll-related-p)
  (defret primop-value-ll-related-p-when-groundp
    (implies (and yes/no
                  (primop-value-groundp op))
             (equal (primop-value-fix new-op) (primop-value-fix op)))
    :fn primop-value-ll-related-p)
  :mutual-recursion expr-value-ll-related-p
  ;; The map and environment members of the clique are skipped: they are
  ;; reached only through lambda values, which are never ground.
  :skip-others t
  ;; The primitive-operation case reconstructs both values from their
  ;; fields (the FIX-WHEN rules, disabled by default), which the OF-FIELDS
  ;; rules would immediately undo, so those are disabled here.
  :hints (("Goal"
           :induct (ll-groundp-ind flag new-val val w new-vals vals ws
                                   new-op op)
           :expand ((expr-value-ll-related-p new-val val w genv)
                    (expr-value-list-ll-related-p new-vals vals ws genv)
                    (primop-value-ll-related-p new-op op ws genv)
                    (expr-value-groundp val)
                    (expr-value-list-groundp vals)
                    (primop-value-groundp op))
           :in-theory (e/d (equal-of-expr-value-fix-when-both-base
                            equal-of-expr-value-fix-when-both-primop
                            equal-of-expr-value-fix-when-both-box
                            equal-of-expr-value-fix-when-both-vector
                            equal-of-expr-value-fix-when-both-vector-empty
                            expr-value-list-fix$inline
                            primop-value-fix-when-int-unary
                            primop-value-fix-when-int-binary
                            primop-value-fix-when-int-binary-x
                            primop-value-fix-when-int-rel
                            primop-value-fix-when-int-rel-x
                            primop-value-fix-when-int-to-float
                            primop-value-fix-when-int-to-bool
                            primop-value-fix-when-float-unary
                            primop-value-fix-when-float-binary
                            primop-value-fix-when-float-binary-x
                            primop-value-fix-when-float-rel
                            primop-value-fix-when-float-rel-x
                            primop-value-fix-when-float-truncate
                            primop-value-fix-when-float-round
                            primop-value-fix-when-float-ceiling
                            primop-value-fix-when-float-floor
                            primop-value-fix-when-bool-unary
                            primop-value-fix-when-bool-binary
                            primop-value-fix-when-bool-binary-x
                            primop-value-fix-when-bool-rel
                            primop-value-fix-when-bool-rel-x
                            primop-value-fix-when-bool-to-int
                            primop-value-fix-when-bool-to-float
                            primop-value-fix-when-head
                            primop-value-fix-when-head-t
                            primop-value-fix-when-head-t-d
                            primop-value-fix-when-head-t-d-s
                            primop-value-fix-when-tail
                            primop-value-fix-when-tail-t
                            primop-value-fix-when-tail-t-d
                            primop-value-fix-when-tail-t-d-s
                            primop-value-fix-when-length
                            primop-value-fix-when-length-t
                            primop-value-fix-when-length-t-d
                            primop-value-fix-when-length-t-d-s
                            primop-value-fix-when-append
                            primop-value-fix-when-append-t
                            primop-value-fix-when-append-t-m
                            primop-value-fix-when-append-t-m-n
                            primop-value-fix-when-append-t-m-n-s
                            primop-value-fix-when-append-t-m-n-s-x
                            primop-value-fix-when-reverse
                            primop-value-fix-when-reverse-t
                            primop-value-fix-when-reverse-t-d
                            primop-value-fix-when-reverse-t-d-s
                            primop-value-fix-when-index
                            primop-value-fix-when-index-t
                            primop-value-fix-when-index-t-m
                            primop-value-fix-when-index-t-m-x
                            primop-value-fix-when-index2d
                            primop-value-fix-when-index2d-t
                            primop-value-fix-when-index2d-t-m
                            primop-value-fix-when-index2d-t-m-n
                            primop-value-fix-when-index2d-t-m-n-x
                            primop-value-fix-when-sum
                            primop-value-fix-when-sum-s
                            primop-value-fix-when-reshape
                            primop-value-fix-when-reshape-t
                            primop-value-fix-when-reshape-t-s1
                            primop-value-fix-when-reshape-t-s1-s2
                            primop-value-fix-when-flatten
                            primop-value-fix-when-flatten-t
                            primop-value-fix-when-flatten-t-m
                            primop-value-fix-when-flatten-t-m-n
                            primop-value-fix-when-flatten-t-m-n-s
                            primop-value-fix-when-transpose2d
                            primop-value-fix-when-transpose2d-t
                            primop-value-fix-when-transpose2d-t-m
                            primop-value-fix-when-transpose2d-t-m-n
                            primop-value-fix-when-iota/static
                            primop-value-fix-when-reduce
                            primop-value-fix-when-reduce-t
                            primop-value-fix-when-reduce-t-d
                            primop-value-fix-when-reduce-t-d-s
                            primop-value-fix-when-reduce-t-d-s-f
                            primop-value-fix-when-fold
                            primop-value-fix-when-fold-t
                            primop-value-fix-when-fold-t-t2
                            primop-value-fix-when-fold-t-t2-d
                            primop-value-fix-when-fold-t-t2-d-s
                            primop-value-fix-when-fold-t-t2-d-s-s2
                            primop-value-fix-when-fold-t-t2-d-s-s2-f
                            primop-value-fix-when-fold-t-t2-d-s-s2-f-z
                            primop-value-fix-when-reify-dim
                            primop-value-fix-when-reify-shape
                            primop-value-fix-when-iota
                            primop-value-fix-when-iota-d
                            primop-value-fix-when-trace
                            primop-value-fix-when-trace-t
                            primop-value-fix-when-trace-t-r
                            primop-value-fix-when-trace-t-r-s
                            primop-value-fix-when-trace-t-r-s-q
                            primop-value-fix-when-trace-t-r-s-q-x
                            primop-value-fix-when-undefined
                            primop-value-fix-when-undefined-t)
                           (expr-value-ll-related-p
                            expr-value-list-ll-related-p
                            primop-value-ll-related-p
                            primop-value-int-unary-of-fields
                            primop-value-int-binary-of-fields
                            primop-value-int-binary-x-of-fields
                            primop-value-int-rel-of-fields
                            primop-value-int-rel-x-of-fields
                            primop-value-float-unary-of-fields
                            primop-value-float-binary-of-fields
                            primop-value-float-binary-x-of-fields
                            primop-value-float-rel-of-fields
                            primop-value-float-rel-x-of-fields
                            primop-value-bool-unary-of-fields
                            primop-value-bool-binary-of-fields
                            primop-value-bool-binary-x-of-fields
                            primop-value-bool-rel-of-fields
                            primop-value-bool-rel-x-of-fields
                            primop-value-head-t-of-fields
                            primop-value-head-t-d-of-fields
                            primop-value-head-t-d-s-of-fields
                            primop-value-tail-t-of-fields
                            primop-value-tail-t-d-of-fields
                            primop-value-tail-t-d-s-of-fields
                            primop-value-length-t-of-fields
                            primop-value-length-t-d-of-fields
                            primop-value-length-t-d-s-of-fields
                            primop-value-append-t-of-fields
                            primop-value-append-t-m-of-fields
                            primop-value-append-t-m-n-of-fields
                            primop-value-append-t-m-n-s-of-fields
                            primop-value-append-t-m-n-s-x-of-fields
                            primop-value-reverse-t-of-fields
                            primop-value-reverse-t-d-of-fields
                            primop-value-reverse-t-d-s-of-fields
                            primop-value-index-t-of-fields
                            primop-value-index-t-m-of-fields
                            primop-value-index-t-m-x-of-fields
                            primop-value-index2d-t-of-fields
                            primop-value-index2d-t-m-of-fields
                            primop-value-index2d-t-m-n-of-fields
                            primop-value-index2d-t-m-n-x-of-fields
                            primop-value-sum-s-of-fields
                            primop-value-reshape-t-of-fields
                            primop-value-reshape-t-s1-of-fields
                            primop-value-reshape-t-s1-s2-of-fields
                            primop-value-flatten-t-of-fields
                            primop-value-flatten-t-m-of-fields
                            primop-value-flatten-t-m-n-of-fields
                            primop-value-flatten-t-m-n-s-of-fields
                            primop-value-transpose2d-t-of-fields
                            primop-value-transpose2d-t-m-of-fields
                            primop-value-transpose2d-t-m-n-of-fields
                            primop-value-reduce-t-of-fields
                            primop-value-reduce-t-d-of-fields
                            primop-value-reduce-t-d-s-of-fields
                            primop-value-reduce-t-d-s-f-of-fields
                            primop-value-fold-t-of-fields
                            primop-value-fold-t-t2-of-fields
                            primop-value-fold-t-t2-d-of-fields
                            primop-value-fold-t-t2-d-s-of-fields
                            primop-value-fold-t-t2-d-s-s2-of-fields
                            primop-value-fold-t-t2-d-s-s2-f-of-fields
                            primop-value-fold-t-t2-d-s-s2-f-z-of-fields
                            primop-value-iota-d-of-fields
                            primop-value-trace-t-of-fields
                            primop-value-trace-t-r-of-fields
                            primop-value-trace-t-r-s-of-fields
                            primop-value-trace-t-r-s-q-of-fields
                            primop-value-trace-t-r-s-q-x-of-fields
                            primop-value-undefined-t-of-fields)))))

(defruled equal-when-expr-value-ll-related-p-groundp
  (implies (and (expr-value-ll-related-p new-val val w genv)
                (expr-value-groundp val))
           (equal (expr-value-fix new-val) (expr-value-fix val)))
  :use expr-value-ll-related-p-when-groundp
  :disable expr-value-ll-related-p-when-groundp)
