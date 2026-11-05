; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-trees")
(include-book "all-variable-operations")
(include-book "static-environments")
(include-book "type-environments")
(include-book "type-evaluation")
(include-book "abstract-syntax-well-formedness")
(include-book "free-variable-operations")
(include-book "fresh-variable-operations")
(include-book "lists")
(include-book "omaps")
(include-book "osets")
(include-book "kestrel/fty/string-set" :dir :system)
(include-book "utility-transforms")
(include-book "unique-names-files")

(include-book "std/basic/two-nats-measure" :dir :system)

(include-book "portcullis")

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/len" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lambda-lifting
  :parents (remora)
  :short "Lambda lifting."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lambda lifting replaces a lambda that occurs in the middle of an
     expression by a reference to a definition of it, so that the lambdas
     that remain are the ones bound by definitions.  A lambda that uses
     variables bound outside itself cannot simply be moved, so the
     transformation first abstracts over those variables --- they become
     parameters of the definition --- and then passes them back at the point
     the lambda used to be.")
   (xdoc::p
    "For example, the lambda in")
   (xdoc::@{}
    "(let ((x 1)) (f (lambda (y) (+ x y))))")
   (xdoc::p
    "is open in @('x'), so it lifts to a definition whose parameters are
     @('x') and then the lambda's own @('y'), and the occurrence becomes
     that definition applied to @('x') --- a partial application, which is
     the function of @('y') the lambda was:")
   (xdoc::@{}
    "(let ((lifted (fun (x y) (+ x y))))
       (let ((x 1)) (f (lifted x))))")
   (xdoc::p
    "The definition contains no lambda.  A lambda whose whole body is
     another lambda is flattened into it, so a chain of them yields one
     definition with all their parameters.  This is the flat form of
     [impl]'s @('LambdaLift'); as there, captured variables come first.
     The definition has the result type of the lambda.  A lambda annotated
     with a result type is not flattened into, though (each inner lambda is
     lifted on its own): the value of such a lambda carries that type,
     which the curried value of the flattened definition would not.")
   (xdoc::p
    (xdoc::b "What is lifted."))
   (xdoc::p
    "A lambda is lifted when it occurs as an expression, i.e. under @(tsee
     expr-atom), and is closed in type and ispace variables, and so are the
     types of the variables it captures.  Two restrictions follow from
     that.")
   (xdoc::p
    "A lambda inside an array literal is not lifted: an array holds atoms,
     and the reference that would replace the lambda is an expression, so
     there is nowhere to put it.  A lambda that is open in a type or ispace
     variable is not lifted either: abstracting over those would make the
     definition a @(':cfun') or @(':ifun') rather than a @(':fun'), which is
     the business of @(see monomorphize).  Nor is one that captures a
     variable whose type is open in one, e.g. a parameter of type @('&t')
     of an enclosing lambda under a @('t-fn') binding @('&t'): the captured
     variable becomes a parameter of the definition, typed as the
     environment types it, and the definition is outside that binder.  Nor
     is one that captures a variable the environment does not type, such as
     the variable of an unboxing: the parameter it would become would be
     untyped, and evaluating the definition would fail.  All of these are
     left in place, so the transformation is always defined, and its result
     may still contain lambdas of those kinds.")
   (xdoc::p
    "Every lambda in expression position is lifted, including one that is
     already the right-hand side of a binding, which merely gains a level of
     indirection.")
   (xdoc::p
    (xdoc::b "Local functions."))
   (xdoc::p
    "A function bound by a @(':let') is hoisted too, in the same way ---
     the variables it captures become leading parameters, and its uses
     become the definition applied to them --- so that after lifting the
     functions are the top-level ones.  This is [impl]'s
     @('liftLocalFun'), with its condition: a local function is hoisted
     only if none of the variables it captures is a function, and stays
     local otherwise.  ([impl] errors when both functions and values are
     captured; that case stays local here, which is always sound.)  A
     @(':fun') with no parameters stays local as well: it is a value
     binding, whose body is evaluated where it is bound, and hoisting it
     would change when that happens.  So does a function that is open in a
     type or ispace variable, or captures a variable whose type is, or one
     that the environment does not type, as for lambdas.  A @(':let') all of whose bindings are hoisted disappears.")
   (xdoc::p
    "The guards of @(tsee lambda-lift-top-expr) and @(tsee lambda-lift-file)
     require the binders of the input to bind distinct names (see @(tsee
     expr-duplicate-names) and @(tsee file-duplicate-names)), as @(tsee
     expr-uniquify-names) and @(tsee file-uniquify-names) make them.  The
     transformation does not rely on that, though: replacing the uses of a
     hoisted function respects shadowing, in two ways.  A binder of the
     function's own name hides it, so the uses of that name under the
     binder are not replaced.  And the replacement passes the captured
     variables at each use, where they must still mean what they meant at
     the binding; so a function is hoisted only if none of the variables it
     captures is bound again in its scope, and stays local otherwise.")
   (xdoc::p
    (xdoc::b "Names."))
   (xdoc::p
    "The definitions are named by @(tsee fresh-expr-var) from a set of names
     to avoid, which starts as every variable occurring anywhere in the
     input --- not just the free ones, since a lifted definition is placed
     outside all of the input's binders --- and grows as names are used.  So
     no lifted definition captures, or is captured by, a variable of the
     input.")
   (xdoc::p
    (xdoc::b "Where the definitions go."))
   (xdoc::p
    "@(tsee lambda-lift-top-expr) wraps them around the expression in a
     @(':let'), outermost first.  @(tsee lambda-lift-file) turns them into
     declarations and puts the ones lifted out of each declaration right
     before it: the declarations of a file are scoped sequentially, and a
     lifted definition may refer to the declarations before its own, which
     are not local, so not captured."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Small conversions between the sets the variable operations return and the
; lists the AST constructors take.

; A set of strings is already a list of them, in the set's order, so the
; free variables can be used directly as a parameter and argument list.

(local (in-theory (enable acl2::string-listp-when-string-setp)))

; The nodes whose fixtype constrains the length of a list component are
; rebuilt from the pointwise traversal of that component, so the guard
; proofs need the length theorems of the list traversals in the CONSP form
; the goals arise in.

(local (in-theory (enable consp-when-positive-len positive-len-when-consp)))

; The names bound again in the scope of a :LET binding are gathered from
; the later bindings and the body by APPEND.

(local
 (defrule string-listp-of-append-local
   (implies (and (string-listp x)
                 (string-listp y))
            (string-listp (append x y)))
   :induct (len x)
   :enable (append string-listp len)))

(define names-to-exprs ((names string-listp))
  :returns (exprs expr-listp)
  :short "Turn variable names into variable expressions."
  (if (endp names)
      nil
    (cons (expr-var (str-fix (car names)))
          (names-to-exprs (cdr names))))

  ///

  (defret len-of-names-to-exprs
    (equal (len exprs) (len names))
    :hints (("Goal" :in-theory (enable len)))))

(define apply-to-names ((fun exprp) (names string-listp))
  :returns (e exprp)
  :short "Apply an expression to the given variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "With no variables this is the expression itself; with one it is an
     @(':app'); with two or more an @(':appn'), whose arity constraint is
     met."))
  (cond ((endp names) (expr-fix fun))
        ((endp (cdr names)) (expr-app fun (expr-var (str-fix (car names)))))
        (t (expr-appn fun (names-to-exprs names)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A lambda captures the variables it uses that are bound around it within
; the current declaration --- the local ones.  What is free in it but not
; local (a primitive operation, or a top-level definition) is in scope
; wherever the definition is placed, so it is referred to there, not
; passed.  This is [impl]'s CAPTURED.  The set of local names is kept
; separately from the type environment, which the validator may fail to
; extend: a variable must be captured whether or not its type is known.

; The captured variables are the @(tsee set::intersect) of the free variables
; with the local names; see @(tsee emit-lifted-lambda) and @(tsee
; hoist-local-fun).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A chain of nested lambdas, each the whole body of the previous one, is
; flattened into one definition with all their parameters.  This is the
; step of that: does the body consist of a lambda, and if so of what.

(define nested-lambda ((body exprp))
  :returns (mv (nestedp booleanp)
               (params var+type?-listp)
               (inner exprp)
               (type? type-optionp))
  :short "Whether an expression is a lambda, and if so its parameters, body,
          and result type annotation."
  (b* ((body (expr-fix body))
       ((unless (expr-case body :atom)) (mv nil nil body (type-option-none)))
       (a (expr-atom->atom body)))
    (atom-case a
      :lambda (mv t (list a.param) a.body a.type?)
      :lambdan (mv t a.params a.body a.type?)
      :otherwise (mv nil nil body (type-option-none))))

  ///

  (defret expr-count-of-nested-lambda
    (implies nestedp
             (< (expr-count inner) (expr-count body)))
    :rule-classes :linear))

; A lambda is lifted only if it is closed in type and ispace variables, and
; so are the parameters that the variables it captures become; see
; LAMBDA-LIFTING.

(define captured-params-closed-p ((captured string-setp)
                                  (tenv string-type-mapp))
  :returns (yes/no booleanp)
  :short "Whether the parameters that captured variables become are closed
          in type and ispace variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "A lifted or hoisted definition takes the variables it captures as
     leading parameters, typed as @('tenv') types them (see @(tsee
     names-to-params)).  The definition is placed outside all the binders
     of the declaration, including those of type and ispace variables, so
     those types must not mention any."))
  (b* ((params (names-to-params captured tenv)))
    (and (set::emptyp (var+type?-list-free-type-vars params))
         (set::emptyp (var+type?-list-free-ispace-vars params)))))

; A captured variable becomes a parameter typed as the environment types it,
; and evaluating a lambda value requires the type of its parameter.  So a
; lambda is lifted, or a local function hoisted, only if the environment
; types every variable it captures.  It may not: an unboxed variable, for
; instance, is local but untyped there.

; The application of a lambda checks the dimensions of its argument against
; the type of its parameter, but against the outer dimensions only (see
; EXPR-VALUES-MATCH-TYPE-VALUES-P), while type equivalence unwraps a
; zero-rank array, so that a value may have a nested array type whose outer
; dimensions are not its own.  So a captured variable becomes a parameter
; only if its type is flat: an atom type, or an array type of an atom type.

(define type-evals-to-atom-p ((type typep))
  :returns (yes/no booleanp)
  :short "Whether a type is syntactically an atom type."
  :long
  (xdoc::topstring
   (xdoc::p
    "A function type with no inputs is its output type, which may be an
     array type."))
  (type-case type
             :base t
             :fun t
             :funn (consp type.in)
             :forall t
             :foralln t
             :pi t
             :pin t
             :sigma t
             :sigman t
             :otherwise nil))

(define type-flat-syntax-p ((type typep))
  :returns (yes/no booleanp)
  :short "Whether a type is syntactically flat:
          an atom type, or an array type of an atom type."
  (type-case type
             :var nil
             :scalar (type-evals-to-atom-p type.elem)
             :array (type-evals-to-atom-p type.elem)
             :bracket (type-evals-to-atom-p type.elem)
             :funn (if (consp type.in) t (type-flat-syntax-p type.out))
             :otherwise t)
  :measure (type-count type))

;;;;;;;;;;;;;;;;;;;;

; A lifted or hoisted definition is bound at the top, where its binding is
; evaluated: that evaluates the type of its first parameter and its result
; type (see EVAL-BIND), whether or not the original program ever evaluates
; the lambda or the binding it comes from.  So those types must evaluate
; successfully; they are closed (see CAPTURED-PARAMS-CLOSED-P), so this is
; checked in the empty environment.  (A closed type may fail to evaluate,
; e.g. if a dimension is a subtraction with a negative result.)

(define type-evaluable-p ((type typep))
  :returns (yes/no booleanp)
  :short "Whether a type evaluates successfully in the empty environment."
  (not (reserrp (eval-type type (type-denv (ispace-denv nil) nil)))))

(define type-option-evaluable-p ((type? type-optionp))
  :returns (yes/no booleanp)
  :short "Whether an optional type is absent or evaluates successfully
          in the empty environment."
  (type-option-case type?
                    :none t
                    :some (type-evaluable-p type?.val)))

(define param-evaluable-p ((param var+type?-p))
  :returns (yes/no booleanp)
  :short "Whether a parameter has a type that evaluates successfully
          in the empty environment."
  (b* ((type? (var+type?->type? param)))
    (type-option-case type?
                      :none nil
                      :some (type-evaluable-p type?.val))))

(define captured-params-typed-p ((captured string-setp)
                                 (tenv string-type-mapp))
  :returns (yes/no booleanp)
  :short "Whether the environment types every captured variable,
          with a flat type."
  :long
  (xdoc::topstring
   (xdoc::p
    "A lifted or hoisted definition takes the variables it captures as
     leading parameters, typed as @('tenv') types them (see @(tsee
     names-to-params)); a variable that @('tenv') does not type would
     become an untyped parameter, on which evaluation fails.  The variable
     of an unboxing, for instance, is local but not in @('tenv').  The
     types must be flat (see @(tsee type-flat-syntax-p)), for the
     application that passes the variable to check its dimensions, and
     they must evaluate successfully (see @(tsee type-evaluable-p)), since
     the first of them is evaluated where the definition is bound."))
  (b* (((unless (mbt (string-setp captured))) nil)
       ((when (set::emptyp captured)) t)
       (type? (name-to-type-option (set::head captured) tenv)))
    (and (type-option-case type? :some)
         (type-flat-syntax-p (type-option-some->val type?))
         (type-evaluable-p (type-option-some->val type?))
         (captured-params-typed-p (set::tail captured) tenv)))
  :measure (acl2-count captured))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The lifting step itself, for a lambda whose parameters have been collected
; and whose body has already been lifted out of.  It is not recursive.

(define emit-lifted-lambda ((params var+type?-listp)
                            (body exprp)
                            (type? type-optionp)
                            (tenv string-type-mapp)
                            (locals string-setp)
                            (used string-setp))
  :returns (mv (e exprp) (lifted bind-listp) (new-used string-setp))
  :short "Make the definition of a lambda, and the reference that replaces it."
  :long
  (xdoc::topstring
   (xdoc::p
    "The definition is a @(':fun') under a fresh name whose parameters are
     the variables the lambda captures followed by the lambda's own
     parameters, and whose body is the lambda's body.  So it contains no
     lambda: this is the flat form of lambda lifting, as in [impl]'s
     @('LambdaLift'), where the captured variables become leading
     parameters.  They are the lambda's free variables that are locally
     bound --- the intersection of the free variables with the local
     names --- typed from the environment.")
   (xdoc::p
    "The result type of the definition is that of the lambda,
     @('type?').  It travels with the innermost abstraction of the
     definition's curried value (see @(tsee eval-bind)), which is the one
     over the lambda's last parameter, as it does for the lambda.")
   (xdoc::p
    "The expression returned, which replaces the lambda, is the name
     applied to the captured variables alone.  That is a partial
     application of the definition, which is what the lambda was: a
     function of its own parameters.")
   (xdoc::p
    "The definition is bound at the top, which evaluates the type of its
     first parameter and its result type (see @(tsee type-evaluable-p)),
     and the reference passes the captured variables to its parameters,
     which checks their dimensions (see @(tsee captured-params-typed-p)).
     So the captured variables must have flat types that evaluate, and the
     first parameter and the result type must have types that evaluate.
     Otherwise the lambda is not lifted: what is returned is the lambda
     itself, over the parameters collected and the body lifted out of,
     and no definition."))
  (b* ((params (var+type?-list-fix params))
       (body (expr-fix body))
       (used (string-sfix used))
       (fv (set::intersect
            (set::difference (expr-free-expr-vars body)
                             (set::mergesort (var+type?-list->var params)))
            locals))
       (def-params (append (names-to-params fv tenv) params))
       ((unless (and (consp params)
                     (captured-params-typed-p fv tenv)
                     (param-evaluable-p (car def-params))
                     (type-option-evaluable-p type?)))
        (mv (if (consp params)
                (expr-atom (make-atom-lambda/lambdan params body type?))
              body)
            nil
            used))
       (name (fresh-expr-var "lam_" used))
       (used (set::insert name used))
       (bind (make-bind-fun :var name
                            :params def-params
                            :type? type?
                            :expr body)))
    (mv (apply-to-names (expr-var name) fv) (list bind) used)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lambda-chain-result-type ((body exprp) (type? type-optionp))
  :returns (result-type? type-optionp)
  :short "The result type of the definition a lambda is lifted to."
  :long
  (xdoc::topstring
   (xdoc::p
    "A lambda whose body is a lambda, and which is not annotated, is
     flattened into it (see @(tsee ll-lambda)): the definition has the
     result type of the innermost lambda of the chain."))
  (b* (((mv nestedp & inner inner-type?) (nested-lambda body)))
    (if (and nestedp (type-option-case type? :none))
        (lambda-chain-result-type inner inner-type?)
      (type-option-fix type?)))
  :measure (expr-count body))

(define liftable-lambda-p ((a atomp)
                           (tenv string-type-mapp)
                           (locals string-setp)
                           (lmap string-expr-mapp))
  :returns (yes/no booleanp)
  :short "Whether an atom is a lambda that lifting handles."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variables the lambda captures are the free ones that are local.
     Those are checked here, before the body is lifted out of; afterwards,
     the body may also refer to variables captured by the hoisted functions
     it uses (whose uses are replaced by applications to them), but those
     were checked when the functions were hoisted (see @(tsee
     hoist-local-fun)), and they are not bound again in their scope, so
     they still have the types checked then.")
   (xdoc::p
    "Conversely, a hoisted function the lambda uses is local, but it is not
     captured: its uses are replaced (see @('lmap')).  Its type need not be
     known --- the type checker may well fail on its binding alone, which
     refers to variables bound outside it --- so it is exempt from the check
     that the captured variables are typed.")
   (xdoc::p
    "The type of the lambda's first parameter, and the result type of the
     definition, must evaluate successfully, since they may be evaluated
     where the definition is bound (see @(tsee type-evaluable-p))."))
  (b* ((captured (set::intersect (atom-free-expr-vars a)
                                 (string-sfix locals))))
    (and (atom-case a
                    :lambda (and (param-evaluable-p a.param)
                                 (type-option-evaluable-p
                                  (lambda-chain-result-type a.body a.type?)))
                    :lambdan (and (consp a.params)
                                  (param-evaluable-p (car a.params))
                                  (type-option-evaluable-p
                                   (lambda-chain-result-type a.body a.type?)))
                    :otherwise nil)
         (set::emptyp (atom-free-type-vars a))
         (set::emptyp (atom-free-ispace-vars a))
         (captured-params-typed-p
          (set::difference captured
                           (omap::keys (string-expr-map-fix lmap)))
          tenv)
         (captured-params-closed-p captured tenv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Hoisting of local functions, [impl]'s LIFTLOCALFUN.  A :FUN bound by a
; :LET is hoisted like a lambda --- captured variables prepended, uses
; replaced by the partial application --- provided none of the variables
; it captures is a function.  One that captures a function stays local.
; ([impl] also stays local for that, and errors when both functions and
; values are captured; there is no error channel here, so that case stays
; local too, which is always sound.)  A :FUN with no parameters stays local
; too: it is a value binding (see EVAL-BIND), whose body is evaluated where
; it is bound, so hoisting it would change when that happens.

(define function-type-p ((ty typep))
  :returns (yes/no booleanp)
  :short "Whether a type is a function type, as [impl]'s @('isFunctionType')."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, an arrow, possibly as the element type of an array; the
     validator gives a function variable an array type over an arrow."))
  (b* ((ty (type-fix ty))
       (elem (type-case ty :array ty.elem :otherwise ty)))
    (or (type-case elem :fun)
        (type-case elem :funn))))

(define captures-function-p ((vars string-setp) (tenv string-type-mapp))
  :returns (yes/no booleanp)
  :short "Whether any of the variables has a function type."
  (b* (((unless (mbt (string-setp vars))) nil)
       ((when (set::emptyp vars)) nil)
       (type? (name-to-type-option (set::head vars) tenv)))
    (or (and (type-option-case type? :some)
             (function-type-p (type-option-some->val type?)))
        (captures-function-p (set::tail vars) tenv)))
  :measure (acl2-count vars))

(define hoist-local-fun ((b bindp)
                         (rebound string-listp)
                         (tenv string-type-mapp)
                         (locals string-setp)
                         (used string-setp))
  :returns (mv (hoistedp booleanp)
               (var stringp)
               (hoisted bindp)
               (replacement exprp)
               (new-used string-setp))
  :short "Hoist a local function binding, if it captures no function,
          no variable that is bound again in its scope,
          and no variable whose type is open."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given a binding whose body has already been lifted out of, the names
     @('rebound') bound by the binders in the scope of the binding, and the
     environment outside it: if it is a @(':fun') with at least one
     parameter, closed in type and ispace variables, whose captured
     variables are not functions, are not in @('rebound'), and have types,
     closed in type and ispace variables (see @(tsee
     captured-params-typed-p) and @(tsee captured-params-closed-p)), the
     result is @('t'), its variable, a
     definition of it under a fresh name with the captured variables as
     leading parameters, and the expression --- that name applied to the
     captured variables --- that replaces its uses.  Otherwise the result
     is @('nil') and the binding itself.")
   (xdoc::p
    "A @(':fun') with no parameters is a value binding: its body is
     evaluated where it is bound (see @(tsee eval-bind)).  Hoisted, its body
     would be evaluated at the top level if nothing is captured, and at each
     use otherwise; either way an error in it could appear or disappear.")
   (xdoc::p
    "The replacement passes the captured variables at each use, so a
     captured variable in @('rebound') might mean something else there than
     at the binding."))
  (b* ((b (bind-fix b))
       (used (string-sfix used))
       ((unless (bind-case b :fun)) (mv nil "" b (expr-var "") used))
       ((bind-fun b) b)
       ((unless (and (consp b.params)
                     (param-evaluable-p (car b.params))
                     (type-option-evaluable-p b.type?)
                     (set::emptyp (bind-free-type-vars b))
                     (set::emptyp (bind-free-ispace-vars b))))
        (mv nil b.var b (expr-var b.var) used))
       (fv (set::intersect (bind-free-expr-vars b) locals))
       ((when (or (captures-function-p fv tenv)
                  (intersectp-equal fv (str::string-list-fix rebound))
                  (not (captured-params-typed-p fv tenv))
                  (not (captured-params-closed-p fv tenv))))
        (mv nil b.var b (expr-var b.var) used))
       (name (fresh-expr-var b.var used))
       (used (set::insert name used))
       (hoisted (make-bind-fun :var name
                               :params (append (names-to-params fv tenv) b.params)
                               :type? b.type?
                               :expr b.expr)))
    (mv t b.var hoisted (apply-to-names (expr-var name) fv) used)))

(define locals-with-params ((params var+type?-listp) (locals string-setp))
  :returns (new-locals string-setp)
  :short "Add the names of parameters to the local names."
  (set::union (set::mergesort (var+type?-list->var params))
              (string-sfix locals)))

; A binder of an expression variable hides the hoisted local function of
; that name, if any: the variable's uses under the binder are not replaced.

(define string-expr-map-remove-keys ((keys string-listp)
                                     (map string-expr-mapp))
  :returns (new-map string-expr-mapp)
  :short "Remove some keys from a map from strings to expressions."
  (if (endp keys)
      (string-expr-map-fix map)
    (string-expr-map-remove-keys
     (cdr keys)
     (omap::delete (str-fix (car keys)) (string-expr-map-fix map))))

  ///

  (defret assoc-of-string-expr-map-remove-keys
    (equal (omap::assoc key new-map)
           (if (member-equal key (str::string-list-fix keys))
               nil
             (omap::assoc key (string-expr-map-fix map))))
    :hints (("Goal"
             :induct t
             :in-theory (enable str::string-list-fix omap::assoc-of-delete)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The types of the variables bound by a :LET are inferred by the type
; checker (see EXTEND-TENV-WITH-BINDS), but only from the types of other
; such variables: a binding is checked only if every local variable it
; refers to is one whose type was inferred so, and the types inferred are
; kept only if they are closed.  The set TLETS of those variables travels
; with the type environment.
;
; The reason is the validation of lambda lifting (see
; LAMBDA-LIFTING-VALIDATION), which relies on the soundness of the type
; checker: a captured variable's value must have the shape of its type.  For
; a parameter that is checked by the application that binds it.  For a
; variable bound by a :LET it follows from the soundness of the checker for
; the binding, provided the variables the binding refers to have values of
; their types --- which is known of variables bound by :LETs in this way,
; but not of parameters, whose values are checked for their shapes only.

(define tlets-without ((names string-listp) (tlets string-setp))
  :returns (new-tlets string-setp)
  :short "Remove some names from the set of variables with inferred types."
  (set::difference (string-sfix tlets)
                   (set::mergesort (str::string-list-fix names))))

(define type-map-all-closed-p ((tmap string-type-mapp))
  :returns (yes/no booleanp)
  :short "Whether all the types in a map are closed
          in type and ispace variables."
  (b* ((tmap (string-type-map-fix tmap))
       ((when (omap::emptyp tmap)) t)
       (type (omap::head-val tmap)))
    (and (set::emptyp (type-free-type-vars type))
         (set::emptyp (type-free-ispace-vars type))
         (type-map-all-closed-p (omap::tail tmap))))
  :measure (acl2-count (string-type-map-fix tmap)))

(local
 (defrule string-setp-of-keys-when-string-type-mapp
   (implies (string-type-mapp m)
            (string-setp (omap::keys m)))
   :induct (omap::keys m)
   :enable (omap::keys string-type-mapp)))

(define extend-tenv-with-let-bind ((b bindp)
                                   (tenv string-type-mapp)
                                   (tlets string-setp)
                                   (locals string-setp))
  :returns (mv (new-tenv string-type-mapp)
               (new-tlets string-setp))
  :short "Record the types of the variables a binding of a @(':let') binds."
  :long
  (xdoc::topstring
   (xdoc::p
    "The binding is checked by the type checker, as in @(tsee
     extend-tenv-with-binds), but only if the local variables it refers to
     are all in @('tlets'), and only with their types (over the primitive
     operations).  The types inferred for the variables it binds are kept
     if they are well formed and closed, and those variables are then in
     @('tlets'); otherwise they are not."))
  (b* ((b (bind-fix b))
       (tenv (string-type-map-fix tenv))
       (tlets (string-sfix tlets))
       (vars (bind-bound-expr-vars b))
       (others (set::difference tlets vars))
       (free-locals (set::intersect (bind-free-expr-vars b)
                                    (string-sfix locals)))
       ((unless (set::subset free-locals tlets)) (mv tenv others))
       (scope (restrict-to-keys free-locals tenv))
       (sbs (check-bind-list (list b)
                             (init-ispace-senv)
                             (init-type-senv)
                             (tenv-to-expr-senv scope)))
       ((when (reserrp sbs)) (mv tenv others))
       (new (restrict-to-keys vars (expr-senv->exprs (senvs+binds->eenv sbs))))
       ((unless (and (type-map-all-wfp new)
                     (type-map-all-closed-p new)))
        (mv tenv others)))
    (mv (omap::update* new tenv)
        (set::union (omap::keys new) others)))
  :guard-hints
  (("Goal" :in-theory (enable senvs+binds-p-when-result-not-error))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines lambda-lift-exprs/atoms/binds
  :short "Lift the lambdas out of expressions, atoms, and bindings,
          and hoist the local functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides the node, each function takes the type environment @('tenv'),
     the set @('tlets') of the variables in it whose types were inferred
     from their @(':let') bindings (see @(tsee extend-tenv-with-let-bind)),
     the set of local names @('locals') of the variables bound around
     the node within the declaration, the map @('lmap') from the hoisted
     local functions in scope to the expressions that replace their uses,
     and the set @('used') of names in use.  The first three are scoped ---
     in particular, a binder of an expression variable removes the variable
     from @('lmap') --- and the last is threaded.  Each returns the rebuilt
     node, the definitions lifted out of it, and the names in use."))

  (define ll-expr ((x exprp)
                   (tenv string-type-mapp)
                   (tlets string-setp)
                   (locals string-setp)
                   (lmap string-expr-mapp)
                   (used string-setp))
    :returns (mv (new-x exprp) (lifted bind-listp) (new-used string-setp))
    (expr-case x
      :var (b* ((pair (omap::assoc x.name (string-expr-map-fix lmap))))
             (mv (if pair (expr-fix (cdr pair)) (expr-fix x))
                 nil
                 (string-sfix used)))
      :atom (b* ((a x.atom)
                 ((when (liftable-lambda-p a tenv locals lmap))
                  (atom-case a
                    :lambda (ll-lambda (list a.param) a.body a.type?
                                       tenv tlets locals lmap used)
                    :lambdan (ll-lambda a.params a.body a.type?
                                        tenv tlets locals lmap used)
                    :otherwise (mv (expr-fix x) nil (string-sfix used))))
                 ((mv new-a lifted used) (ll-atom a tenv tlets locals lmap used)))
              (mv (expr-atom new-a) lifted used))
      :array (b* (((mv new-as lifted used)
                   (ll-atom-list x.atoms tenv tlets locals lmap used)))
               (mv (expr-array x.dims new-as) lifted used))
      :frame (b* (((mv new-es lifted used)
                   (ll-expr-list x.exprs tenv tlets locals lmap used)))
               (mv (expr-frame x.dims new-es) lifted used))
      :app (b* (((mv new-f lifted1 used) (ll-expr x.fun tenv tlets locals lmap used))
                ((mv new-a lifted2 used) (ll-expr x.arg tenv tlets locals lmap used)))
             (mv (expr-app new-f new-a) (append lifted1 lifted2) used))
      :appn (b* (((mv new-f lifted1 used) (ll-expr x.fun tenv tlets locals lmap used))
                 ((mv new-as lifted2 used)
                  (ll-expr-list x.args tenv tlets locals lmap used)))
              (mv (expr-appn new-f new-as) (append lifted1 lifted2) used))
      :tapp (b* (((mv new-f lifted used) (ll-expr x.fun tenv tlets locals lmap used)))
              (mv (expr-tapp new-f x.arg) lifted used))
      :tappn (b* (((mv new-f lifted used) (ll-expr x.fun tenv tlets locals lmap used)))
               (mv (expr-tappn new-f x.args) lifted used))
      :iapp (b* (((mv new-f lifted used) (ll-expr x.fun tenv tlets locals lmap used)))
              (mv (expr-iapp new-f x.arg) lifted used))
      :iappn (b* (((mv new-f lifted used) (ll-expr x.fun tenv tlets locals lmap used)))
               (mv (expr-iappn new-f x.args) lifted used))
      :capp (b* (((mv new-f lifted1 used) (ll-expr x.fun tenv tlets locals lmap used))
                 ((mv new-as lifted2 used)
                  (ll-expr-list x.args tenv tlets locals lmap used)))
              (mv (expr-capp new-f x.targs x.iargs new-as)
                  (append lifted1 lifted2) used))
      :unbox (b* ((body-tlets (tlets-without (list x.var) tlets))
                  (body-locals (set::insert x.var (string-sfix locals)))
                  (body-lmap (string-expr-map-remove-keys (list x.var) lmap))
                  ((mv new-t lifted1 used)
                   (ll-expr x.target tenv tlets locals lmap used))
                  ((mv new-b lifted2 used)
                   (ll-expr x.body tenv body-tlets body-locals body-lmap used)))
               (mv (expr-unbox x.ispace x.var new-t new-b x.type?)
                   (append lifted1 lifted2) used))
      :unboxn (b* ((body-tlets (tlets-without (list x.var) tlets))
                   (body-locals (set::insert x.var (string-sfix locals)))
                   (body-lmap (string-expr-map-remove-keys (list x.var) lmap))
                   ((mv new-t lifted1 used)
                    (ll-expr x.target tenv tlets locals lmap used))
                   ((mv new-b lifted2 used)
                    (ll-expr x.body tenv body-tlets body-locals body-lmap used)))
                (mv (expr-unboxn x.ispaces x.var new-t new-b x.type?)
                    (append lifted1 lifted2) used))
      :bracket (b* (((mv new-es lifted used)
                     (ll-expr-list x.exprs tenv tlets locals lmap used)))
                 (mv (expr-bracket new-es) lifted used))
      :let (b* (((mv kept lifted1 tenv locals lmap used tlets)
                 (ll-let-binds x.binds (expr-expr-var-binders x.body)
                               tenv tlets locals lmap used))
                ((mv new-b lifted2 used) (ll-expr x.body tenv tlets locals lmap used)))
             ;; a :LET all of whose bindings were hoisted is just its body
             (mv (if (consp kept) (expr-let kept new-b) new-b)
                 (append lifted1 lifted2)
                 used))
      :otherwise (mv (expr-fix x) nil (string-sfix used)))
    :measure (two-nats-measure (expr-count x) 0))

  ; A lambda, with the parameters collected so far and its result type
  ; annotation.  A body that is itself a lambda is absorbed into the
  ; parameter list rather than lifted on its own, so that a chain of lambdas
  ; yields one definition --- but only if the lambda is not annotated: the
  ; value of an annotated lambda carries its result type (see EVAL-ATOM),
  ; and the value of the definition, applied to the same parameters, would
  ; not, since the definition's result type is the inner one.
  (define ll-lambda ((params var+type?-listp)
                     (body exprp)
                     (type? type-optionp)
                     (tenv string-type-mapp)
                     (tlets string-setp)
                     (locals string-setp)
                     (lmap string-expr-mapp)
                     (used string-setp))
    :returns (mv (e exprp) (lifted bind-listp) (new-used string-setp))
    (b* ((params (var+type?-list-fix params))
         (tenv (extend-tenv-with-params params tenv))
         (tlets (tlets-without (var+type?-list->var params) tlets))
         (locals (locals-with-params params locals))
         (lmap (string-expr-map-remove-keys (var+type?-list->var params) lmap))
         ((mv nestedp more-params inner inner-type?) (nested-lambda body))
         ((when (and nestedp (type-option-case type? :none)))
          (ll-lambda (append params more-params) inner inner-type?
                     tenv tlets locals lmap used))
         ((mv new-body lifted used) (ll-expr body tenv tlets locals lmap used))
         ;; the definitions lifted out of the body go before this one,
         ;; which refers to them
         ((mv e more used)
          (emit-lifted-lambda params new-body type? tenv locals used)))
      (mv e (append lifted more) used))
    :measure (two-nats-measure (expr-count body) 1))

  (define ll-expr-list ((x expr-listp)
                        (tenv string-type-mapp)
                        (tlets string-setp)
                        (locals string-setp)
                        (lmap string-expr-mapp)
                        (used string-setp))
    :returns (mv (new-x (and (expr-listp new-x)
                             (equal (len new-x) (len x))))
                 (lifted bind-listp)
                 (new-used string-setp))
    (b* (((when (endp x)) (mv nil nil (string-sfix used)))
         ((mv new-e lifted1 used) (ll-expr (car x) tenv tlets locals lmap used))
         ((mv new-es lifted2 used) (ll-expr-list (cdr x) tenv tlets locals lmap used)))
      (mv (cons new-e new-es) (append lifted1 lifted2) used))
    :measure (two-nats-measure (expr-list-count x) 0))

  (define ll-atom ((x atomp)
                   (tenv string-type-mapp)
                   (tlets string-setp)
                   (locals string-setp)
                   (lmap string-expr-mapp)
                   (used string-setp))
    :returns (mv (new-x atomp) (lifted bind-listp) (new-used string-setp))
    (atom-case x
      :lambda (b* ((body-tenv (extend-tenv-with-params (list x.param) tenv))
                   (body-tlets (tlets-without (list (var+type?->var x.param))
                                              tlets))
                   (body-locals (locals-with-params (list x.param) locals))
                   (body-lmap (string-expr-map-remove-keys
                               (list (var+type?->var x.param))
                               lmap))
                   ((mv new-b lifted used)
                    (ll-expr x.body body-tenv body-tlets body-locals body-lmap used)))
                (mv (atom-lambda x.param new-b x.type?) lifted used))
      :lambdan (b* ((body-tenv (extend-tenv-with-params x.params tenv))
                    (body-tlets (tlets-without (var+type?-list->var x.params)
                                               tlets))
                    (body-locals (locals-with-params x.params locals))
                    (body-lmap (string-expr-map-remove-keys
                                (var+type?-list->var x.params)
                                lmap))
                    ((mv new-b lifted used)
                     (ll-expr x.body body-tenv body-tlets body-locals body-lmap used)))
                 (mv (atom-lambdan x.params new-b x.type?) lifted used))
      :tlambda (b* (((mv new-b lifted used) (ll-expr x.body tenv tlets locals lmap used)))
                 (mv (atom-tlambda x.param new-b) lifted used))
      :tlambdan (b* (((mv new-b lifted used) (ll-expr x.body tenv tlets locals lmap used)))
                  (mv (atom-tlambdan x.params new-b) lifted used))
      :ilambda (b* (((mv new-b lifted used) (ll-expr x.body tenv tlets locals lmap used)))
                 (mv (atom-ilambda x.param new-b) lifted used))
      :ilambdan (b* (((mv new-b lifted used) (ll-expr x.body tenv tlets locals lmap used)))
                  (mv (atom-ilambdan x.params new-b) lifted used))
      :box (b* (((mv new-a lifted used) (ll-expr x.array tenv tlets locals lmap used)))
             (mv (atom-box x.ispace new-a x.type?) lifted used))
      :boxn (b* (((mv new-a lifted used) (ll-expr x.array tenv tlets locals lmap used)))
              (mv (atom-boxn x.ispaces new-a x.type?) lifted used))
      :otherwise (mv (atom-fix x) nil (string-sfix used)))
    :measure (two-nats-measure (atom-count x) 0))

  (define ll-atom-list ((x atom-listp)
                        (tenv string-type-mapp)
                        (tlets string-setp)
                        (locals string-setp)
                        (lmap string-expr-mapp)
                        (used string-setp))
    :returns (mv (new-x (and (atom-listp new-x)
                             (equal (len new-x) (len x))))
                 (lifted bind-listp)
                 (new-used string-setp))
    (b* (((when (endp x)) (mv nil nil (string-sfix used)))
         ((mv new-a lifted1 used) (ll-atom (car x) tenv tlets locals lmap used))
         ((mv new-as lifted2 used) (ll-atom-list (cdr x) tenv tlets locals lmap used)))
      (mv (cons new-a new-as) (append lifted1 lifted2) used))
    :measure (two-nats-measure (atom-list-count x) 0))

  (define ll-bind ((x bindp)
                   (tenv string-type-mapp)
                   (tlets string-setp)
                   (locals string-setp)
                   (lmap string-expr-mapp)
                   (used string-setp))
    :returns (mv (new-x bindp) (lifted bind-listp) (new-used string-setp))
    (bind-case x
      :val (b* (((mv new-e lifted used) (ll-expr x.expr tenv tlets locals lmap used)))
             (mv (bind-val x.var x.type? new-e) lifted used))
      :fun (b* ((body-tenv (extend-tenv-with-params x.params tenv))
                (body-tlets (tlets-without (var+type?-list->var x.params)
                                           tlets))
                (body-locals (locals-with-params x.params locals))
                (body-lmap (string-expr-map-remove-keys
                            (var+type?-list->var x.params)
                            lmap))
                ((mv new-e lifted used)
                 (ll-expr x.expr body-tenv body-tlets body-locals body-lmap used)))
             (mv (bind-fun x.var x.params x.type? new-e) lifted used))
      :tfun (b* (((mv new-e lifted used) (ll-expr x.expr tenv tlets locals lmap used)))
              (mv (bind-tfun x.var x.params x.type? new-e) lifted used))
      :ifun (b* (((mv new-e lifted used) (ll-expr x.expr tenv tlets locals lmap used)))
              (mv (bind-ifun x.var x.params x.type? new-e) lifted used))
      :cfun (b* ((body-tenv (extend-tenv-with-params x.params tenv))
                 (body-tlets (tlets-without (var+type?-list->var x.params)
                                            tlets))
                 (body-locals (locals-with-params x.params locals))
                 (body-lmap (string-expr-map-remove-keys
                             (var+type?-list->var x.params)
                             lmap))
                 ((mv new-e lifted used)
                  (ll-expr x.expr body-tenv body-tlets body-locals body-lmap used)))
              (mv (bind-cfun x.var x.tparams? x.iparams? x.params x.type new-e)
                  lifted used))
      :otherwise (mv (bind-fix x) nil (string-sfix used)))
    :measure (two-nats-measure (bind-count x) 0))

  ; The bindings of a :LET, in order.  Each is lifted out of, and then
  ; either hoisted --- recorded in LMAP, and not kept --- or kept, which
  ; hides any hoisted function of its name.  BODY-BINDERS are the names bound
  ; by the binders in the body of the :LET, which with those in the later
  ; bindings are the names rebound in the scope of a binding.  The
  ; environments returned are for the body of the :LET.
  (define ll-let-binds ((binds bind-listp)
                        (body-binders string-listp)
                        (tenv string-type-mapp)
                        (tlets string-setp)
                        (locals string-setp)
                        (lmap string-expr-mapp)
                        (used string-setp))
    :returns (mv (kept bind-listp)
                 (lifted bind-listp)
                 (new-tenv string-type-mapp)
                 (new-locals string-setp)
                 (new-lmap string-expr-mapp)
                 (new-used string-setp)
                 (new-tlets string-setp))
    (b* (((when (endp binds))
          (mv nil nil
              (string-type-map-fix tenv)
              (string-sfix locals)
              (string-expr-map-fix lmap)
              (string-sfix used)
              (string-sfix tlets)))
         (b (bind-fix (car binds)))
         ((mv new-b lifted1 used) (ll-bind b tenv tlets locals lmap used))
         (rebound (append (bind-list-expr-var-binders (cdr binds))
                          (str::string-list-fix body-binders)))
         ((mv hoistedp var hoisted replacement used)
          (hoist-local-fun new-b rebound tenv locals used))
         ;; the binding is in scope for the rest, kept or not: a hoisted
         ;; name is replaced wherever it is not hidden, so recording it is
         ;; harmless
         ((mv tenv tlets) (extend-tenv-with-let-bind b tenv tlets locals))
         (locals (set::union (bind-bound-expr-vars b) (string-sfix locals)))
         (lmap (if hoistedp
                   (omap::update var replacement (string-expr-map-fix lmap))
                 (string-expr-map-remove-keys (bind-bound-expr-vars b) lmap)))
         ((mv kept lifted2 tenv locals lmap used tlets)
          (ll-let-binds (cdr binds) body-binders tenv tlets locals lmap used)))
      (mv (if hoistedp kept (cons new-b kept))
          (append lifted1 (if hoistedp (list hoisted) nil) lifted2)
          tenv locals lmap used tlets))
    :measure (two-nats-measure (bind-list-count binds) 0))

  :verify-guards :after-returns

  ; The flag function is needed by the well-formedness proofs, which are in
  ; their own book.
  :flag-local nil

  :returns-hints (("Goal" :in-theory (e/d (len)
                                          (binary-append
                                           acl2::utf8-table36-length-lemmas
                                           acl2::consp-when-member-equal-of-cons-listp
                                           member-equal)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lambda-lift-top-expr ((x exprp))
  :guard (not (expr-duplicate-names x))
  :returns (new-x exprp)
  :short "Lambda-lift a standalone (top-level) Remora expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The definitions lifted out of @('x') are wrapped around it in a
     @(':let'), outermost first, so that each is in scope where its
     reference occurs.  When nothing is lifted the expression is returned
     unchanged, rather than wrapped in a @(':let') with no bindings, which
     would not be well formed.")
   (xdoc::p
    "The guard requires the binders of @('x') to bind distinct names, as
     @(tsee expr-uniquify-names) makes them; see @(see lambda-lifting)."))
  (b* ((used (expr-all-expr-vars x))
       ((mv new-x lifted &) (ll-expr x nil nil nil nil used)))
    (nest-let-binds lifted new-x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lambda-lift-top-binds ((binds bind-listp) (used string-setp))
  :returns (new-binds bind-listp)
  :short "Lambda-lift top-level bindings."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the bindings a file's declarations become.  Each is lifted
     out of, but neither hoisted nor recorded as local, since it is not
     local: nothing is local around it.  The definitions lifted out of a
     binding are placed right before it: there, they are in the scope of
     the top-level bindings before it, which they may refer to, and the
     binding is in their scope."))
  (b* (((when (endp binds)) nil)
       ((mv new-b lifted used) (ll-bind (car binds) nil nil nil nil used)))
    (append lifted
            (cons new-b (lambda-lift-top-binds (cdr binds) used)))))

(define lambda-lift-file ((f filep))
  :guard (not (file-duplicate-names f))
  :returns (new-f filep)
  :short "Lambda-lift a Remora file."
  :long
  (xdoc::topstring
   (xdoc::p
    "The declarations are turned into bindings (see @(tsee
     decl-list-to-binds)), lifted by @(tsee lambda-lift-top-binds), and
     turned back into declarations (see @(tsee bind-list-to-decls)).  The
     entry point names are those the file declares, so that a lifted
     definition is a @('def') rather than an entry point.")
   (xdoc::p
    "The guard requires the binders of the file to bind distinct names, as
     @(tsee file-uniquify-names) makes them; see @(see lambda-lifting).")
   (xdoc::p
    "The imports are carried through unchanged; unlike @(tsee
     monomorphize-file), this does not require the file to be
     import-free, since it never needs to look a definition up."))
  (b* (((file f) f)
       (binds (decl-list-to-binds f.decls))
       (new-binds (lambda-lift-top-binds binds (bind-list-all-expr-vars binds)))
       (entry-names (decl-list-entry-names f.decls)))
    (make-file :imports f.imports
               :decls (bind-list-to-decls new-binds entry-names))))
