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
(include-book "type-checker")
(include-book "type-environments")
(include-book "abstract-syntax-well-formedness")
(include-book "free-variable-operations")
(include-book "fresh-variable-operations")
(include-book "lists")
(include-book "osets")
(include-book "kestrel/fty/string-set" :dir :system)
(include-book "utility-transforms")

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
     [impl]'s @('LambdaLift'); as there, captured variables come first.")
   (xdoc::p
    (xdoc::b "What is lifted."))
   (xdoc::p
    "A lambda is lifted when it occurs as an expression, i.e. under @(tsee
     expr-atom), and is closed in type and ispace variables.  Two
     restrictions follow from that.")
   (xdoc::p
    "A lambda inside an array literal is not lifted: an array holds atoms,
     and the reference that would replace the lambda is an expression, so
     there is nowhere to put it.  A lambda that is open in a type or ispace
     variable is not lifted either: abstracting over those would make the
     definition a @(':cfun') or @(':ifun') rather than a @(':fun'), which is
     the business of @(see monomorphize).  Both are left in place, so the
     transformation is always defined, and its result may still contain
     lambdas of those two kinds.")
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
     @(':let') all of whose bindings are hoisted disappears.")
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
     declarations and puts them before the file's own, which is where the
     pipeline stage that this models puts them."))
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
; separately from the type environment, which the type checker may fail to
; extend: a variable must be captured whether or not its type is known.

; The captured variables are the @(tsee set::intersect) of the free variables
; with the local names; see @(tsee emit-lifted-lambda) and @(tsee
; hoist-local-fun).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The lifting step itself, for a lambda whose parameters have been collected
; and whose body has already been lifted out of.  It is not recursive.

(define emit-lifted-lambda ((params var+type?-listp)
                            (body exprp)
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
    "The expression returned, which replaces the lambda, is the name
     applied to the captured variables alone.  That is a partial
     application of the definition, which is what the lambda was: a
     function of its own parameters."))
  (b* ((params (var+type?-list-fix params))
       (body (expr-fix body))
       (used (string-sfix used))
       (fv (set::intersect
            (set::difference (expr-free-expr-vars body)
                             (set::mergesort (var+type?-list->var params)))
            locals))
       (name (fresh-expr-var "lam_" used))
       (used (set::insert name used))
       (bind (make-bind-fun :var name
                            :params (append (names-to-params fv tenv) params)
                            :type? (type-option-none)
                            :expr body)))
    (mv (apply-to-names (expr-var name) fv) (list bind) used)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A chain of nested lambdas, each the whole body of the previous one, is
; flattened into one definition with all their parameters.  This is the
; step of that: does the body consist of a lambda, and if so of what.

(define nested-lambda ((body exprp))
  :returns (mv (nestedp booleanp) (params var+type?-listp) (inner exprp))
  :short "Whether an expression is a lambda, and if so its parameters and body."
  (b* ((body (expr-fix body))
       ((unless (expr-case body :atom)) (mv nil nil body))
       (a (expr-atom->atom body)))
    (atom-case a
      :lambda (mv t (list a.param) a.body)
      :lambdan (mv t a.params a.body)
      :otherwise (mv nil nil body)))

  ///

  (defret expr-count-of-nested-lambda
    (implies nestedp
             (< (expr-count inner) (expr-count body)))
    :rule-classes :linear))

; A lambda is lifted only if it is closed in type and ispace variables; see
; LAMBDA-LIFTING.

(define liftable-lambda-p ((a atomp))
  :returns (yes/no booleanp)
  :short "Whether an atom is a lambda that lifting handles."
  (and (or (atom-case a :lambda) (atom-case a :lambdan))
       (set::emptyp (atom-free-type-vars a))
       (set::emptyp (atom-free-ispace-vars a))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Hoisting of local functions, [impl]'s LIFTLOCALFUN.  A :FUN bound by a
; :LET is hoisted like a lambda --- captured variables prepended, uses
; replaced by the partial application --- provided none of the variables
; it captures is a function.  One that captures a function stays local.
; ([impl] also stays local for that, and errors when both functions and
; values are captured; there is no error channel here, so that case stays
; local too, which is always sound.)

(define function-type-p ((ty typep))
  :returns (yes/no booleanp)
  :short "Whether a type is a function type, as [impl]'s @('isFunctionType')."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, an arrow, possibly as the element type of an array; the
     type checker gives a function variable an array type over an arrow."))
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
                         (tenv string-type-mapp)
                         (locals string-setp)
                         (used string-setp))
  :returns (mv (hoistedp booleanp)
               (var stringp)
               (hoisted bindp)
               (replacement exprp)
               (new-used string-setp))
  :short "Hoist a local function binding, if it captures no function."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given a binding whose body has already been lifted out of, and the
     environment outside it: if it is a @(':fun'), closed in type and
     ispace variables, whose captured variables are not functions, the
     result is @('t'), its variable, a definition of it under a fresh name
     with the captured variables as leading parameters, and the expression
     --- that name applied to the captured variables --- that replaces its
     uses.  Otherwise the result is @('nil') and the binding itself."))
  (b* ((b (bind-fix b))
       (used (string-sfix used))
       ((unless (bind-case b :fun)) (mv nil "" b (expr-var "") used))
       ((bind-fun b) b)
       ((unless (and (set::emptyp (bind-free-type-vars b))
                     (set::emptyp (bind-free-ispace-vars b))))
        (mv nil b.var b (expr-var b.var) used))
       (fv (set::intersect (bind-free-expr-vars b) locals))
       ((when (captures-function-p fv tenv))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines lambda-lift-exprs/atoms/binds
  :short "Lift the lambdas out of expressions, atoms, and bindings,
          and hoist the local functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides the node, each function takes the type environment @('tenv')
     and the set of local names @('locals') of the variables bound around
     the node within the declaration, the map @('lmap') from hoisted local
     functions to the expressions that replace their uses, and the set
     @('used') of names in use.  The first three are scoped; the last is
     threaded.  Each returns the rebuilt node, the definitions lifted out
     of it, and the names in use."))

  (define ll-expr ((x exprp)
                   (tenv string-type-mapp)
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
                 ((when (liftable-lambda-p a))
                  (atom-case a
                    :lambda (ll-lambda (list a.param) a.body
                                       tenv locals lmap used)
                    :lambdan (ll-lambda a.params a.body tenv locals lmap used)
                    :otherwise (mv (expr-fix x) nil (string-sfix used))))
                 ((mv new-a lifted used) (ll-atom a tenv locals lmap used)))
              (mv (expr-atom new-a) lifted used))
      :array (b* (((mv new-as lifted used)
                   (ll-atom-list x.atoms tenv locals lmap used)))
               (mv (expr-array x.dims new-as) lifted used))
      :frame (b* (((mv new-es lifted used)
                   (ll-expr-list x.exprs tenv locals lmap used)))
               (mv (expr-frame x.dims new-es) lifted used))
      :app (b* (((mv new-f lifted1 used) (ll-expr x.fun tenv locals lmap used))
                ((mv new-a lifted2 used) (ll-expr x.arg tenv locals lmap used)))
             (mv (expr-app new-f new-a) (append lifted1 lifted2) used))
      :appn (b* (((mv new-f lifted1 used) (ll-expr x.fun tenv locals lmap used))
                 ((mv new-as lifted2 used)
                  (ll-expr-list x.args tenv locals lmap used)))
              (mv (expr-appn new-f new-as) (append lifted1 lifted2) used))
      :tapp (b* (((mv new-f lifted used) (ll-expr x.fun tenv locals lmap used)))
              (mv (expr-tapp new-f x.arg) lifted used))
      :tappn (b* (((mv new-f lifted used) (ll-expr x.fun tenv locals lmap used)))
               (mv (expr-tappn new-f x.args) lifted used))
      :iapp (b* (((mv new-f lifted used) (ll-expr x.fun tenv locals lmap used)))
              (mv (expr-iapp new-f x.arg) lifted used))
      :iappn (b* (((mv new-f lifted used) (ll-expr x.fun tenv locals lmap used)))
               (mv (expr-iappn new-f x.args) lifted used))
      :capp (b* (((mv new-f lifted1 used) (ll-expr x.fun tenv locals lmap used))
                 ((mv new-as lifted2 used)
                  (ll-expr-list x.args tenv locals lmap used)))
              (mv (expr-capp new-f x.targs x.iargs new-as)
                  (append lifted1 lifted2) used))
      :unbox (b* ((body-locals (set::insert x.var (string-sfix locals)))
                  ((mv new-t lifted1 used)
                   (ll-expr x.target tenv locals lmap used))
                  ((mv new-b lifted2 used)
                   (ll-expr x.body tenv body-locals lmap used)))
               (mv (expr-unbox x.ispace x.var new-t new-b x.type?)
                   (append lifted1 lifted2) used))
      :unboxn (b* ((body-locals (set::insert x.var (string-sfix locals)))
                   ((mv new-t lifted1 used)
                    (ll-expr x.target tenv locals lmap used))
                   ((mv new-b lifted2 used)
                    (ll-expr x.body tenv body-locals lmap used)))
                (mv (expr-unboxn x.ispaces x.var new-t new-b x.type?)
                    (append lifted1 lifted2) used))
      :bracket (b* (((mv new-es lifted used)
                     (ll-expr-list x.exprs tenv locals lmap used)))
                 (mv (expr-bracket new-es) lifted used))
      :let (b* (((mv kept lifted1 tenv locals lmap used)
                 (ll-let-binds x.binds tenv locals lmap used))
                ((mv new-b lifted2 used) (ll-expr x.body tenv locals lmap used)))
             ;; a :LET all of whose bindings were hoisted is just its body
             (mv (if (consp kept) (expr-let kept new-b) new-b)
                 (append lifted1 lifted2)
                 used))
      :otherwise (mv (expr-fix x) nil (string-sfix used)))
    :measure (two-nats-measure (expr-count x) 0))

  ; A lambda, with the parameters collected so far.  A body that is itself
  ; a lambda is absorbed into the parameter list rather than lifted on its
  ; own, so that a chain of lambdas yields one definition.
  (define ll-lambda ((params var+type?-listp)
                     (body exprp)
                     (tenv string-type-mapp)
                     (locals string-setp)
                     (lmap string-expr-mapp)
                     (used string-setp))
    :returns (mv (e exprp) (lifted bind-listp) (new-used string-setp))
    (b* ((params (var+type?-list-fix params))
         (tenv (extend-tenv-with-params params tenv))
         (locals (locals-with-params params locals))
         ((mv nestedp more-params inner) (nested-lambda body))
         ((when nestedp)
          (ll-lambda (append params more-params) inner tenv locals lmap used))
         ((mv new-body lifted used) (ll-expr body tenv locals lmap used))
         ;; the definitions lifted out of the body go before this one,
         ;; which refers to them
         ((mv e more used) (emit-lifted-lambda params new-body tenv locals used)))
      (mv e (append lifted more) used))
    :measure (two-nats-measure (expr-count body) 1))

  (define ll-expr-list ((x expr-listp)
                        (tenv string-type-mapp)
                        (locals string-setp)
                        (lmap string-expr-mapp)
                        (used string-setp))
    :returns (mv (new-x (and (expr-listp new-x)
                             (equal (len new-x) (len x))))
                 (lifted bind-listp)
                 (new-used string-setp))
    (b* (((when (endp x)) (mv nil nil (string-sfix used)))
         ((mv new-e lifted1 used) (ll-expr (car x) tenv locals lmap used))
         ((mv new-es lifted2 used) (ll-expr-list (cdr x) tenv locals lmap used)))
      (mv (cons new-e new-es) (append lifted1 lifted2) used))
    :measure (two-nats-measure (expr-list-count x) 0))

  (define ll-atom ((x atomp)
                   (tenv string-type-mapp)
                   (locals string-setp)
                   (lmap string-expr-mapp)
                   (used string-setp))
    :returns (mv (new-x atomp) (lifted bind-listp) (new-used string-setp))
    (atom-case x
      :lambda (b* ((body-tenv (extend-tenv-with-params (list x.param) tenv))
                   (body-locals (locals-with-params (list x.param) locals))
                   ((mv new-b lifted used)
                    (ll-expr x.body body-tenv body-locals lmap used)))
                (mv (atom-lambda x.param new-b x.type?) lifted used))
      :lambdan (b* ((body-tenv (extend-tenv-with-params x.params tenv))
                    (body-locals (locals-with-params x.params locals))
                    ((mv new-b lifted used)
                     (ll-expr x.body body-tenv body-locals lmap used)))
                 (mv (atom-lambdan x.params new-b x.type?) lifted used))
      :tlambda (b* (((mv new-b lifted used) (ll-expr x.body tenv locals lmap used)))
                 (mv (atom-tlambda x.param new-b) lifted used))
      :tlambdan (b* (((mv new-b lifted used) (ll-expr x.body tenv locals lmap used)))
                  (mv (atom-tlambdan x.params new-b) lifted used))
      :ilambda (b* (((mv new-b lifted used) (ll-expr x.body tenv locals lmap used)))
                 (mv (atom-ilambda x.param new-b) lifted used))
      :ilambdan (b* (((mv new-b lifted used) (ll-expr x.body tenv locals lmap used)))
                  (mv (atom-ilambdan x.params new-b) lifted used))
      :box (b* (((mv new-a lifted used) (ll-expr x.array tenv locals lmap used)))
             (mv (atom-box x.ispace new-a x.type?) lifted used))
      :boxn (b* (((mv new-a lifted used) (ll-expr x.array tenv locals lmap used)))
              (mv (atom-boxn x.ispaces new-a x.type) lifted used))
      :otherwise (mv (atom-fix x) nil (string-sfix used)))
    :measure (two-nats-measure (atom-count x) 0))

  (define ll-atom-list ((x atom-listp)
                        (tenv string-type-mapp)
                        (locals string-setp)
                        (lmap string-expr-mapp)
                        (used string-setp))
    :returns (mv (new-x (and (atom-listp new-x)
                             (equal (len new-x) (len x))))
                 (lifted bind-listp)
                 (new-used string-setp))
    (b* (((when (endp x)) (mv nil nil (string-sfix used)))
         ((mv new-a lifted1 used) (ll-atom (car x) tenv locals lmap used))
         ((mv new-as lifted2 used) (ll-atom-list (cdr x) tenv locals lmap used)))
      (mv (cons new-a new-as) (append lifted1 lifted2) used))
    :measure (two-nats-measure (atom-list-count x) 0))

  (define ll-bind ((x bindp)
                   (tenv string-type-mapp)
                   (locals string-setp)
                   (lmap string-expr-mapp)
                   (used string-setp))
    :returns (mv (new-x bindp) (lifted bind-listp) (new-used string-setp))
    (bind-case x
      :val (b* (((mv new-e lifted used) (ll-expr x.expr tenv locals lmap used)))
             (mv (bind-val x.var x.type? new-e) lifted used))
      :fun (b* ((body-tenv (extend-tenv-with-params x.params tenv))
                (body-locals (locals-with-params x.params locals))
                ((mv new-e lifted used)
                 (ll-expr x.expr body-tenv body-locals lmap used)))
             (mv (bind-fun x.var x.params x.type? new-e) lifted used))
      :tfun (b* (((mv new-e lifted used) (ll-expr x.expr tenv locals lmap used)))
              (mv (bind-tfun x.var x.params x.type? new-e) lifted used))
      :ifun (b* (((mv new-e lifted used) (ll-expr x.expr tenv locals lmap used)))
              (mv (bind-ifun x.var x.params x.type? new-e) lifted used))
      :cfun (b* ((body-tenv (extend-tenv-with-params x.params tenv))
                 (body-locals (locals-with-params x.params locals))
                 ((mv new-e lifted used)
                  (ll-expr x.expr body-tenv body-locals lmap used)))
              (mv (bind-cfun x.var x.tparams? x.iparams? x.params x.type new-e)
                  lifted used))
      :otherwise (mv (bind-fix x) nil (string-sfix used)))
    :measure (two-nats-measure (bind-count x) 0))

  ; The bindings of a :LET, in order.  Each is lifted out of, and then
  ; either hoisted --- recorded in LMAP, and not kept --- or kept.  The
  ; environments returned are for the body of the :LET.
  (define ll-let-binds ((binds bind-listp)
                        (tenv string-type-mapp)
                        (locals string-setp)
                        (lmap string-expr-mapp)
                        (used string-setp))
    :returns (mv (kept bind-listp)
                 (lifted bind-listp)
                 (new-tenv string-type-mapp)
                 (new-locals string-setp)
                 (new-lmap string-expr-mapp)
                 (new-used string-setp))
    (b* (((when (endp binds))
          (mv nil nil
              (string-type-map-fix tenv)
              (string-sfix locals)
              (string-expr-map-fix lmap)
              (string-sfix used)))
         (b (bind-fix (car binds)))
         ((mv new-b lifted1 used) (ll-bind b tenv locals lmap used))
         ((mv hoistedp var hoisted replacement used)
          (hoist-local-fun new-b tenv locals used))
         ;; the binding is in scope for the rest, kept or not: a hoisted
         ;; name never occurs again, so recording it is harmless
         (tenv (extend-tenv-with-binds (list b) tenv))
         (locals (set::union (bind-bound-expr-vars b) (string-sfix locals)))
         (lmap (if hoistedp
                   (omap::update var replacement (string-expr-map-fix lmap))
                 (string-expr-map-fix lmap)))
         ((mv kept lifted2 tenv locals lmap used)
          (ll-let-binds (cdr binds) tenv locals lmap used)))
      (mv (if hoistedp kept (cons new-b kept))
          (append lifted1 (if hoistedp (list hoisted) nil) lifted2)
          tenv locals lmap used))
    :measure (two-nats-measure (bind-list-count binds) 0))

  ; Top-level bindings, as a file's declarations become: lifted out of, but
  ; neither hoisted nor recorded as local, since they are not local.
  (define ll-bind-list ((x bind-listp)
                        (tenv string-type-mapp)
                        (locals string-setp)
                        (lmap string-expr-mapp)
                        (used string-setp))
    :returns (mv (new-x (and (bind-listp new-x)
                             (equal (len new-x) (len x))))
                 (lifted bind-listp)
                 (new-used string-setp))
    (b* (((when (endp x)) (mv nil nil (string-sfix used)))
         ((mv new-b lifted1 used) (ll-bind (car x) tenv locals lmap used))
         ((mv new-bs lifted2 used) (ll-bind-list (cdr x) tenv locals lmap used)))
      (mv (cons new-b new-bs) (append lifted1 lifted2) used))
    :measure (two-nats-measure (bind-list-count x) 0))

  :verify-guards :after-returns

  ; The flag function is needed by the well-formedness proofs, which are in
  ; their own book.
  :flag-local nil

  :returns-hints (("Goal" :in-theory (enable len))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lambda-lift-top-expr ((x exprp))
  :returns (new-x exprp)
  :short "Lambda-lift a standalone (top-level) Remora expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The definitions lifted out of @('x') are wrapped around it in a
     @(':let'), outermost first, so that each is in scope where its
     reference occurs.  When nothing is lifted the expression is returned
     unchanged, rather than wrapped in a @(':let') with no bindings, which
     would not be well formed."))
  (b* ((used (expr-all-expr-vars x))
       ((mv new-x lifted &) (ll-expr x nil nil nil used)))
    (nest-let-binds lifted new-x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lambda-lift-file ((f filep))
  :returns (new-f filep)
  :short "Lambda-lift a Remora file."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each declaration is lifted in turn, and the definitions lifted out of
     all of them are turned into declarations, by @(tsee
     bind-list-to-decls), and placed before the file's own.  The entry point
     names are those the file declares, so that a lifted definition is a
     @('def') rather than an entry point.")
   (xdoc::p
    "The imports are carried through unchanged; unlike @(tsee
     monomorphize-file), this does not require the file to be
     import-free, since it never needs to look a definition up."))
  (b* (((file f) f)
       (binds (decl-list-to-binds f.decls))
       (used (bind-list-all-expr-vars binds))
       ((mv new-binds lifted &) (ll-bind-list binds nil nil nil used))
       (entry-names (decl-list-entry-names f.decls))
       (new-decls (bind-list-to-decls (append lifted new-binds) entry-names)))
    (make-file :imports f.imports :decls new-decls)))
