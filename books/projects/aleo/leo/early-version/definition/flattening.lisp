; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "files")
(include-book "values")
(include-book "value-expressions")
(include-book "arithmetic-operations")
(include-book "shift-operations")
(include-book "bitwise-operations")
(include-book "equality-operations")
(include-book "logical-operations")
(include-book "ordering-operations")

(include-book "kestrel/number-theory/prime" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ flattening
  :parents (definition)
  :short "Flattening of Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "Leo code is flattened by transforming it according to certain criteria.
     The transformation involves:")
   (xdoc::ul
    (xdoc::li
     "Constant propagation.")
    (xdoc::li
     "Constant folding.")
    (xdoc::li
     "Loop unrolling.")
    (xdoc::li
     "Function specialization."))
   (xdoc::p
    "The latter could be replaced by function inlining,
     but for now we want to preserve the functional decomposition of the program
     and therefore we do function specialization instead.")
   (xdoc::p
    "The flattening transformation starts with known values for
     the constant inputs of the @('main') function.
     The transformation goes through
     the statements and expressions of the @('main') function,
     transforming them as follows
     (the same transformations also apply to other functions;
     more on this below).")
   (xdoc::p
    "The known values of the constants are propagated
     where those constants are mentioned in expressions.
     That is, the names of the constants are replaced with "
    (xdoc::seetopic "value-expressions" "value expressions")
    ".")
   (xdoc::p
    "This constant propagation may cause certain (sub)expressions
     to consists of operators applied to operands that are value expressions.
     In this case, the constants can be folded,
     i.e. the operands are evaluated to values,
     the operator is applied to values,
     and the result is turned into a value expression.
     This is constant folding.")
   (xdoc::p
    "Note that constant folding also applies to
     constant expression that only involve literals and operators
     (i.e. no named constants),
     which perhaps the Leo code writer has written that way for clarity.
     Those are folded by this transformation, as expected and desired.")
   (xdoc::p
    "When we encounter a constant declaration,
     assuming that the code is type-checked,
     the initializing expression must be constant.
     Therefore, constant propagation and folding must cause it
     to be turned into a value (more precisely, a value expression).
     Thus, we extend our table of known constant values
     with a new association, so that this constant can be also propagated.")
   (xdoc::p
    "When a loop is encountered,
     assuming that the code is type-checked,
     the starting and ending bounds must be reducible to values,
     in the same way as the initializing expressions of constant declarations.
     Thus, we know all the values that the loop counter goes through,
     and we unroll the loop.
     This is done by replicating the body block as many times
     as the values taken by the loop counter, in order.
     For each replicated block,
     the table of known constant values
     is extended with the known value of the loop counter,
     so that constant propagation and folding can be performed
     in each replicated block.")
   (xdoc::p
    "When we encounter a call of a function, say @('f'),
     given that, as mentioned above, we do not do inlining,
     we proceed as follows instead.
     First, we transform its argument expressions.
     If @('f') has no constant parameters,
     there is nothing else to do for the call.
     If @('f') has one or more constant parameters,
     then, assuming that the code is type-checked,
     the values passed to these constant parameters must be known.
     We generate a version @('f1') of @('f')
     that is specialized to these constant input values.
     This function @('f1') only has the non-constant parameters of @('f'),
     and no constant parameters.
     The body of @('f1') is transformed in the same way as explained above;
     the starting point consists of
     the known values of the constant parameters.")
   (xdoc::p
    "The above transformations, which start on @('main'),
     are performed on all the functions
     called directly or indirectly from @('main').
     As explained, this may cause the creation of new functions,
     specialized to certain values of the constant parameters;
     there may be multiple specialized versions of the same function,
     corresponding to different combinations of constant values.")
   (xdoc::p
    "Functions with constant parameters are eventually eliminated.
     Only their specialized versions survive the transformation.
     Function without constant parameters survive if they are called,
     directly or indirectly, from @('main');
     otherwise, they are eliminated, since they are dead code
     (when starting execution from @('main')).
     The @('main') function is transformed, besides in the body as above,
     also by removing its constant parameters,
     since they have been used to transform the body.")
   (xdoc::p
    "Overall, this transformation produces a new program that includes
     one or more functions (i.e. @('main') plus zero or more functions),
     each of which has no constant parameters,
     no constant declarations,
     and no loops;
     it also does not contain any ``reducible expression'',
     i.e. an expression that could be evaluated to a value.")
   (xdoc::p
    "We formalize these flattening transformations as
     executable ACL2 functions that perform the flattening.
     These ACL2 functions return error indications
     when certain unexpected conditions happen,
     e.g. that the initializing expression of a constant declaration
     cannot be evaluated to a value.
     These conditions should be ruled out by type checking:
     that is, type checking, which also does ``constancy checking'',
     is meant to ensure that the code can in fact be flattened.
     We plan to prove formally that this is the case:
     that is, that the executable transformation functions
     never returns certain error indications
     when executed over type-checked code;
     this proof, which is similar to the one planned for the dynamic semantics,
     would also provide a major validation of the design of Leo.")
   (xdoc::p
    "More precisely, the flattening ACL2 functions
     may return two kinds of errors.
     A static error happens when some condition is violated
     that should be ruled out by type checking:
     we plan to prove that static errors never occur
     when flattening type-checked code,
     as mentioned above.
     A dynamic error happens when constant folding
     results in an erroneous operation,
     such as integer overflow:
     these conditions are not ruled out by type checking,
     and may cause actual errors when flattening type-checked code."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap const-fenv
  :short "Fixtype of constant flattening environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "A constant flattening environment captures the information
     about the currently known values of constants.
     It is a finite map from constant names (identifiers) to values."))
  :key-type identifier
  :val-type value
  :pred const-fenvp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod fenv
  :short "Fixtype of flattening environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of a constant flattening environment
     and a curve (the one that Leo is parameterized ove).
     This may be extended with additional components at some point."))
  ((constants const-fenv)
   (curve curve))
  :tag :fenv
  :pred fenvp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption fenv-option
  fenv
  :short "Fixtype of optional flattening environments."
  :pred fenv-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-fenv ((curve curvep))
  :returns (env fenvp)
  :short "Initial flattening environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This only contains
     the prime and the curve and the curve order (scalar-prime),
     and no constants."))
  (make-fenv :constants nil :curve curve)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fenv-const-lookup ((const identifierp) (env fenvp))
  :returns (val value-optionp
                :hints (("Goal" :in-theory (enable value-optionp))))
  :short "Look up a constant in a flattening environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return the associated value if the constant is found
     in the constant flattening environment of the flattening environment.
     Otherwise we return @('nil')."))
  (cdr (omap::assoc (identifier-fix const) (fenv->constants env)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fenv-const-add ((const identifierp) (val valuep) (env fenvp))
  :returns (new-env fenv-optionp)
  :short "Extend a flattening environment with a constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return @('nil') if a constant with that name is already present."))
  (b* ((const-env (fenv->constants env))
       ((when (consp (omap::assoc (identifier-fix const) const-env))) nil)
       (new-const-env (omap::update (identifier-fix const)
                                    (value-fix val)
                                    const-env)))
    (change-fenv env :constants new-const-env))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines flatten-expression
  :short "Flatten an expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "A variable or constant is looked up in the flattening environment.
     If it is found, it is regarded as a constant,
     and it is replaced with an expression for its value.
     If it is not found, it is regarded as a variable,
     and left unchanged.")
   (xdoc::p
    "A literal is left unchanged.")
   (xdoc::p
    "For a unary expression,
     first we transform the operand.
     If the transformed operand is a value expression,
     we apply the operator to the denoted value,
     and then we replace the whole unary expression with
     the value expression that denotes the result value.
     If the transformed operand is not a value expression,
     we leave the unary operator applied to the transformed operand.")
   (xdoc::p
    "Binary expressions are handled similarly to unary ones,
     but both operands must be value expressions
     in order to apply the operator to the denoted values.")
   (xdoc::p
    "For a conditional expression, we first transform the test.
     If the transformed test is a value expression that evaluates to true,
     we transform and return the true branch, ignoring the false branch.
     If the transformed test is a value expression that evaluates to false,
     we transform and return the flse branch, ignoring the true branch.
     If the transformed test is a value expression
     that evaluates to a non-boolean,
     it is a static error;
     this should never happen with type-checked code.
     If the transformed test is not a value expression,
     we transform both true and false branches,
     and return a conditional with the transformed operands.")
   (xdoc::p
    "For a tuple expression, we first transform the components.
     If they are all value expressions, we evaluate them,
     obtaining a tuple, and turn that into its value expression.")
   (xdoc::p
    "For a tuple component expression, we first transform the sub-expression.
     If it is a value expression, we extract the component.")
   (xdoc::p
    "For now we reject function calls; we will cover them later."))

  (define flatten-expression ((expr expressionp) (env fenvp))
    :returns (new-expr expression-resultp)
    (expression-case
     expr
     :literal (expression-fix expr)
     :var/const (b* ((val (fenv-const-lookup expr.name env)))
                  (if val
                      (b* ((new-expr (value-to-value-expr val))
                           ((when (reserrp new-expr))
                            (reserrf (list :static new-expr))))
                        new-expr)
                    (expression-fix expr)))
     :assoc-const (reserrf :todo)
     :unary (b* (((okf new-arg) (flatten-expression expr.arg env))
                 ((unless (expression-valuep new-arg))
                  (make-expression-unary :op expr.op
                                         :arg new-arg))
                 (arg-val (value-expr-to-value new-arg (fenv->curve env)))
                 ((when (reserrp arg-val))
                  (reserrf (list :static arg-val)))
                 ((okf expr-val)
                  (unop-case expr.op
                             :not (op-not arg-val)
                             :neg (op-neg arg-val (fenv->curve env))
                             :abs (op-abs arg-val)
                             :abs-wrapped (op-abs-wrapped arg-val)
                             :double (op-double arg-val
                                                (fenv->curve env))
                             :inv (op-inv arg-val (fenv->curve env))
                             :square (op-square arg-val (fenv->curve env))
                             :square-root (op-square-root arg-val
                                                          (fenv->curve env))))
                 (new-expr (value-to-value-expr expr-val))
                 ((when (reserrp new-expr))
                  (reserrf (list :static new-expr))))
              new-expr)
     :binary (b* (((okf new-arg1) (flatten-expression expr.arg1 env))
                  ((okf new-arg2) (flatten-expression expr.arg2 env))
                  ((unless (and (expression-valuep new-arg1)
                                (expression-valuep new-arg2)))
                   (make-expression-binary :op expr.op
                                           :arg1 new-arg1
                                           :arg2 new-arg2))
                  (arg1-val (value-expr-to-value new-arg1 (fenv->curve env)))
                  ((when (reserrp arg1-val))
                   (reserrf (list :static arg1-val)))
                  (arg2-val (value-expr-to-value new-arg2 (fenv->curve env)))
                  ((when (reserrp arg2-val))
                   (reserrf (list :static arg2-val)))
                  ((okf expr-val)
                   (binop-case
                    expr.op
                    :nand (op-nand arg1-val arg2-val)
                    :nor (op-nor arg1-val arg2-val)
                    :and (op-and arg1-val arg2-val)
                    :or (op-or arg1-val arg2-val)
                    :eq (op-eq arg1-val arg2-val)
                    :ne (op-ne arg1-val arg2-val)
                    :ge (op-ge arg1-val arg2-val)
                    :gt (op-gt arg1-val arg2-val)
                    :le (op-le arg1-val arg2-val)
                    :lt (op-lt arg1-val arg2-val)
                    :bitxor (op-bitxor arg1-val arg2-val)
                    :bitior (op-bitior arg1-val arg2-val)
                    :bitand (op-bitand arg1-val arg2-val)
                    :shl (op-shl arg1-val arg2-val)
                    :shr (op-shr arg1-val arg2-val)
                    :shl-wrapped (op-shl-wrapped arg1-val arg2-val)
                    :shr-wrapped (op-shr-wrapped arg1-val arg2-val)
                    :add (op-add arg1-val
                                 arg2-val
                                 (fenv->curve env))
                    :sub (op-sub arg1-val
                                 arg2-val
                                 (fenv->curve env))
                    :mul (op-mul arg1-val
                                 arg2-val
                                 (fenv->curve env))
                    :div (op-div arg1-val
                                 arg2-val
                                 (fenv->curve env))
                    :rem (op-rem arg1-val
                                 arg2-val
                                 (fenv->curve env))
                    :pow (op-pow arg1-val
                                 arg2-val
                                 (fenv->curve env))
                    :add-wrapped (op-add-wrapped arg1-val
                                                 arg2-val
                                                 (fenv->curve env))
                    :sub-wrapped (op-sub-wrapped arg1-val
                                                 arg2-val
                                                 (fenv->curve env))
                    :mul-wrapped (op-mul-wrapped arg1-val
                                                 arg2-val
                                                 (fenv->curve env))
                    :div-wrapped (op-div-wrapped arg1-val
                                                 arg2-val
                                                 (fenv->curve env))
                    :rem-wrapped (op-rem-wrapped arg1-val
                                                 arg2-val
                                                 (fenv->curve env))
                    :pow-wrapped (op-pow-wrapped arg1-val
                                                 arg2-val (fenv->curve env))))
                  (new-expr (value-to-value-expr expr-val))
                  ((when (reserrp new-expr))
                   (reserrf (list :static new-expr))))
               new-expr)
     :cond (b* (((okf new-test) (flatten-expression expr.test env)))
             (if (expression-valuep new-test)
                 (b* ((test-val
                       (value-expr-to-value new-test (fenv->curve env)))
                      ((when (reserrp test-val))
                       (reserrf (list :static test-val)))
                      ((when (equal test-val (value-bool t)))
                       (flatten-expression expr.then env))
                      ((when (equal test-val (value-bool nil)))
                       (flatten-expression expr.else env)))
                   (reserrf (list :static :test-value test-val)))
               (b* (((okf new-then) (flatten-expression expr.then env))
                    ((okf new-else) (flatten-expression expr.else env)))
                 (make-expression-cond :test new-test
                                       :then new-then
                                       :else new-else))))
     :unit (make-expression-unit)
     :tuple (b* (((okf new-exprs) (flatten-expression-list expr.components env))
                 ((when (expression-list-valuep new-exprs))
                  (b* (((okf vals)
                        (value-expr-list-to-value-list new-exprs
                                                       (fenv->curve env)))
                       (val (op-tuple-make vals)))
                    (value-to-value-expr val))))
              (make-expression-tuple :components new-exprs))
     :tuple-component (b* (((okf new-expr) (flatten-expression expr.tuple env))
                           ((when (expression-valuep new-expr))
                            (b* (((okf val)
                                  (value-expr-to-value new-expr
                                                       (fenv->curve env)))
                                 ((okf new-val) (op-tuple-read val expr.index)))
                              (value-to-value-expr new-val))))
                        (make-expression-tuple-component
                         :tuple new-expr
                         :index expr.index))
     :struct (reserrf (list :dynamic :todo-struct))
     :struct-component (reserrf (list :dynamic :todo-struct-component))
     :internal-call (reserrf (list :dynamic :todo-call))
     :external-call (reserrf (list :dynamic :todo-call))
     :static-call (reserrf (list :dynamic :todo-call)))
    :measure (expression-count expr))

  (define flatten-expression-list ((exprs expression-listp) (env fenvp))
    :returns (new-exprs expression-list-resultp)
    :short "Flatten a list of expressions."
    (b* (((when (endp exprs)) nil)
         ((okf new-expr) (flatten-expression (car exprs) env))
         ((okf new-exprs) (flatten-expression-list (cdr exprs) env)))
      (cons new-expr new-exprs))
    :measure (expression-list-count exprs))

  :prepwork
  ((local
    (in-theory
     (enable
      expressionp-when-expression-resultp-and-not-reserrp
      expression-listp-when-expression-list-resultp-and-not-reserrp))))

  :verify-guards nil ; done below
  ///
  (verify-guards flatten-expression)

  (fty::deffixequiv-mutual flatten-expression))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simplify-flattened-if ((branches branch-listp) (else statement-listp))
  :returns (stmt statementp)
  :short "Simplify a flattened conditional statement."
  :long
  (xdoc::topstring
   (xdoc::p
    "A conditional statement is flattened in two phases.
     The first phase, in @(tsee flatten-statement),
     homomorphically flattens their constituents,
     obtaining a list of branches with flattened tests and bodies
     plus a flattened list of statements for the default.
     In the second phase, which we do in this ACL2 function here,
     we simplify things as follows.
     We go through the branches in order, and:
     (i) if a branch test is false, we remove the branch
     and continue processing the subsequent ones;
     (ii) if a branch test is true, we discard all the branches that follow;
     (iii) otherwise, we keep the branch
     and continue processing the subsequent ones.
     The default block is discarded if a branch with true test is found;
     otherwise it is kept.
     If no branches are left (i.e. they have all been removed),
     we just return the default block.
     If there are branches left,
     we return those along with the default branch,
     packaged into a conditional statement.
     In any case, this ACL2 function returns a statement.
     This function never returns any error.
     The returned statement may be the same as
     the result from the first phase,
     i.e. the second phase may not simplify anything."))
  (b* (((mv new-branches new-else) (simplify-flattened-if-aux branches else)))
    (if (consp new-branches)
        (make-statement-if :branches new-branches :else new-else)
      (statement-block new-else)))
  :hooks (:fix)

  :prepwork
  ((define simplify-flattened-if-aux ((branches branch-listp)
                                      (else statement-listp))
     :returns (mv (new-branches branch-listp)
                  (new-else statement-listp))
     :parents nil
     (b* (((when (endp branches)) (mv nil (statement-list-fix else)))
          (branch (car branches))
          ((when (equal (branch->test branch)
                        (expression-literal (literal-bool t))))
           (mv nil (branch->body branch)))
          ((when (equal (branch->test branch)
                        (expression-literal (literal-bool nil))))
           (simplify-flattened-if-aux (cdr branches) else))
          ((mv new-cdr-branches new-else)
           (simplify-flattened-if-aux (cdr branches) else))
          (new-branches (cons (branch-fix branch)
                              new-cdr-branches)))
       (mv new-branches new-else))
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines flatten-statements/branches
  :short "Flatten statements and branches."

  (define flatten-statement ((stmt statementp) (env fenvp))
    :returns (new-stmt statement-resultp)
    :short "Flatten a statement."
    :long
    (xdoc::topstring
     (xdoc::p
      "For a variable declaration, we flatten the initializer.
       The variable declaration remains,
       even if the initializer is a constant expression:
       here we only propagate actual constants,
       not also variables that happen to have a constant value.
       The latter kind of transformation will be handled separately.")
     (xdoc::p
      "Constant declarations are handled not here but
       in the ACL2 function to flatten lists of statements.
       The reason is that constant declarations are
       incorporated into the flattening environments and removed;
       the removal does not produce any statement in that place.
       Because of that, the code in this ACL2 function
       for the constant declaration case should be unreachable.")
     (xdoc::p
      "For an assignment, we flatten the left-hand side and the right-hand side.
       In the current version of Leo flattening the left-hand side
       has no effect in type-correct code,
       where the left-hand side is always a variable.")
     (xdoc::p
      "For a return statement, we flatten the expression.")
     (xdoc::p
      "For now we reject loop statements,
       because we only do constant propagation and unfolding.
       We will do loop unrolling later.")
     (xdoc::p
      "Conditional statements are flattened in two phases.
       The first phase, carried out in these ACL2 functions here,
       homomorphically flattens their constituents.
       The second phase, carried out in @(tsee simplify-flattened-if),
       simplifies the resulting constituents.")
     (xdoc::p
      "For a console statement, we transform its arguments.")
     (xdoc::p
      "For a block, we flatten its statements."))
    (statement-case
     stmt
     :let
     (b* (((vardecl decl) stmt.get)
          ((okf new-init) (flatten-expression decl.init env)))
       (statement-let (change-vardecl stmt.get :init new-init)))
     :const
     (reserrf (list :static :unreachable))
     :assign
     (b* (((okf new-left) (flatten-expression stmt.left env))
          ((okf new-right) (flatten-expression stmt.right env)))
       (make-statement-assign :op stmt.op :left new-left :right new-right))
     :return
     (b* (((okf new-value) (flatten-expression stmt.value env)))
       (make-statement-return :value new-value))
     :for
     (reserrf (list :dynamic :todo-for))
     :if
     (b* (((okf new-branches) (flatten-branch-list stmt.branches env))
          ((okf new-else) (flatten-statement-list stmt.else env)))
       (simplify-flattened-if new-branches new-else))
     :console
     (console-case
      stmt.get
      :assert
      (b* (((okf new-arg) (flatten-expression stmt.get.arg env)))
        (statement-console (console-assert new-arg)))
      :error
      (b* (((okf new-exprs) (flatten-expression-list stmt.get.exprs env)))
        (statement-console (make-console-error :string stmt.get.string
                                               :exprs new-exprs)))
      :log
      (b* (((okf new-exprs) (flatten-expression-list stmt.get.exprs env)))
        (statement-console (make-console-log :string stmt.get.string
                                             :exprs new-exprs))))
     ;; TODO: the next three
     :finalize
     (reserrf :flattening-finalize-statement-not-yet-implemented)
     :increment
     (reserrf :flattening-increment-statement-not-yet-implemented)
     :decrement
     (reserrf :flattening-decrement-statement-not-yet-implemented)
     :block
     (b* (((okf new-stmts) (flatten-statement-list stmt.get env)))
       (statement-block new-stmts)))
    :measure (statement-count stmt))

  (define flatten-statement-list ((stmts statement-listp) (env fenvp))
    :returns (new-stmts statement-list-resultp)
    :short "Flatten a list of statements."
    :long
    (xdoc::topstring
     (xdoc::p
      "If we encounter a constant declaration, we process it here:
       we flatten its initializer,
       we turn into a value,
       we extend the flattening environment with the new constant,
       and we discard the constant declaration.")
     (xdoc::p
      "If we encounter any other kind of statement,
       we flatten it and then we flatten the subsequent ones."))
    (b* (((when (endp stmts)) nil)
         (stmt (car stmts)))
      (if (statement-case stmt :const)
          (b* (((constdecl decl) (statement-const->get stmt))
               ((okf new-init) (flatten-expression decl.init env))
               ((unless (expression-valuep new-init))
                (reserrf (list :static :const-init-not-value)))
               (val (value-expr-to-value new-init (fenv->curve env)))
               ((when (reserrp val)) (reserrf (list :static val)))
               (env (fenv-const-add decl.name val env))
               ((unless env) (reserrf (list :static :duplicate-const))))
            (flatten-statement-list (cdr stmts) env))
        (b* (((okf new-stmt) (flatten-statement stmt env))
             ((okf new-stmts) (flatten-statement-list (cdr stmts) env)))
          (cons new-stmt new-stmts))))
    :measure (statement-list-count stmts))

  (define flatten-branch ((branch branchp) (env fenvp))
    :returns (new-branch branch-resultp)
    :short "Flatten a branch."
    :long
    (xdoc::topstring
     (xdoc::p
      "We homomorphically flatten test and body."))
    (b* (((okf new-test) (flatten-expression (branch->test branch) env))
         ((okf new-body) (flatten-statement-list (branch->body branch) env)))
      (make-branch :test new-test :body new-body))
    :measure (branch-count branch))

  (define flatten-branch-list ((branches branch-listp) (env fenvp))
    :returns (new-branches branch-list-resultp)
    :short "Flatten a list of branches."
    :long
    (xdoc::topstring
     (xdoc::p
      "We homomorphically flatten the elements of the list."))
    (b* (((when (endp branches)) nil)
         ((okf new-branch) (flatten-branch (car branches) env))
         ((okf new-branches) (flatten-branch-list (cdr branches) env)))
      (cons new-branch new-branches))
    :measure (branch-list-count branches))

  :prepwork
  ((local
    (in-theory
     (enable
      statementp-when-statement-resultp-and-not-reserrp
      statement-listp-when-statement-list-resultp-and-not-reserrp
      branchp-when-branch-resultp-and-not-reserrp
      branch-listp-when-branch-list-resultp-and-not-reserrp))))

  :verify-guards nil ; done below
  ///
  (verify-guards flatten-statement)

  (fty::deffixequiv-mutual flatten-statements/branches))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define flatten-fundecl ((decl fundeclp) (env fenvp))
  :returns (new-decl fundecl-resultp)
  :short "Flatten a function declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "The flattening environment passed to this ACL2 function
     is meant to consist of the known values of the constant parameters.
     We are not yet handling function specialization here
     (which is where these environments will be calculated).")
   (xdoc::p
    "Any case, given such an environment,
     the function declaration is flattened
     by flattening its body."))
  (b* (((fundecl decl) decl)
       ((okf new-body) (flatten-statement-list decl.body env)))
    (change-fundecl decl :body new-body))
  :hooks (:fix))
