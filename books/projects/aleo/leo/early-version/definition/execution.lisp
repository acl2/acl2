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
(include-book "dynamic-environments")
(include-book "locations")
(include-book "arithmetic-operations")
(include-book "shift-operations")
(include-book "bitwise-operations")
(include-book "equality-operations")
(include-book "logical-operations")
(include-book "ordering-operations")
(include-book "tuple-operations")
(include-book "struct-operations")
(include-book "literal-evaluation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ execution
  :parents (dynamic-semantics)
  :short "Execution of expressions, statements, etc."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize a big-step interpretive operational semantics,
     via mutually recursive ACL2 functions
     over the abstract syntax of expressions and statements.
     The `big-step' attribute means that the ACL2 functions
     return the ``final'' result of executing the expression or statement.
     The `interpretive' attribute means that the ACL2 functions
     are executable as an interpreter of Leo;
     note that this interpreter is written for clarity and simplicity,
     not for efficiency.")
   (xdoc::p
    "In the absence of static semantic restrictions,
     executing Leo code may not terminate,
     due to recursive function calls.
     Since we want to define a defensive dynamic semantics
     that does not assume any static semantics restrictions,
     we must therefore include limit counters in the ACL2 functions,
     which must always terminate for logical consistency.
     Each mutually recursive ACL2 function takes a limit counter,
     terminates if the counter reaches 0,
     and otherwise it passes a counter decremented by one
     to each recursive call;
     thus, the counter measures the depth of the recursion
     of the ACL2 functions (not of the Leo functions).")
   (xdoc::p
    "An alternative to ensure function termination in ACL2
     could be to maintain a sequence of called functions
     and stop with an error when a recursive function call happens,
     which should therefore let us take into account
     the sequence of called functions when formulating the measure
     to prove the termination of the ACL2 functions.
     However, the limit counters are simpler, and commonly used.
     Furthermore, they will still work if Leo is extended with
     richer loops that are not amenable to simple termination checks
     (although the loops will have to be bounded)
     or with recursion
     (which will have to be bounded).")
   (xdoc::p
    "At some point we may also formalize a small-step operational semantics,
     and formally prove it equivalent to the big step one.
     In a small-step operational semantics,
     we must formalize more of the Leo computation state,
     including a notion of how much of an expression or statement
     has been executed vs. must be still executed,
     and describe ``small'' changes to the computation state.
     These steps, chained together, are equivalent to the big steps.")
   (xdoc::p
    "The small-step approach may provide more flexibility
     in formulating and proving properties of interest,
     but it is more complicated, because of the need
     to explicate more of the computation state as described above.
     This is why we use a big-step approach:
     it is easier to formulate,
     and may turn out to be sufficient for many, if not all,
     our verification purposes.")
   (xdoc::p
    "In the current relatively simple version of Leo,
     we could avoid explicating the call stack in the dynamic semantics,
     and instead use ACL2 call stack for that purpose.
     However, explicating the call stack provides more flexibility,
     in particular for future versions of Leo
     that may include references (via @('self'))
     to locations in preceding frames in the call stack."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-variable-value-in-scope ((var identifierp)
                                        (val valuep)
                                        (scope vcscope-dinfop))
  :returns (new-scope vcscope-dinfo-option-resultp)
  :short "Update the value in a variable in a scope."
  :long
  (xdoc::topstring
   (xdoc::p
    "If a variable with the given name is in the scope
     and the new value has the same type as the old value,
     we overwrite the value and return the scope.
     If the types differ, we return an error.
     If a constant with the given name (instead of a variable) is in the scope,
     we return an error.
     If no variable or constant in the scope has the given name,
     we return no scope, but not an error:
     this just means that we must look in another scope."))
  (b* ((info (get-var/const-dinfo-from-scope var scope))
       ((unless info) (vcscope-dinfo-option-none))
       ((var/const-dinfo info) info)
       ((when info.constp) (reserrf (list :update-constant-attempt
                                      (identifier-fix var))))
       ((unless (equal (type-of-value info.value)
                       (type-of-value val)))
        (reserrf (list :mismatch-value-update
                   (identifier-fix var)
                   info.value
                   (value-fix val))))
       (new-info (change-var/const-dinfo info :value (value-fix val)))
       (new-scope (omap::update (identifier-fix var)
                                new-info
                                (vcscope-dinfo-fix scope))))
    (vcscope-dinfo-option-some new-scope))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-variable-value-in-scope-list ((var identifierp)
                                             (val valuep)
                                             (scopes vcscope-dinfo-listp))
  :returns (new-scopes vcscope-dinfo-list-resultp)
  :short "Update the value in a variable in a list of scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return an error if we run out of scopes,
     i.e. if the variable is not found in any scope.
     This is justified by the fact that, when we call this updating function,
     the variable in question is from a location that results from
     the evaluation of an expression,
     and thus the variable must exist and be accessible.
     We plan to incorporate this expected invariant
     into the guard of this updating function."))
  (b* (((when (endp scopes))
        (reserrf (list :no-var-to-update (identifier-fix var))))
       (scope (vcscope-dinfo-fix (car scopes)))
       ((okf new-scope) (update-variable-value-in-scope var val scope))
       ((when (vcscope-dinfo-option-case new-scope :some))
        (cons (vcscope-dinfo-option-some->get new-scope)
              (vcscope-dinfo-list-fix (cdr scopes))))
       ((okf new-scopes)
        (update-variable-value-in-scope-list var val (cdr scopes))))
    (cons scope new-scopes))
  :prepwork
  ((local
    (in-theory
     (enable
      vcscope-dinfo-listp-when-vcscope-dinfo-list-resultp-and-not-reserrp))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-variable-value ((var identifierp) (val valuep) (env denvp))
  :returns (new-env denv-resultp)
  :short "Update the value in a variable in a dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variable must be in the top call frame."))
  (b* ((calls (denv->call-stack env))
       ((when (endp calls)) (reserrf :empty-call-stack))
       (top-call (car calls))
       (scopes (call-dinfo->scopes top-call))
       ((okf new-scopes) (update-variable-value-in-scope-list var val scopes))
       (new-top-call (change-call-dinfo top-call :scopes new-scopes))
       (new-calls (cons new-top-call (cdr calls)))
       (new-env (change-denv env :call-stack new-calls)))
    new-env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-location ((loc locationp) (env denvp))
  :returns (val value-resultp)
  :short "Read the value stored in a location."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the location is a variable, we read its value.
     We retrieve the variable or constant with the given name (if any),
     and we ensure that it is a variable and not a constant;
     this should always be the case,
     for locations obtained by evaluating expressions without error,
     and we plan to formally prove that.")
   (xdoc::p
    "If the location is a tuple or struct component,
     we first read the tuple or struct value,
     then we extract the component."))
  (location-case
   loc
   :var (b* ((var loc.name)
             (info (get-var/const-dinfo var env))
             ((when (not info))
              (reserrf (list :var-not-found var)))
             ((when (var/const-dinfo->constp info))
              (reserrf (list :const-location var))))
          (var/const-dinfo->value info))
   :tuple-comp (b* (((okf tuple) (read-location loc.tuple env)))
                 (op-tuple-read tuple loc.index))
   :struct-comp (b* (((okf struct) (read-location loc.struct env)))
                   (op-struct-read struct loc.name)))
  :measure (location-count loc)
  :verify-guards :after-returns
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-location ((loc locationp) (val valuep) (env denvp))
  :returns (new-env denv-resultp)
  :short "Write a value into a location."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the location is a variable, we update its value.")
   (xdoc::p
    "If the location is a tuple or struct component,
     we read the tuple,
     we update its component,
     and recursively write the value into the enclosing location."))
  (location-case
   loc
   :var (update-variable-value loc.name val env)
   :tuple-comp (b* (((okf tuple) (read-location loc.tuple env))
                    ((okf new-tuple) (op-tuple-write tuple loc.index val)))
                 (write-location loc.tuple new-tuple env))
   :struct-comp (b* (((okf circ) (read-location loc.struct env))
                      ((okf new-circ) (op-struct-write circ loc.name val)))
                   (write-location loc.struct new-circ env)))
  :measure (location-count loc)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define push-call-dinfo ((info call-dinfop) (env denvp))
  :returns (new-env denvp)
  :short "Push information about a call
          onto the call stack of a dynamic environment."
  (b* ((calls (denv->call-stack env))
       (new-calls (cons info calls))
       (new-env (change-denv env :call-stack new-calls)))
    new-env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pop-call-dinfo ((env denvp))
  :returns (new-env denv-resultp)
  :short "Pop information about the top call
          off the call stack of a dynamic environment."
  (b* ((calls (denv->call-stack env))
       ((when (endp calls)) (reserrf :empty-call-stack))
       (new-calls (cdr calls))
       (new-env (change-denv env :call-stack new-calls)))
    new-env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define push-vcscope-dinfo ((scope vcscope-dinfop) (env denvp))
  :returns (new-env denv-resultp)
  :short "Push information about a variable and constant scope
          onto the scope stack of the top call of a dynamic environment."
  (b* ((calls (denv->call-stack env))
       ((when (endp calls)) (reserrf :empty-call-stack))
       (top-call (car calls))
       (scopes (call-dinfo->scopes top-call))
       (new-scopes (cons scope scopes))
       (new-top-call (change-call-dinfo top-call :scopes new-scopes))
       (new-calls (cons new-top-call (cdr calls)))
       (new-env (change-denv env :call-stack new-calls)))
    new-env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pop-vcscope-dinfo ((env denvp))
  :returns (new-env denv-resultp)
  :short "Pop information about a variable and constant scope
          off the scope stack of the top call of a dynamic environment."
  (b* ((calls (denv->call-stack env))
       ((when (endp calls)) (reserrf :empty-call-stack))
       (top-call (car calls))
       (scopes (call-dinfo->scopes top-call))
       ((when (endp scopes)) (reserrf :empty-scope-stack))
       (new-scopes (cdr scopes))
       (new-top-call (change-call-dinfo top-call :scopes new-scopes))
       (new-calls (cons new-top-call (cdr calls)))
       (new-env (change-denv env :call-stack new-calls)))
    new-env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum expr-value
  :short "Fixtype of expression values."
  :long
  (xdoc::topstring
   (xdoc::p
    "An expression evaluates to a location or a value.
     We introduce a notion of expression value
     to capture these two possibliities.")
   (xdoc::p
    "This is a dynamic counterpart of @(tsee expr-type),
     which is used in type checking.")
   (xdoc::p
    "Note that for now we do not capture whether the value is constant
     (i.e. it is obtained by evaluating a constant expression or not).
     We may add that in the future."))
  (:location ((get location)))
  (:value ((get value)))
  :pred expr-valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod evalue+denv
  :short "Fixtype of pairs consisting of
          an expression value and a dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "In general, the execution of an expression
     not only yields an expression value (see @(tsee expr-value),
     but also affects the dynamic environment.
     Actually, this is not quite the case in the current simple version of Leo,
     but it will likely be the case when Leo is extended;
     so we formalize the necessary mathematical structure for right now."))
  ((evalue expr-value)
   (denv denv))
  :tag :evalue+denv
  :pred evalue+denv-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult evalue+denv-result
  :short "Fixtype of errors and pairs consisting of
          an expression value and a dynamic environment."
  :ok evalue+denv
  :pred evalue+denv-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod values+denv
  :short "Fixtype of pairs consisting of
          a list of values and a dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used as the results of lists of expressions,
     which, in the current version of Leo,
     are always evaluated to obtain a list of values (never locations)."))
  ((values value-list)
   (denv denv))
  :tag :values+denv
  :pred values+denv-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult values+denv-result
  :short "Fixtype of errors and pairs consisting of
          a list of values and a dynamic environment."
  :ok values+denv
  :pred values+denv-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod value?+denv
  :short "Fixtype of pairs consisting of
          an optional value and a dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "In general, the execution of a statement may return a value (or not),
     and may affect the dynamic environment,
     by introducing new variables and constants
     and by modifying the content of existing variables.
     This fixtype captures these possible outcomes.")
   (xdoc::p
    "This fixtype is a dynamic counterpart of @(tsee types+senv),
     which is used in type checking.
     In @(tsee types+senv),
     the set of optional types describes many possible optional return values,
     which in this @('value?+denv') fixtype we have just one."))
  ((value? value-option)
   (denv denv))
  :tag :value?+denv
  :pred value?+denv-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult value?+denv-result
  :short "Fixtype of errors and pairs consisting of
          an optional value and a dynamic environment."
  :ok value?+denv
  :pred value?+denv-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod namevalue+denv
  :short "Fixtype of pairs consisting of
          a name-value pair and a dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used as (non-erroneous) results
     of executing struct component initializers."))
  ((namevalue name+value)
   (denv denv))
  :tag :namevalue+denv
  :pred namevalue+denv-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult namevalue+denv-result
  :short "Fixtype of errors and pairs consisting of
          a name-value pair and a dynamic environment."
  :ok namevalue+denv
  :pred namevalue+denv-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod valuemap+denv
  :short "Fixtype of pairs consisting of a value map and a dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used as (non-erroneous) results
     of executing lists of struct component initializers."))
  ((valuemap value-map)
   (denv denv))
  :tag :valuemap+denv
  :pred valuemap+denv-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult valuemap+denv-result
  :short "Fixtype of errors and pairs consisting of
          a value map and a dynamic environment."
  :ok valuemap+denv
  :pred valuemap+denv-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-value-to-value ((eval expr-valuep) (env denvp))
  :returns (val value-resultp)
  :short "Turn an expression value into a value."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee expr-value),
     an expression may evaluate to a location or to a value.
     When the expression is a sub-expression of a larger one,
     in some cases the location and value cases are treated differently,
     but in other cases the value of the expression is needed,
     whether it denotes a value or a location:
     if it denotes a location, the value stored in it is read;
     this way, expressions can be uniformly treated as returning values,
     when needed in the context of certain larger expressions.")
   (xdoc::p
    "This ACL2 function performs this conversion.
     If the expression value is just a value, it is returned.
     If the expression value is a location, the value is read from the location.
     The latter requires a dynamic environment,
     which is an additional parameter of this ACL2 function.")
   (xdoc::p
    "We return an error if the location cannot be read,
     but this should never be the case when we call this ACL2 function.
     We plan to look into formalizing and proving this invariant,
     e.g. via suitable guards."))
  (expr-value-case eval
                   :location (read-location eval.get env)
                   :value eval.get)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-var/const ((name identifierp) (env denvp))
  :returns (evalue+denv evalue+denv-resultp)
  :short "Execute a variable or constant expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is an expression consisting of the name of a variable or constant.
     We attempt to retrieve the variable or constant from the environment.
     If it is a variable, we return its location;
     if it is a constant, we return its value.
     The environment is unchanged."))
  (b* ((info (get-var/const-dinfo name env))
       ((unless info)
        (reserrf (list :var/const-not-found (identifier-fix name))))
       ((var/const-dinfo info) info)
       (eval (if info.constp
                 (expr-value-value info.value)
               (expr-value-location (location-var name)))))
    (make-evalue+denv :evalue eval :denv (denv-fix env)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-literal ((lit literalp) (env denvp))
  :returns (evalue+denv evalue+denv-resultp)
  :short "Execute a literal expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "We evaluate the literal, propagating errors.
     The resulting expression value is a value, not a location.
     The environment is unchanged."))
  (b* ((val (eval-literal lit (denv->curve env)))
       ((unless val) (reserrf (list :eval-literal-failed (literal-fix lit))))
       (eval (expr-value-value val)))
    (make-evalue+denv :evalue eval :denv (denv-fix env)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-unary ((op unopp) (arg expr-valuep) (env denvp))
  :returns (evalue+denv evalue+denv-resultp)
  :short "Execute a unary operator, on an expression value."
  :long
  (xdoc::topstring
   (xdoc::p
    "We coerce the expression value to a value if needed.
     We apply the operator.
     The result is a value.
     The environment is unchanged."))
  (b* (((okf arg) (expr-value-to-value arg env))
       ((okf val)
        (unop-case op
                   :not (op-not arg)
                   :neg (op-neg arg (denv->curve env))
                   :abs (op-abs arg)
                   :abs-wrapped (op-abs-wrapped arg)
                   :double (op-double arg (denv->curve env))
                   :inv (op-inv arg (denv->curve env))
                   :square (op-square arg (denv->curve env))
                   :square-root (op-square-root arg (denv->curve env))))
       (eval (expr-value-value val)))
    (make-evalue+denv :evalue eval :denv (denv-fix env)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-binary ((op binopp)
                     (arg1 expr-valuep)
                     (arg2 expr-valuep)
                     (env denvp))
  :returns (evalue+denv evalue+denv-resultp)
  :short "Execute a binary operator, on two expression values."
  :long
  (xdoc::topstring
   (xdoc::p
    "We coerce the expression values to values if needed.
     We apply the operator.
     The result is a value.
     The environment is unchanged."))
  (b* (((okf arg1) (expr-value-to-value arg1 env))
       ((okf arg2) (expr-value-to-value arg2 env))
       (curve (denv->curve env))
       ((okf val)
        (binop-case op
                    :and (op-and arg1 arg2)
                    :or (op-or arg1 arg2)
                    :nand (op-nand arg1 arg2)
                    :nor (op-nor arg1 arg2)
                    :eq (op-eq arg1 arg2)
                    :ne (op-ne arg1 arg2)
                    :ge (op-ge arg1 arg2)
                    :gt (op-gt arg1 arg2)
                    :le (op-le arg1 arg2)
                    :lt (op-lt arg1 arg2)
                    :bitxor (op-bitxor arg1 arg2)
                    :bitior (op-bitior arg1 arg2)
                    :bitand (op-bitand arg1 arg2)
                    :shl (op-shl arg1 arg2)
                    :shr (op-shr arg1 arg2)
                    :shl-wrapped (op-shl-wrapped arg1 arg2)
                    :shr-wrapped (op-shr-wrapped arg1 arg2)
                    :add (op-add arg1 arg2 curve)
                    :sub (op-sub arg1 arg2 curve)
                    :mul (op-mul arg1 arg2 curve)
                    :div (op-div arg1 arg2 curve)
                    :rem (op-rem arg1 arg2 curve)
                    :pow (op-pow arg1 arg2 curve)
                    :add-wrapped (op-add-wrapped arg1 arg2 curve)
                    :sub-wrapped (op-sub-wrapped arg1 arg2 curve)
                    :mul-wrapped (op-mul-wrapped arg1 arg2 curve)
                    :div-wrapped (op-div-wrapped arg1 arg2 curve)
                    :rem-wrapped (op-rem-wrapped arg1 arg2 curve)
                    :pow-wrapped (op-pow-wrapped arg1 arg2 curve)
                    ))
       (eval (expr-value-value val)))
    (make-evalue+denv :evalue eval :denv (denv-fix env)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ensure-boolean ((test expr-valuep) (env denvp))
  :returns (bool boolean-resultp)
  :short "Ensure that an expression value is a boolean."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used for tests of conditional expressions and statements,
     on the expression value resulting from the test expression.
     We coerce the expression value to a value if needed.
     We check that the value is a boolean,
     in which case we return it."))
  (b* (((okf test) (expr-value-to-value test env))
       ((unless (value-case test :bool))
        (reserrf (list :non-bool-test (value-fix test)))))
    (value-bool->get test))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-vcscope-dinfo-call ((params funparam-listp) (args value-listp))
  :returns (vcscope-info vcscope-dinfo-resultp)
  :short "Initialize the dynamic information about
          a variable and constant scope,
          for a function call."
  :long
  (xdoc::topstring
   (xdoc::p
    "This calculates the initial scope in the frame for the call.
     We go through the parameters of the called function
     and the arguments passed to the call,
     and we ensure they agree in number and types.
     We stop with an error if there are duplicate parameters.")
   (xdoc::p
    "For now we treat public and private parameters as just variables,
     and we treat constant and const parameters as just constants.
     We may extend this in the future."))
  (b* (((when (endp params))
        (if (endp args)
            nil
          (reserrf (list :extra-args (value-list-fix args)))))
       ((when (endp args))
        (reserrf (list :extra-params (funparam-list-fix params))))
       ((funparam param) (car params))
       (arg (car args))
       ((unless (equal (type-of-value arg)
                       param.type))
        (reserrf (list :type-mismatch
                   param.name
                   param.type
                   (value-fix arg))))
       (constp (or (var/const-sort-case param.sort :constant)
                   (var/const-sort-case param.sort :const)))
       (info (make-var/const-dinfo :value arg :constp constp))
       ((okf scope) (init-vcscope-dinfo-call (cdr params) (cdr args)))
       ((when (get-var/const-dinfo-from-scope param.name scope))
        (reserrf (list :duplicate-param param.name)))
       (scope (add-var/const-dinfo-to-scope param.name info scope)))
    scope)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-vcscope-dinfo-loop ((name identifierp) (val valuep))
  :returns (vcscope-info vcscope-dinfop)
  :short "Initialize the dynamic information
          about a variable and constant scope,
          for a loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "This scope consists of just the loop variable,
     which is marked as a constant because,
     due to loop unrolling,
     loop variables are considered constants in the loop bodies."))
  (b* ((info (make-var/const-dinfo :value val :constp t)))
    (omap::update (identifier-fix name) info nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod int+denv
  :short "Fixtype of pairs consisting of
          an integer and a dynamic environment."
  ((int int)
   (denv denv))
  :tag :int+denv
  :pred int+denv-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult int+denv-result
  :short "Fixtype of errors and pairs consisting of
          an integer and a dynamic environment."
  :ok int+denv
  :pred int+denv-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-for-loop ((name identifierp)
                       (type typep)
                       (from expr-valuep)
                       (to expr-valuep)
                       (env denvp))
  :returns (bound+env int+denv-resultp)
  :short "Initialize the execution of a @('for') loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "We ensure that the starting and ending expressions
     both have the declared type for the loop variable,
     which must be an integer type.")
   (xdoc::p
    "We use the starting expression's value to initialize
     a new constant with the name of the loop variable.
     Note that the loop variable is considered a constant
     inside the body of the loop, due to Leo's loop unrolling.
     We push a new scope with that constant.")
   (xdoc::p
    "We return the ending expressions' value, as an ACL2 integers,
     so that it can be used to eventually stop the loop iterations."))
  (b* (((unless (member-eq (type-kind type) '(:unsigned :signed)))
        (reserrf (list :non-integer-loop-var-type (type-fix type))))
       ((okf from) (expr-value-to-value from env))
       ((unless (type-equiv (type-of-value from) type))
        (reserrf (list :mismatched-loop-type
                   :required (type-fix type)
                   :from-value from)))
       ((okf to) (expr-value-to-value to env))
       ((unless (type-equiv (type-of-value to) type))
        (reserrf (list :mismatched-loop-type
                   :required (type-fix type)
                   :from-value from)))
       (scope (init-vcscope-dinfo-loop name from))
       ((okf env) (push-vcscope-dinfo scope env))
       (bound (int-value-to-int to)))
    (make-int+denv :int bound :denv env))
  :guard-hints (("Goal"
                 :in-theory (enable int-valuep)
                 :expand (type-of-value (expr-value-to-value to env))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define end-of-for-loop-p ((name identifierp) (bound integerp) (env denvp))
  :returns (yes/no booleanp)
  :short "Check if a @('for') loop has ended."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in @(tsee exec-for-loop-iterations),
     to check whether the iterations end.
     We retrieve the value of the named loop variable,
     and compare it with the bound:
     the loop has ended if the value is greater than or equal to the bound.
     If the loop variable does not exist, or is not integer,
     we return @('nil');
     however, none of this will ever happen
     in well-formed computation states,
     which we plan to prove formally."))
  (b* ((info (get-var/const-dinfo name env))
       ((unless info) nil)
       (val (var/const-dinfo->value info))
       ((unless (int-valuep val)) nil)
       (int (int-value-to-int val)))
    (>= int (ifix bound)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step-for-loop ((name identifierp) (env denvp))
  :returns (new-env denv-resultp)
  :short "Step the loop variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in @(tsee exec-for-loop-iterations),
     after executing the body of the loop
     and before comparing the stepped variable with the bound.
     As explained in @(tsee init-for-loop),
     the loop variable is actually marked as a constant in the environment.
     Nonetheless, we increment it here,
     because this is automatically incremented at each loop iteration,
     even though its constant status prevents
     the body of the loop from modifying it.")
   (xdoc::p
    "If the variable does not exist
     or is not an integer
     or cannot be safely incremented,
     we return an error.
     However, these situations should never arise
     in well-formed computation states,
     which we plan for formally prove."))
  (b* ((info (get-var/const-dinfo name env))
       ((unless info) (reserrf :impossible))
       (val (var/const-dinfo->value info))
       ((unless (int-valuep val)) (reserrf :impossible))
       (int (int-value-to-int val))
       (new-int (1+ int))
       (new-val
        (value-case val
                    :u8 (and (< new-int (expt 2 8))
                             (value-u8 new-int))
                    :u16 (and (< new-int (expt 2 16))
                              (value-u16 new-int))
                    :u32 (and (< new-int (expt 2 32))
                              (value-u32 new-int))
                    :u64 (and (< new-int (expt 2 64))
                              (value-u64 new-int))
                    :u128 (and (< new-int (expt 2 128))
                               (value-u128 new-int))
                    :i8 (and (< new-int (expt 2 7))
                             (value-i8 new-int))
                    :i16 (and (< new-int (expt 2 15))
                              (value-i16 new-int))
                    :i32 (and (< new-int (expt 2 31))
                              (value-i32 new-int))
                    :i64 (and (< new-int (expt 2 63))
                              (value-i64 new-int))
                    :i128 (and (< new-int (expt 2 127))
                               (value-i128 new-int))
                    :bool (impossible)
                    :address (impossible)
                    :field (impossible)
                    :group (impossible)
                    :scalar (impossible)
                    :string (impossible)
                    :tuple (impossible)
                    :struct (impossible)))
       ((unless new-val) (reserrf :impossible))
       (new-info (make-var/const-dinfo :value new-val :constp t))
       (env (update-var/const-dinfo name new-info env))
       ((unless env) (reserrf :impossible)))
    env)
  :guard-hints (("Goal" :in-theory (enable int-value-to-int
                                           int-valuep
                                           ubyte8p
                                           ubyte16p
                                           ubyte32p
                                           ubyte64p
                                           ubyte128p
                                           sbyte8p
                                           sbyte16p
                                           sbyte32p
                                           sbyte64p
                                           sbyte128p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-print ((message screen-messagep) (env denvp))
  :returns (new-env denvp)
  :short "Execute the printing of a message on the screen."
  (b* ((screen (denv->screen env))
       (new-screen (print-message-to-screen message screen))
       (new-env (change-denv env :screen new-screen)))
    new-env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines exec-expressions/statements
  :short "Execute expressions and statements."

  (define exec-expression ((expr expressionp) (env denvp) (limit natp))
    :returns (evalue+denv evalue+denv-resultp)
    :parents (execution exec-expressions/statements)
    :short "Execute an expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "We use separate ACL2 functions for variables and constants,
       and for literals.")
     (xdoc::p
      "For unary and binary expressions, first we execute the operand(s).
       For binary expressions,
       we execute them from left to right,
       threading through the environment.
       We propagate errors from the operand(s).
       We use separate ACL2 functions to calculate the final result.")
     (xdoc::p
      "For a conditional expression, we first execute the test,
       which must return a boolean.
       If the boolean is true, we execute the `then' branch;
       if the boolean is false, we execute the `else' branch.")
     (xdoc::p
      "For a tuple expression, we first evaluate the sub-expressions,
       then put them together into a tuple value.")
     (xdoc::p
      "For a tuple component expression, we first evaluate the sub-expression.
       If the result is a location, we return a location for the component.
       If the result is a value, we ensure that it is a tuple value,
       and we return the component value (if the index is in range).")
     (xdoc::p
      "For a struct expression,
       we evaluate its components,
       and we create a struct value from them.")
     (xdoc::p
      "For a struct component expression, we first evaluate the sub-expression.
       If the result is a location, we return a location for the component.
       If the result is a value, we ensure that it is a struct value,
       and we return the component value
       (if the component is among the declared ones for the struct type).")
     (xdoc::p
      "For a fucntion call, we first evaluate the argument expressions.
       Then we call a separate ACL2 function to handle the call."))
    (b* (((when (zp limit)) (reserrf :limit)))
      (expression-case
       expr
       :literal
       (exec-literal expr.get env)
       :var/const
       (exec-var/const expr.name env)
       :assoc-const
       (reserrf :todo)
       :unary
       (b* (((when (and (unop-case expr.op :neg)
                        (equal expr.arg
                               (expression-literal
                                (make-literal-signed :val (expt 2 7)
                                                     :size (bitsize-8))))))
             (make-evalue+denv
              :evalue (expr-value-value (value-i8 (- (expt 2 7))))
              :denv env))
            ((when (and (unop-case expr.op :neg)
                        (equal expr.arg
                               (expression-literal
                                (make-literal-signed :val (expt 2 15)
                                                     :size (bitsize-16))))))
             (make-evalue+denv
              :evalue (expr-value-value (value-i16 (- (expt 2 15))))
              :denv env))
            ((when (and (unop-case expr.op :neg)
                        (equal expr.arg
                               (expression-literal
                                (make-literal-signed :val (expt 2 31)
                                                     :size (bitsize-32))))))
             (make-evalue+denv
              :evalue (expr-value-value (value-i32 (- (expt 2 31))))
              :denv env))
            ((when (and (unop-case expr.op :neg)
                        (equal expr.arg
                               (expression-literal
                                (make-literal-signed :val (expt 2 63)
                                                     :size (bitsize-64))))))
             (make-evalue+denv
              :evalue (expr-value-value (value-i64 (- (expt 2 63))))
              :denv env))
            ((when (and (unop-case expr.op :neg)
                        (equal expr.arg
                               (expression-literal
                                (make-literal-signed :val (expt 2 127)
                                                     :size (bitsize-128))))))
             (make-evalue+denv
              :evalue (expr-value-value (value-i128 (- (expt 2 127))))
              :denv env))
            ((okf arg+denv) (exec-expression expr.arg env (1- limit)))
            ((evalue+denv arg+denv) arg+denv)
            (arg arg+denv.evalue)
            (env arg+denv.denv))
         (exec-unary expr.op arg env))
       :binary
       (b* (((okf arg1+denv) (exec-expression expr.arg1 env (1- limit)))
            ((evalue+denv arg1+denv) arg1+denv)
            (arg1 arg1+denv.evalue)
            (env arg1+denv.denv)
            ((okf arg2+denv) (exec-expression expr.arg2 env (1- limit)))
            ((evalue+denv arg2+denv) arg2+denv)
            (arg2 arg2+denv.evalue)
            (env arg2+denv.denv))
         (exec-binary expr.op arg1 arg2 env))
       :cond
       (b* (((okf test+denv) (exec-expression expr.test env (1- limit)))
            ((evalue+denv test+denv) test+denv)
            (test test+denv.evalue)
            (env test+denv.denv)
            ((okf test) (ensure-boolean test env)))
         (if test
             (exec-expression expr.then env (1- limit))
           (exec-expression expr.else env (1- limit))))
       :unit
       (make-evalue+denv :evalue (expr-value-value (op-tuple-make nil))
                         :denv env)
       :tuple
       (b* (((okf vals+env)
             (exec-expression-list expr.components env (1- limit)))
            (vals (values+denv->values vals+env))
            (env (values+denv->denv vals+env))
            (val (op-tuple-make vals))
            (eval (expr-value-value val)))
         (make-evalue+denv :evalue eval :denv env))
       :tuple-component
       (b* (((okf eval+env) (exec-expression expr.tuple env (1- limit)))
            (eval (evalue+denv->evalue eval+env))
            (env (evalue+denv->denv eval+env)))
         (expr-value-case
          eval
          :location (make-evalue+denv
                     :evalue (expr-value-location
                              (make-location-tuple-comp :tuple eval.get
                                                        :index expr.index))
                     :denv env)
          :value (b* (((okf comp) (op-tuple-read eval.get expr.index)))
                   (make-evalue+denv
                    :evalue (expr-value-value comp)
                    :denv env))))
       :struct
       (b* (((okf valmap+env)
             (exec-struct-init-list expr.components env (1- limit)))
            (valmap (valuemap+denv->valuemap valmap+env))
            (env (valuemap+denv->denv valmap+env))
            ((okf val)
             (op-struct-make expr.type valmap (denv->structs env)))
            (eval (expr-value-value val)))
         (make-evalue+denv :evalue eval :denv env))
       :struct-component
       (b* (((okf eval+env) (exec-expression expr.struct env (1- limit)))
            (eval (evalue+denv->evalue eval+env))
            (env (evalue+denv->denv eval+env)))
         (expr-value-case
          eval
          :location (make-evalue+denv
                     :evalue (expr-value-location
                              (make-location-struct-comp :struct eval.get
                                                          :name expr.component))
                     :denv env)
          :value (b* (((okf comp) (op-struct-read eval.get expr.component)))
                   (make-evalue+denv
                    :evalue (expr-value-value comp)
                    :denv env))))
       :internal-call
       (b* (((okf vals+denv) (exec-expression-list expr.args env (1- limit)))
            ((values+denv vals+denv) vals+denv)
            (vals vals+denv.values)
            (env vals+denv.denv))
         (exec-function expr.fun vals env (1- limit)))
       :external-call
       (reserrf :todo)
       :static-call
       (reserrf :todo)))
    :measure (nfix limit))

  (define exec-expression-list ((exprs expression-listp)
                                (env denvp)
                                (limit natp))
    :returns (values+denv values+denv-resultp)
    :parents (execution exec-expressions/statements)
    :short "Execute a list of expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "The expressions are executed one after the other,
       threading the environment through
       and stopping as soon as there is an error."))
    (b* (((when (zp limit)) (reserrf :limit))
         ((when (endp exprs))
          (make-values+denv :values nil :denv (denv-fix env)))
         ((okf eval+denv) (exec-expression (car exprs) env (1- limit)))
         ((evalue+denv eval+denv) eval+denv)
         (eval eval+denv.evalue)
         (env eval+denv.denv)
         ((okf val) (expr-value-to-value eval env))
         ((okf vals+denv) (exec-expression-list (cdr exprs) env (1- limit)))
         ((values+denv vals+denv) vals+denv)
         (vals vals+denv.values)
         (env vals+denv.denv))
      (make-values+denv :values (cons val vals) :denv env))
    :measure (nfix limit))

  (define exec-struct-init ((init struct-initp) (env denvp) (limit natp))
    :returns (nameval+env namevalue+denv-resultp)
    :parents (execution exec-expressions/statements)
    :short "Execute a struct component initializer."
    :long
    (xdoc::topstring
     (xdoc::p
      "We execute the underlying expression,
       obtaining a value and a possibly updated environment,
       and we lift the value to a name-value pair."))
    (b* (((when (zp limit)) (reserrf :limit))
         ((okf eval+env)
          (exec-expression (struct-init->expr init) env (1- limit)))
         (eval (evalue+denv->evalue eval+env))
         (env (evalue+denv->denv eval+env))
         ((okf val) (expr-value-to-value eval env))
         (nameval (make-name+value :name (struct-init->name init)
                                   :value val)))
      (make-namevalue+denv :namevalue nameval :denv env))
    :measure (nfix limit))

  (define exec-struct-init-list ((inits struct-init-listp)
                                  (env denvp)
                                  (limit natp))
    :returns (valmap+env valuemap+denv-resultp)
    :parents (execution exec-expressions/statements)
    :short "Execute a list of struct component initializers."
    :long
    (xdoc::topstring
     (xdoc::p
      "We execute each component initializer,
       accumulating them in a value map.
       It is an error if there is a duplicate component name."))
    (b* (((when (zp limit)) (reserrf :limit))
         ((when (endp inits))
          (make-valuemap+denv :valuemap nil :denv (denv-fix env)))
         ((okf nameval+env) (exec-struct-init (car inits) env (1- limit)))
         (nameval (namevalue+denv->namevalue nameval+env))
         (env (namevalue+denv->denv nameval+env))
         (name (name+value->name nameval))
         (val (name+value->value nameval))
         ((okf valmap+env) (exec-struct-init-list (cdr inits) env (1- limit)))
         (valmap (valuemap+denv->valuemap valmap+env))
         (env (valuemap+denv->denv valmap+env))
         ((when (consp (omap::assoc name valmap)))
          (reserrf (list :duplicate-component name)))
         (valmap (omap::update name val valmap)))
      (make-valuemap+denv :valuemap valmap :denv env))
    :measure (nfix limit))

  (define exec-function ((fun identifierp)
                         (args value-listp)
                         (env denvp)
                         (limit natp))
    :returns (evalue+denv evalue+denv-resultp)
    :parents (execution exec-expressions/statements)
    :short "Execute a function call."
    :long
    (xdoc::topstring
     (xdoc::p
      "We look up the function in the environment.
       We build an initial variable and constant scope
       with the function's parameters and arguments,
       and we put that into a call frame,
       which we push onto the environment's call stack.
       We execute the body of the function,
       ensuring it returns a value with the function's output type;
       we return that value, after popping the frame."))
    (b* (((when (zp limit)) (reserrf :limit))
         (finfo (get-function-dinfo fun (denv->functions env)))
         ((unless finfo) (reserrf (list :function-not-found (identifier-fix fun))))
         ((function-dinfo finfo) finfo)
         ((okf scope) (init-vcscope-dinfo-call finfo.inputs args))
         (frame (make-call-dinfo :fun fun :scopes (list scope)))
         (env (push-call-dinfo frame env))
         ((okf val?+env) (exec-statement-list finfo.body env (1- limit)))
         (val? (value?+denv->value? val?+env))
         (env (value?+denv->denv val?+env))
         ((unless val?) (reserrf (list :no-value-returned (identifier-fix fun))))
         ((unless (equal (type-of-value val?)
                         finfo.output))
          (reserrf (list :return-type-mismatch
                     :required finfo.output
                     :returned val?)))
         ((okf env) (pop-call-dinfo env)))
      (make-evalue+denv :evalue (expr-value-value val?)
                        :denv env))
    :measure (nfix limit))

  (define exec-statement ((stmt statementp) (env denvp) (limit natp))
    :returns (value?+denv value?+denv-resultp)
    :parents (execution exec-expressions/statements)
    :short "Execute a statement."
    :long
    (xdoc::topstring
     (xdoc::p
      "A variable or constant declaration is executed
       by first evaluating the initializing expression,
       then ensuring that it has the type of the variable or constant,
       and finally adding it to the environment.
       We return no value.")
     (xdoc::p
      "For an assignment, we evaluate both expressions,
       ensuring that the first one returns a location.
       We update the location with a value,
       which also ensures that
       the new value has the same type as the old value.
       We return no value")
     (xdoc::p
      "For a return statement, we evaluate the expression,
       and return its value as the return value of the statement.")
     (xdoc::p
      "For a loop statement,
       we first evaluate the starting and ending exxpressions.
       Then we initialize the loop, via @(tsee init-for-loop),
       by adding a scope with the loop counter
       and obtaining the loop bound (i.e. the ending value).
       The loop iterations are executed by @(tsee exec-for-loop-iterations).")
     (xdoc::p
      "A console assertion statement is executed by evaluating the expression,
       and ensuring that it is a boolean.
       If the boolean is false, we stop with an assertion error.
       Otherwise we proceed: a console assertion statement returns no value.")
     (xdoc::p
      "A console print statement is executed by evaluating the expressions,
       and then printing the message on the screen.
       This kind of statement returns no value."))
    (b* (((when (zp limit)) (reserrf :limit)))
      (statement-case
       stmt
       :let
       (b* (((vardecl decl) stmt.get)
            ((okf eval+env) (exec-expression decl.init env (1- limit)))
            (env (evalue+denv->denv eval+env))
            ((okf val) (expr-value-to-value (evalue+denv->evalue eval+env) env))
            ((unless (equal (type-of-value val) decl.type))
             (reserrf (list :let-mismatch
                        :required decl.type
                        :supplied val)))
            (info (make-var/const-dinfo :value val :constp nil))
            (env (add-var/const-dinfo decl.name info env))
            ((unless env) (reserrf (list :variable-exists decl.name))))
         (make-value?+denv :value? nil :denv env))
       :const
       (b* (((constdecl decl) stmt.get)
            ((okf eval+env) (exec-expression decl.init env (1- limit)))
            (env (evalue+denv->denv eval+env))
            ((okf val) (expr-value-to-value (evalue+denv->evalue eval+env) env))
            ((unless (equal (type-of-value val) decl.type))
             (reserrf (list :let-mismatch
                        :required decl.type
                        :supplied val)))
            (info (make-var/const-dinfo :value val :constp t))
            (env (add-var/const-dinfo decl.name info env))
            ((unless env) (reserrf (list :variable-exists decl.name))))
         (make-value?+denv :value? nil :denv env))
       :assign
       (b* (((okf left+env) (exec-expression stmt.left env (1- limit)))
            (left (evalue+denv->evalue left+env))
            (env (evalue+denv->denv left+env))
            ((unless (expr-value-case left :location))
             (reserrf (list :assignment-to-non-location left)))
            (loc (expr-value-location->get left))
            ((okf right+env) (exec-expression stmt.right env (1- limit)))
            (right (evalue+denv->evalue right+env))
            (env (evalue+denv->denv right+env))
            ((okf right) (expr-value-to-value right env))
            ((okf env) (write-location loc right env)))
         (make-value?+denv :value? nil :denv env))
       :return
       (b* (((okf val+env) (exec-expression stmt.value env (1- limit)))
            (val (evalue+denv->evalue val+env))
            (env (evalue+denv->denv val+env))
            ((okf val) (expr-value-to-value val env)))
         (make-value?+denv :value? val :denv env))
       :for
       (b* (((okf from+env) (exec-expression stmt.from env (1- limit)))
            (from (evalue+denv->evalue from+env))
            (env (evalue+denv->denv from+env))
            ((okf to+env) (exec-expression stmt.to env (1- limit)))
            (to (evalue+denv->evalue to+env))
            (env (evalue+denv->denv to+env))
            ((okf bound+env) (init-for-loop stmt.name stmt.type from to env))
            (bound (int+denv->int bound+env))
            (env (int+denv->denv bound+env)))
         (exec-for-loop-iterations stmt.name bound stmt.body env (1- limit)))
       :if
       (exec-if stmt.branches stmt.else env (1- limit))
       :console
       (console-case
        stmt.get
        :assert
        (b* (((okf test+env) (exec-expression stmt.get.arg env (1- limit)))
             (test (evalue+denv->evalue test+env))
             (env (evalue+denv->denv test+env))
             ((okf test) (ensure-boolean test env)))
          (if test
              (make-value?+denv :value? nil :denv env)
            (reserrf (list :assert-fail stmt.get.arg))))
        :error
        (b* (((okf vals+env)
              (exec-expression-list stmt.get.exprs env (1- limit)))
             (vals (values+denv->values vals+env))
             (env (values+denv->denv vals+env))
             (msg (make-screen-message-error :string stmt.get.string
                                             :values vals))
             (env (exec-print msg env)))
          (make-value?+denv :value? nil :denv env))
        :log
        (b* (((okf vals+env)
              (exec-expression-list stmt.get.exprs env (1- limit)))
             (vals (values+denv->values vals+env))
             (env (values+denv->denv vals+env))
             (msg (make-screen-message-log :string stmt.get.string
                                           :values vals))
             (env (exec-print msg env)))
          (make-value?+denv :value? nil :denv env)))
       ;; TODO: the next three
       :finalize (reserrf :execution-of-finalize-statement-not-yet-implemented)
       :increment (reserrf :execution-of-increment-statement-not-yet-implemented)
       :decrement (reserrf :execution-of-decrement-statement-not-yet-implemented)
       :block
       (exec-block stmt.get env (1- limit))))
    :measure (nfix limit))

  (define exec-statement-list ((stmts statement-listp) (env denvp) (limit natp))
    :returns (value?+denv value?+denv-resultp)
    :parents (execution exec-expressions/statements)
    :short "Execute a list of statements."
    :long
    (xdoc::topstring
     (xdoc::p
      "If the list is empty,
       we return no value and leave the environment unchanged.
       Otherwise, we execute the first statement,
       propagating any errors.
       If the statement returns a value, we return that value,
       and we do not execute the remaining statements.
       Otherwise, we proceed to execute the remaining statements."))
    (b* (((when (zp limit)) (reserrf :limit))
         ((when (endp stmts))
          (make-value?+denv :value? nil :denv (denv-fix env)))
         ((okf val?+env) (exec-statement (car stmts) env (1- limit)))
         (val? (value?+denv->value? val?+env))
         (env (value?+denv->denv val?+env))
         ((when val?) (make-value?+denv :value? val? :denv env)))
      (exec-statement-list (cdr stmts) env (1- limit)))
    :measure (nfix limit))

  (define exec-block ((stmts statement-listp) (env denvp) (limit natp))
    :returns (val?+denv value?+denv-resultp)
    :parents (execution exec-expressions/statements)
    :short "Execute a block."
    :long
    (xdoc::topstring
     (xdoc::p
      "The block consists of a list of statements,
       which are supplied to this ACL2 function.
       We first push a new empty scope for variables and constants;
       then we execute the statements,
       propagating any return value.
       If there is no return value, we pop the scope we pushed before."))
    (b* (((when (zp limit)) (reserrf :limit))
         ((okf env) (push-vcscope-dinfo nil env))
         ((okf val?+env) (exec-statement-list stmts env (1- limit)))
         (val? (value?+denv->value? val?+env))
         (env (value?+denv->denv val?+env))
         ((when val?) (make-value?+denv :value? val? :denv env))
         ((okf env) (pop-vcscope-dinfo env)))
      (make-value?+denv :value? nil :denv env))
    :measure (nfix limit))

  (define exec-for-loop-iterations ((name identifierp)
                                    (bound integerp)
                                    (body statement-listp)
                                    (env denvp)
                                    (limit natp))
    :returns (value?+denv value?+denv-resultp)
    :parents (execution exec-expressions/statements)
    :short "Execute the iterations of a @('for') loop."
    :long
    (xdoc::topstring
     (xdoc::p
      "We first check whether the loop has ended, with a separate ACL2 function.
       If it does, we pop the top scope;
       note that this top scope contains exactly the loop counter,
       initially pushed by @(tsee init-for-loop),
       and preserved by @(tsee exec-block).
       Besides popping this top scope, we return no value,
       because the loop has ended without returning a value.
       If the loop has not ended, we execute the loop body as a block.
       Note that this immediately pushes a new scope for the block,
       which is why the preceding scope, as noted above,
       only contains the loop counter.
       It would be a mistake to not push a new scope here,
       because the loop may declare new variables and constants
       at each iteration.
       If the loop body returns a value, we return  it and end the loop.
       Otherwise, we increment the loop counter,
       and recursively call this ACL2 function to loop back."))
    (b* (((when (zp limit)) (reserrf :limit))
         ((when (end-of-for-loop-p name bound env))
          (b* (((okf env) (pop-vcscope-dinfo env)))
            (make-value?+denv :value? nil :denv env)))
         ((okf val?+env) (exec-block body env (1- limit)))
         (val? (value?+denv->value? val?+env))
         (env (value?+denv->denv val?+env))
         ((when val?) (make-value?+denv :value? val? :denv env))
         ((okf env) (step-for-loop name env)))
      (exec-for-loop-iterations name bound body env (1- limit)))
    :measure (nfix limit))

  (define exec-if ((branches branch-listp)
                   (else statement-listp)
                   (env denvp)
                   (limit natp))
    :returns (value?+denv value?+denv-resultp)
    :parents (execution exec-expressions/statements)
    :short "Execute the constituents of a conditional statement."
    :long
    (xdoc::topstring
     (xdoc::p
      "The constituents are a list of branches and a default block.
       We go through the branches.
       For each, we execute the test of the branch:
       if it succeeds, we execute the block and the branch
       and return the result;
       if it succeeds, we examine the next branch in the same way.
       If we run out of branches, we execute the default block."))
    (b* (((when (zp limit)) (reserrf :limit))
         ((when (endp branches)) (exec-block else env (1- limit)))
         ((branch branch) (car branches))
         ((okf test+env) (exec-expression branch.test env (1- limit)))
         (test (evalue+denv->evalue test+env))
         (env (evalue+denv->denv test+env))
         ((okf test) (ensure-boolean test env))
         ((when test) (exec-block branch.body env (1- limit))))
      (exec-if (cdr branches) else env (1- limit)))
    :measure (nfix limit))

  :verify-guards nil ; done below
  ///
  (verify-guards exec-expression)

  (fty::deffixequiv-mutual exec-expressions/statements
    :hints (("Goal" :in-theory (disable ifix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define extend-denv-with-fundecl ((decl fundeclp) (env denvp))
  :returns (new-env denv-resultp)
  :short "Extend a dynamic environment with a function declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "Information about the function
     is added to the dynamic function environment,
     unless a function with that name is already present."))
  (b* (((fundecl decl) decl)
       (info (make-function-dinfo :inputs decl.inputs
                                  :output decl.output
                                  :body decl.body))
       (fenv (denv->functions env))
       (new-fenv (add-function-dinfo decl.name info fenv))
       ((when (function-denv-option-case new-fenv :none))
        (reserrf (list :duplicate-function decl.name)))
       (new-fenv (function-denv-option-some->get new-fenv))
       (new-env (change-denv env :functions new-fenv)))
    new-env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define extend-denv-with-structdecl ((decl structdeclp) (env denvp))
  :returns (new-env denv-resultp)
  :short "Extend a dynamic environment with a struct declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "Information about the struct type
     is added to the dynamic struct environment,
     unless a struct type with that name is already present."))
  (b* (((structdecl decl) decl)
       ((okf comps)
        (extend-type-map-with-compdecl-list decl.components nil))
       (info (make-struct-dinfo :components comps))
       (cenv (denv->structs env))
       (new-cenv (add-struct-dinfo decl.name info cenv))
       ((when (struct-denv-option-case new-cenv :none))
        (reserrf (list :duplicate-struct decl.name)))
       (new-cenv (struct-denv-option-some->get new-cenv))
       (new-env (change-denv env :structs new-cenv)))
    new-env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define extend-denv-with-topdecl ((decl topdeclp) (env denvp))
  :returns (new-env denv-resultp)
  :short "Extend a dynamic environment with a top-level declaration."
  (topdecl-case decl
                :function (extend-denv-with-fundecl decl.get env)
                :struct (extend-denv-with-structdecl decl.get env)
                ;; TODO: fix :mapping
                :mapping (reserrf :extend-denv-for-mapping-not-yet-implemented))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define extend-denv-with-topdecl-list ((decls topdecl-listp) (env denvp))
  :returns (new-env denv-resultp)
  :short "Extend a dynamic environment with a list of top-level declarations."
  (b* (((when (endp decls)) (denv-fix env))
       ((okf env) (extend-denv-with-topdecl (car decls) env)))
    (extend-denv-with-topdecl-list (cdr decls) env))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define build-denv-from-file ((file filep) (curve curvep))
  :returns (env denv-resultp)
  :short "Build a dynamic environment from a file."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the initial dynamic environment used for executing a program.")
   (xdoc::p
    "Besides the file, we also need the prime and the curve."))
  ;; TODO: consider imports
  (extend-denv-with-topdecl-list (programdecl->items (file->program file))
                                 (init-denv curve))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-file-main ((file filep)
                        (args value-listp)
                        (curve curvep)
                        (limit natp))
  :returns (result value-resultp)
  :short "Execute the @('main') function of a file."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides the file, we supply the argument values,
     as well as the prime and the curve;
     we also need to supply a limit for the execution functions.
     The limit could be so large that it never runs out in practice
     (if the Leo code terminates).
     In the future, we may be able to calculate automatically
     a sufficiently large limit
     that suffices to execute the program to completion.")
   (xdoc::p
    "We construct the dynamic environment from the file,
     and then we use the execution (ACL2) function for (Leo) functions,
     which takes values as arguments.")
   (xdoc::p
    "The final result is either a value or an error.
     This error may be any that happens in execution,
     including not finding the @('main') function,
     if the file does not have one."))
  (b* (((okf env) (build-denv-from-file file curve))
       ((okf val+env) (exec-function (identifier "main") args env limit))
       (val (evalue+denv->evalue val+env))
       (env (evalue+denv->denv val+env)))
    (expr-value-to-value val env))
  :prepwork ((local (in-theory (disable nfix))))
  :hooks (:fix))
