; Java Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "clause-processors/pseudo-term-fty" :dir :system)
(include-book "kestrel/std/system/all-vars-open" :dir :system)
(include-book "kestrel/std/system/dumb-occur-var-open" :dir :system)
(include-book "std/lists/repeat" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation-var-reuse
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          marking of reusable lambda-bound variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "Consider a function body of the form")
   (xdoc::codeblock
    "(let ((x ...))"
    "  (let ((x ...))"
    "    (f x)))")
   (xdoc::p
    "The second @('x') bound by @(tsee let)
     ``overwrites'' the first one completely,
     because in the rest of the term (namely, @('(f x)'))
     only the second one is referenced, not the first one.")
   (xdoc::p
    "In contrast, consider a function body of the form")
   (xdoc::codeblock
    "(let ((x ...))"
    "  (f (let ((x ...)) (f x)) (g x)))")
   (xdoc::p
    "Here, the second @('x') bound by @(tsee let)
     ``overwrites'' the second one only partially, namely in @('(f x)'),
     but other parts of the rest of the term, namely @('(g x)'),
     reference the first one.")
   (xdoc::p
    "When we translate ACL2 to Java,
     @(tsee let)-bound variables become Java local variables.
     In the first example above,
     provided that the two @('x') variables have the same type,
     the Java code can use the same local variable for both:
     for the first binding, the Java code declares and initializes the variable;
     for the second binding, the Java code assigns to the variable,
     destructively updating it,
     which is safe because the old value is no longer needed.
     However, in the second example above,
     there have to be two distinct Java local variables,
     say @('x1') and @('x2'),
     corresponding to the two bound variables:
     both are declared and initialized,
     none can be safely destructively updated.")
   (xdoc::p
    "This pre-translation step analyzes terms
     to find out which lambda-bound (i.e. @(tsee let)-bound) variables
     can be reused and destructively updated.
     The lambda-bound variables are marked as either `new' or `old':
     the first marking means that
     the variable must be a new Java local variable
     that is declared and initilized;
     the second marking means that
     the variable can be an old Java local variable
     that is destructively assigned.
     These markings provide ``instructions'' to the ACL2-to-Java translation.")
   (xdoc::p
    "In the first example above the markings would be")
   (xdoc::codeblock
    "(let (([n]x ...))"
    "  (let (([o]x ...))"
    "    (f [o]x)))")
   (xdoc::p
    "while in the second example above the markings would be")
   (xdoc::codeblock
    "(let (([n]x ...))"
    "  (f (let (([n]x ...)) (f [n]x)) (g [n]x)))")
   (xdoc::p
    "Note that, as we mark the lambda-bound variables,
     we must mark in the same way the occurrences in the lambda bodies,
     to maintain the well-formedness of the ACL2 terms.")
   (xdoc::p
    "This pre-translation step must be performed after the "
    (xdoc::seetopic "atj-pre-translation-type-annotation"
                    "type annotation step")
    ", so that types are kept into account:
      a variable can be reused only if
      it has the same type in both lambda formal parameters.
      Since the type annotation step adds types to variable names,
      by comparing names for equality we also compare their types for equality.
      If two variables have different types,
      they also have different names (since the name includes the type).")
   (xdoc::p
    "After this translation step, the "
    (xdoc::seetopic "atj-pre-translation-var-renaming"
                    "variable renaming step")
    " takes care of renaming apart ACL2 variables with the same name
      that are both marked as `new'."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-mark-var-new ((var symbolp))
  :returns (marked-var symbolp)
  :short "Mark a variable as `new'."
  (packn-pos (list "[N]" var) var))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-mark-vars-new ((vars symbol-listp))
  :returns (marked-vars symbol-listp)
  :short "Lift @(tsee atj-mark-var-new) to lists."
  (cond ((endp vars) nil)
        (t (cons (atj-mark-var-new (car vars))
                 (atj-mark-vars-new (cdr vars)))))
  ///

  (defret len-of-atj-mark-vars-new
    (equal (len marked-vars)
           (len vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-mark-var-old ((var symbolp))
  :returns (marked-var symbolp)
  :short "Mark a variable as `old'."
  (packn-pos (list "[O]" var) var))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-unmark-var ((var symbolp))
  :returns (mv (unmarked-var symbolp)
               (new? booleanp))
  :short "Decompose a marked variable into its marking and its unmarked name."
  :long
  (xdoc::topstring
   (xdoc::p
    "The marking is a boolean: @('t') for `new', @('nil') for `old'."))
  (b* ((string (symbol-name var))
       ((unless (and (>= (length string) 5)
                     (member-equal (subseq string 0 3) '("[N]" "[O]"))))
        (raise "Internal error: ~x0 has the wrong format." var)
        (mv nil nil))
       (new? (eql (char string 1) #\N))
       (unmarked-string (subseq string 3 (length string)))
       (unmarked-var (intern-in-package-of-symbol unmarked-string var)))
    (mv unmarked-var new?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-unmark-vars ((vars symbol-listp))
  :returns (mv (unmarked-vars symbol-listp)
               (new?s boolean-listp))
  :short "Lift @(tsee atj-unmark-var) to lists."
  (b* (((when (endp vars)) (mv nil nil))
       ((mv var new?) (atj-unmark-var (car vars)))
       ((mv vars new?s) (atj-unmark-vars (cdr vars))))
    (mv (cons var vars) (cons new? new?s)))
  ///

  (defret len-of-atj-unmark-vars.unmarked-vars
    (equal (len unmarked-vars)
           (len vars)))

  (defret len-of-atj-unmark-vars.new?s
    (equal (len new?s)
           (len vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-vars-in-jexpr
  :short "Variables that will occur in the Java expression
          generated from an ACL2 term."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     each Java term is translated to a Java expression
     preceded by a Java block (which may be empty or not).
     The block is non-empty when the term involves
     lambda expressions, which become local variable assignments in Java,
     and @(tsee if) calls, which become @('if') statements in Java.
     As detailed below, some of the variables in the ACL2 term
     will occur (as corresponding Java variables) in the Java expression;
     while others will only occur in the Java block.
     The ones that will occur in the Java expression
     are important for the correct marking of variables.
     This function returns the ACL2 variables in a term
     (as a set represented as a list without duplicates)
     that will occur in the Java expression generated from the term.")
   (xdoc::p
    "A quoted constant has no variables,
     and is always translated to a Java expression without variables.
     Thus, we return @('nil') (i.e. the empty list of variables) in this case.")
   (xdoc::p
    "An ACL2 variable is translated to a corresponding variable in Java,
     and thus in this case we return the singleton list of the variable.")
   (xdoc::p
    "An @(tsee if) call is translated to a block with an @('if') statement
     that performs all the evaluations of the test and branches,
     and the resulting Java expression is just a single fresh Java variable
     that has no counterpart in the ACL2 term.
     Thus, in this case we return @('nil') (the empty list of variables).")
   (xdoc::p
    "A call of a named function different from @(tsee if) is translated
     to an expression that has subexpressions obtained by translating
     the arguments of the ACL2 function call.
     The expression is often a method call,
     with the subexpressions being its actual arguments,
     but it may also be an expression involving a Java operator (e.g. @('+'))
     with the subexpressions as operands.
     Thus, in this case we return the union of the variables
     recursively computed for the argument terms.")
   (xdoc::p
    "A call of a lamda expression is translated to
     a Java block that assigns expressions to local variables
     that correspond to the formal parameters of the lambda expression,
     and to a Java expression obtained by translating
     the body of the lambda expression.
     Thus, in this case we return the variables
     recursively computed for the body of the lambda expression."))

  (define atj-vars-in-jexpr ((term pseudo-termp))
    :returns (vars symbol-listp)
    (pseudo-term-case term
                      :null (raise "Internal error: null term.")
                      :quote nil
                      :var (list term.name)
                      :fncall (if (eq term.fn 'if)
                                  (list nil)
                                (atj-vars-in-jexpr-list term.args))
                      :lambda (atj-vars-in-jexpr term.body))
    :measure (pseudo-term-count term))

  (define atj-vars-in-jexpr-list ((terms pseudo-term-listp))
    :returns (vars symbol-listp)
    (cond ((endp terms) nil)
          (t (union-eq (atj-vars-in-jexpr (car terms))
                       (atj-vars-in-jexpr-list (cdr terms)))))
    :measure (pseudo-term-list-count terms))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-vars-in-jexpr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-mark-term
  :short "Mark the variables in a term as `new' or `old'."
  :long
  (xdoc::topstring
   (xdoc::p
    "Marking a variable as `new' is always ``safe'',
     because it is always safe to introduce a new Java local variable.
     On the other hand, marking a variable as `old' requires care,
     to prevent a Java local variable to be erroneously reused.
     To understand this marking algorithm,
     one has to keep in mind how ACL2 terms are translated to Java:
     see @(tsee atj-gen-shallow-term) and companions.
     This is a delicate algorithm:
     a proof of correctness would be very beneficial.")
   (xdoc::p
    "Two conditions are necessary for reusing a variable:
     (i) the variable must be in scope (i.e. exist and be accessible); and
     (ii) the previous value of the variable must not be used afterwards.
     The parameters @('vars-in-scope') and @('vars-used-after')
     support the checking of these conditions.")
   (xdoc::p
    "The parameter @('vars-in-scope') consists of the variables in scope
     at the point where the term under consideration occurs.
     At the top level (see @(tsee atj-mark-formals+body)),
     it is intialized with the (unmarked) formal parameters
     of the ACL2 function whose formal parameters and body are being marked:
     indeed, the formal parameters of a function are in scope for the body.
     As we descend into subterms, when we encounter a lambda expression,
     we extend @('vars-in-scope') with its (unmarked) formal parameters;
     only the ones that are marked as `new' actually extend the scope,
     while the ones marked as `old' were already in @('vars-in-scope').
     The generated Java code evaluates functions' actual arguments
     left-to-right:
     thus, local variables introduced (for lambda expressions in) an argument
     are generally (see exception shortly) in scope for successive arguments.
     Therefore, @('vars-in-scope') is threaded through the marking functions
     (i.e. passed as argument and returned, possibly updated, as result).
     When processing a lambda expression applied to arguments,
     @('vars-in-scope') is threaded first through the arguments,
     and then through the body (which is evaluated after the arguments),
     after augmenting it with the formal parameters.
     The exception mentioned above is for @(tsee if),
     which is turned into a Java @('if')
     whose branches are Java blocks:
     Java variables declared inside these blocks
     have a more limited scope (namely, the respective block),
     and therefore should not be added to the @('vars-in-scope')
     that is passed to mark terms after the @(tsee if).
     The variables introduced in the test of the @(tsee if)
     are declared outside the branches' blocks,
     and so they are threaded through.
     The @('vars-in-scope') resulting from marking the test of the @(tsee if)
     is passed to mark both branches,
     but their returned @('vars-in-scope') is ignored.
     The code for @(tsee if) is a bit more complicated
     because of the special treatment of @('(if a a b)') terms,
     which are treated as @('(or a b)'):
     the Java code generated for this case is a little different
     (see @(tsee atj-gen-shallow-or-call)),
     but the treatment of @('vars-in-scope')
     is essentially the same as just explained
     (there is no `then' branch to mark, because it is the same as the test,
     which has already been marked).")
   (xdoc::p
    "The parameter @('vars-used-after') consists of the variables
     whose current values are used ``after'' the term under consideration.
     At the top level (see @(tsee atj-mark-formals+body)),
     this is initialized with @('nil'),
     because no variables are used after evaluating the body of the function.
     As we descend into subterms,
     @('vars-used-after') is extended as needed,
     based on the ``neighboring'' subterms
     that will be evaluated (in the generated Java code)
     after the subterm under consideration.
     In particular, when marking an actual argument of a function call,
     @('vars-used-after') is extended with all the free variables
     of the actual arguments of the same function call
     that occur after the one being marked;
     recall that arguments are evaluated left-to-right
     in the generated Java code.
     The function @('atj-mark-terms'),
     which is used to mark the actual arguments of a function call,
     augments @('vars-used-after') with the free variables
     in the @(tsee cdr) of the current list of arguments;
     this is somewhat inefficient,
     as the same free variables are collected repeatedly
     as the argument terms are processed,
     but terms are not expected to be too large in the near future;
     this may be eventually optimized when needed.
     Furthermore, as we traverse the arguments of a function call,
     we augment the used variables with the ones that will occur
     in the Java expressions generated for the preceding arguments;
     see @(tsee atj-vars-in-jexpr).")
   (xdoc::p
    "Calls of @(tsee if) are treated a little differently,
     because the arguments are not evaluated left-to-right
     in the generated Java code:
     when marking the test, we augment @('vars-used-after')
     with all the free variables in the branches;
     when marking either branch, we use the same @('vars-used-after')
     that was passed for the @(tsee if),
     because the two branches are independent.
     The @(tsee or) form of @(tsee if) is treated slightly differently as usual,
     but the essence is the same.
     Unlike @('vars-in-scope'), @('var-used-after') is not threaded through;
     it is simply passed down, and augmented as needed.")
   (xdoc::p
    "The body of a lambda expression is evaluated after its actual arguments:
     thus, when marking the actual arguments of a lambda expression
     we must augment @('vars-used-after')
     with the free variables of the lambda expression,
     i.e. the free variables in the body minus the formal parameters.")
   (xdoc::p
    "As we mark the formal parameters of a lambda expression,
     we need to mark in the same way
     all the references to these variables in the body of the lambda expression.
     For this purpose, we pass around a mapping, @('vars-to-mark-new'),
     from (unmarked) variables to markings:
     this could be an alist from symbols to booleans,
     but we isomorphically use lists (treated as sets) of symbols instead,
     which are the variable marked as `new',
     while the variables not in the list are marked as `old'.
     When the term to be marked is a variable,
     we look it up in this list, and mark it accordingly.")
   (xdoc::p
    "When the term to be marked is a quoted constant,
     it is obviously left unchanged.")
   (xdoc::p
    "When the term to be marked is a function call,
     we first treat the @(tsee if) (and @(tsee or)) case separately.
     We mark the test, and after that the two branches.
     The handling of @('vars-in-scope') and @('vars-used-after') for this case
     has been explained above.")
   (xdoc::p
    "For all other function calls, which are strict,
     we first mark the actual arguments,
     treating @('vars-in-scope') and @('vars-used-after')
     as explained above.
     For calls of named functions, we are done at this point:
     we put the named function in front of the marked arguments and return.
     For calls of lambda expression,
     we use the auxiliary function @('atj-mark-lambda-formals')
     to decide which formal parameters should be marked as `new' or `old'.
     We mark the parameter as `old' (indicating that the variable can be reused)
     iff the following three conditions hold.
     The first condition is that the variable must be in scope;
     note that variables have already been annotated with types at this point,
     and so by testing variable names we also test their types,
     which is needed for Java
     (i.e. we could not reuse a Java variable of type @('Acl2Symbol')
     to store a value of type @('Acl2String')).
     The second condition is that the variable is not used
     after the lambda call term, i.e. it is not in @('vars-used-after'):
     otherwise, we would overwrite something that was supposed to be used later,
     with incorrect results in general.
     The third condition is that the variable is not free
     in any of the actual arguments that correspond to
     the formal parameters of the lambda expression
     that come just after the one being marked:
     this is because, in the generated Java code,
     the lambda variables are assigned one after the other,
     and therefore we should not overwrite a variable
     that may be needed afterwards.
     For instance, consider a swap @('(let ((x y) (y x)) ...)'):
     @('x') cannot be reused
     (even if it is in scope and not used after the @(tsee let))
     because it must be assigned to @('y') after @('y') is assigned to @('x')
     (Java does not support parallel assignment);
     on the other hand, @('y') could be reused,
     if it is in scope and not used after the @(tsee let),
     because at the time of assigning to @('y')
     its (previous) value has already been assigned to @('x').")
   (xdoc::p
    "When analyzing the arguments of a call of a lambda expression,
     we need to extend @('vars-used-after') with
     the free variables in the lambda expression
     (i.e. the free variables in the body minus the formal arguments).
     This is because the body of the lambda expression
     is evaluated after the arguments of the call.
     We store the extended list into @('vars-used-after-args').
     But when we process the body of the lambda expression after that,
     we go back to using @('vars-used-after'),
     which excludes the variables used in the lambda expression,
     and only includes the variables used
     after the call of the lambda expression."))

  (define atj-mark-term ((term pseudo-termp)
                         (vars-in-scope symbol-listp)
                         (vars-used-after symbol-listp)
                         (vars-to-mark-new symbol-listp))
    :returns (mv (marked-term pseudo-termp)
                 (new-vars-in-scope symbol-listp))
    (b* (((unless (mbt (pseudo-termp term))) (mv nil nil))
         ((unless (mbt (symbol-listp vars-in-scope))) (mv nil nil))
         ((unless (mbt (symbol-listp vars-used-after))) (mv nil nil))
         ((unless (mbt (symbol-listp vars-to-mark-new))) (mv nil nil))
         ((when (variablep term))
          (if (member-eq term vars-to-mark-new)
              (mv (atj-mark-var-new term) vars-in-scope)
            (mv (atj-mark-var-old term) vars-in-scope)))
         ((when (fquotep term)) (mv term vars-in-scope))
         (fn (ffn-symb term))
         ((when (eq fn 'if))
          (b* ((test (fargn term 1))
               (then (fargn term 2))
               (else (fargn term 3)))
            (if (equal test then)
                (b* ((vars-used-after-test (union-eq vars-used-after
                                                     (all-vars-open else)))
                     ((mv test
                          vars-in-scope) (atj-mark-term test
                                                        vars-in-scope
                                                        vars-used-after-test
                                                        vars-to-mark-new))
                     ((mv else &) (atj-mark-term else
                                                 vars-in-scope
                                                 vars-used-after
                                                 vars-to-mark-new)))
                  (mv `(if ,test ,test ,else)
                      vars-in-scope))
              (b* ((vars-used-after-test (union-eq vars-used-after
                                                   (all-vars-open-lst
                                                    (list then else))))
                   ((mv test
                        vars-in-scope) (atj-mark-term test
                                                      vars-in-scope
                                                      vars-used-after-test
                                                      vars-to-mark-new))
                   ((mv then &) (atj-mark-term then
                                               vars-in-scope
                                               vars-used-after
                                               vars-to-mark-new))
                   ((mv else &) (atj-mark-term else
                                               vars-in-scope
                                               vars-used-after
                                               vars-to-mark-new)))
                (mv `(if ,test ,then ,else)
                    vars-in-scope)))))
         (args (fargs term))
         (vars-used-after-args
          (if (symbolp fn)
              vars-used-after
            (union-eq vars-used-after
                      (set-difference-eq (all-vars-open (lambda-body fn))
                                         (lambda-formals fn)))))
         ((mv marked-args vars-in-scope) (atj-mark-terms args
                                                         vars-in-scope
                                                         vars-used-after-args
                                                         nil
                                                         vars-to-mark-new))
         ((when (symbolp fn)) (mv (fcons-term fn marked-args)
                                  vars-in-scope))
         (formals (lambda-formals fn))
         ((mv marked-formals
              vars-to-mark-new) (atj-mark-lambda-formals formals
                                                         args
                                                         vars-in-scope
                                                         vars-used-after
                                                         vars-to-mark-new))
         (vars-in-scope (union-eq formals vars-in-scope))
         ((mv marked-body
              vars-in-scope) (atj-mark-term (lambda-body fn)
                                            vars-in-scope
                                            vars-used-after
                                            vars-to-mark-new)))
      (mv (fcons-term (make-lambda marked-formals marked-body)
                      marked-args)
          vars-in-scope)))

  (define atj-mark-terms ((terms pseudo-term-listp)
                          (vars-in-scope symbol-listp)
                          (vars-used-after symbol-listp)
                          (vars-used-in-jexprs symbol-listp)
                          (vars-to-mark-new symbol-listp))
    :returns (mv (marked-terms (and (pseudo-term-listp marked-terms)
                                    (equal (len marked-terms)
                                           (len terms))))
                 (new-vars-in-scope symbol-listp))
    (b* (((unless (mbt (pseudo-term-listp terms)))
          (mv (repeat (len terms) nil) nil))
         ((unless (mbt (symbol-listp vars-in-scope)))
          (mv (repeat (len terms) nil) nil))
         ((unless (mbt (symbol-listp vars-used-after)))
          (mv (repeat (len terms) nil) nil))
         ((unless (mbt (symbol-listp vars-to-mark-new)))
          (mv (repeat (len terms) nil) nil))
         ((when (endp terms)) (mv nil vars-in-scope))
         (first-term (car terms))
         (rest-terms (cdr terms))
         (vars-used-after-first-term (union-eq vars-used-after
                                               (all-vars-open-lst rest-terms)))
         ((mv marked-first-term
              vars-in-scope)
          (atj-mark-term first-term
                         vars-in-scope
                         (union-eq vars-used-after-first-term
                                   vars-used-in-jexprs)
                         vars-to-mark-new))
         ((mv marked-rest-terms
              vars-in-scope)
          (atj-mark-terms rest-terms
                          vars-in-scope
                          vars-used-after
                          (union-eq vars-used-in-jexprs
                                    (atj-vars-in-jexpr first-term))
                          vars-to-mark-new)))
      (mv (cons marked-first-term marked-rest-terms)
          vars-in-scope)))

  :prepwork

  ((local (include-book "std/typed-lists/symbol-listp" :dir :system))

   (define atj-mark-lambda-formals ((formals symbol-listp)
                                    (actuals pseudo-term-listp)
                                    (vars-in-scope symbol-listp)
                                    (vars-used-after symbol-listp)
                                    (vars-to-mark-new symbol-listp))
     :guard (= (len formals) (len actuals))
     :returns (mv (marked-formals (and (symbol-listp marked-formals)
                                       (equal (len marked-formals)
                                              (len formals))))
                  (new-vars-to-mark-new
                   symbol-listp
                   :hyp (and (symbol-listp formals)
                             (symbol-listp vars-to-mark-new))))
     (b* (((when (endp formals)) (mv nil vars-to-mark-new))
          (formal (car formals))
          (new? (or (not (member-eq formal vars-in-scope))
                    (member-eq formal vars-used-after)
                    (dumb-occur-var-open-lst formal (cdr actuals))))
          (marked-formal (if new?
                             (atj-mark-var-new formal)
                           (atj-mark-var-old formal)))
          (vars-to-mark-new (if new?
                                (cons formal vars-to-mark-new)
                              (remove-eq formal vars-to-mark-new)))
          ((mv marked-formals
               vars-to-mark-new) (atj-mark-lambda-formals (cdr formals)
                                                          (cdr actuals)
                                                          vars-in-scope
                                                          vars-used-after
                                                          vars-to-mark-new)))
       (mv (cons marked-formal marked-formals)
           vars-to-mark-new))
     ///

     (more-returns
      (marked-formals true-listp :rule-classes :type-prescription)
      (new-vars-to-mark-new true-listp
                            :hyp (true-listp vars-to-mark-new)
                            :rule-classes :type-prescription))

     (defret len-of-atj-mark-lambda-formals.marked-formals
       (equal (len marked-formals)
              (len formals)))))

  :verify-guards nil ; done below

  ///

  (defrulel true-listp-when-symbol-listp
    (implies (symbol-listp x)
             (true-listp x)))

  (verify-guards atj-mark-term))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-mark-formals+body ((formals symbol-listp) (body pseudo-termp))
  :returns (mv (new-formals symbol-listp)
               (new-body pseudo-termp :hyp :guard))
  :short "Mark all the variables
          in the formal parameters and body of an ACL2 function definition
          as `new' or `old'"
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top level of the marking algorithm;
     this top level is discussed in @(tsee atj-mark-term)."))
  (b* ((marked-formals (atj-mark-vars-new formals))
       ((mv marked-body &) (atj-mark-term body formals nil formals)))
    (mv marked-formals marked-body))
  ///

  (defret len-of-atj-mark-formals+body.new-formals
    (equal (len new-formals)
           (len formals))))
