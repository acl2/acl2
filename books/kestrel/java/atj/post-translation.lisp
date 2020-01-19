; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "java-syntax-operations")

(include-book "centaur/depgraph/toposort" :dir :system)
(include-book "std/lists/index-of" :dir :system)
(include-book "std/strings/decimal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-post-translation
  :parents (atj-code-generation)
  :short "Post-translation performed by ATJ, as part of code generation."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned in "
    (xdoc::seetopic "atj-post-translation" "here")
    ", after translating ACL2 to Java,
     ATJ performs a Java-to-Java post-translation.
     Currently, this post-translation consists of the following steps.
     These steps only apply to the shallow embedding approach.")
   (xdoc::ol
    (xdoc::li
     "We fold @('return') statements into @('if') branches.
      See "
     (xdoc::seetopic "atj-post-translation-fold-returns" "here")
     ".")
    (xdoc::li
     "We eliminate tail recursions, replacing them with loops.
      See "
     (xdoc::seetopic "atj-post-translation-tailrec-elimination" "here")
     ".")
    (xdoc::li
     "We lift tests from conditionals to loops.
      See "
     (xdoc::seetopic "atj-post-translation-lift-loop-tests" "here")
     ".")
    (xdoc::li
     "We eliminate unnecessary @('continue')s from loops.
      See "
     (xdoc::seetopic "atj-post-translation-remove-continue" "here")
     ".")))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-post-translation-fold-returns
  :parents (atj-post-translation)
  :short "Post-translation step:
          folding of @('return')s into @('if')s."
  :long
  (xdoc::topstring
   (xdoc::p
    "ATJ's ACL2-to-Java translation
     introduces a Java local variable for every @(tsee if) in ACL2:
     the variable is assigned in the `then' and `else' branches,
     and then used in subsequent Java code.
     When the subsequent Java code is simply a @('return'),
     the body of a Java method would look like this:")
   (xdoc::codeblock
    "..."
    "<type> <result> = null;"
    "if (...) {"
    "    ..."
    "    <result> = <then>;"
    "} else {"
    "    ..."
    "    <result> = <else>;"
    "}"
    "return <result>;")
   (xdoc::p
    "This post-translation step folds the @('return') into the @('if'),
     turning this code into the following form:")
   (xdoc::codeblock
    "..."
    "if (...) {"
    "    ..."
    "    return <then>;"
    "} else {"
    "    ..."
    "    return <else>;"
    "}")
   (xdoc::p
    "In fact, it does so recursively:
     if the new `then' and/or `else' branch has the same form as above
     (i.e. @('<then>') and/or @('<else>') is a result variable
     introduced for a nested @('if')),
     we keep folding @('return')s into @('if')s.")
   (xdoc::p
    "The function @(tsee atj-gen-shallow-fndef-method),
     which translates an ACL2 function to a Java method,
     always produces a method body that ends with a single @('return').
     This post-translation step may replace that single @('return')
     with a number of @('return')s, inside different conditional branches.
     This is more readable and idiomatic Java code."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-check-foldable-return ((block jblockp))
  :returns (mv (yes/no booleanp)
               (pre-block jblockp :hyp :guard)
               (test-expr jexprp)
               (then-block jblockp)
               (then-expr jexprp)
               (else-block jblockp)
               (else-expr jexprp))
  :short "Check if a Java block has an ending @('return')
          that is foldable into an immediately preceding @('if')."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check whether the block has the structure described "
    (xdoc::seetopic "atj-post-translation-fold-returns" "here")
    ". If it does, we return its components, i.e.
     the block that precedes the declaration of the result variable,
     the `then' block without the final assignment to the result variable,
     the expression assigned to the result variable in the `then' block,
     the `else' block without the final assignment to the result variable,
     and the expression assigned to the result variable in the `else' block.")
   (xdoc::p
    "If the first result of this function is @('nil'),
     the other results have irrelevant values.")
   (xdoc::p
    "We prove that, if the first result is @('t'),
     the @('then-block') and @('else-block') results
     have strictly fewer @('if')s than the input block.
     This is used to prove the termination of @(tsee atj-fold-returns),
     which processes those blocks recursively."))
  (b* (((fun (fail))
        (mv nil nil (jexpr-name "") nil (jexpr-name "") nil (jexpr-name "")))
       ((unless (>= (len block) 3)) (fail))
       (pre-block (butlast block 3))
       (rest-block (nthcdr (len pre-block) block))
       (3rd-to-last-statem (car rest-block))
       (2nd-to-last-statem (cadr rest-block))
       (last-statem (caddr rest-block))
       ((unless (jstatem-case last-statem :return)) (fail))
       (return-expr? (jstatem-return->expr? last-statem))
       ((when (null return-expr?)) (fail))
       (return-expr return-expr?)
       ((unless (jexpr-case return-expr :name)) (fail))
       (result-var (jexpr-name->get return-expr))
       ((unless (jstatem-case 2nd-to-last-statem :ifelse)) (fail))
       (test-expr (jstatem-ifelse->test 2nd-to-last-statem))
       (then+asg-block (jstatem-ifelse->then 2nd-to-last-statem))
       (else+asg-block (jstatem-ifelse->else 2nd-to-last-statem))
       ((unless (and (consp then+asg-block)
                     (consp else+asg-block))) (fail))
       (then-block (butlast then+asg-block 1))
       (else-block (butlast else+asg-block 1))
       (then-asg (car (last then+asg-block)))
       (else-asg (car (last else+asg-block)))
       ((unless (and (jstatem-case then-asg :expr)
                     (jstatem-case else-asg :expr))) (fail))
       (then-asg (jstatem-expr->get then-asg))
       (else-asg (jstatem-expr->get else-asg))
       ((unless (and (jexpr-case then-asg :binary)
                     (jexpr-case else-asg :binary)
                     (jbinop-case (jexpr-binary->op then-asg) :asg)
                     (jbinop-case (jexpr-binary->op else-asg) :asg)
                     (equal (jexpr-binary->left then-asg)
                            (jexpr-name result-var))
                     (equal (jexpr-binary->left else-asg)
                            (jexpr-name result-var)))) (fail))
       (then-expr (jexpr-binary->right then-asg))
       (else-expr (jexpr-binary->right else-asg))
       ((unless (jstatem-case 3rd-to-last-statem :locvar)) (fail))
       (locvar (jstatem-locvar->get 3rd-to-last-statem))
       ((unless (and (equal (jlocvar->name locvar)
                            result-var)
                     (equal (jlocvar->init? locvar)
                            nil))) (fail)))
    (mv t pre-block test-expr then-block then-expr else-block else-expr))

  ///

  (defruledl lemma
    (implies (mv-nth 0 (atj-check-foldable-return block))
             (jstatem-case (nth (- (len block) 2) block) :ifelse)))

  (defret atj-check-foldable-return-then-decreases
    :hyp (mv-nth 0 (atj-check-foldable-return block))
    (< (jblock-count-ifs then-block)
       (jblock-count-ifs block))
    :rule-classes :linear
    :hints(("Goal" :use (lemma
                         (:instance jblock-count-ifs-positive-when-nth-ifelse
                          (i (- (len block) 2)))))))

  (defret atj-check-foldable-return-else-decreases
    :hyp (mv-nth 0 (atj-check-foldable-return block))
    (< (jblock-count-ifs else-block)
       (jblock-count-ifs block))
    :rule-classes :linear
    :hints(("Goal" :use (lemma
                         (:instance jblock-count-ifs-positive-when-nth-ifelse
                          (i (- (len block) 2))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-fold-returns ((block jblockp))
  :returns (new-block jblockp :hyp :guard)
  :verify-guards :after-returns
  :short "Fold @('return')s into @('if')s in a Java block."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the block ends with the pattern described "
    (xdoc::seetopic "atj-post-translation-fold-returns" "here")
    ", we replace it with the equivalent code also described "
    (xdoc::seetopic "atj-post-translation-fold-returns" "here")
    ", recursively."))
  (b* (((mv matchp
            pre-block
            test-expr
            then-block
            then-expr
            else-block
            else-expr) (atj-check-foldable-return block))
       ((unless matchp) block)
       (then-return (jstatem-return then-expr))
       (else-return (jstatem-return else-expr))
       (new-then-block (append then-block (list then-return)))
       (new-else-block (append else-block (list else-return)))
       (new-then-block (atj-fold-returns new-then-block))
       (new-else-block (atj-fold-returns new-else-block))
       (if-block (list
                  (jstatem-ifelse test-expr new-then-block new-else-block)))
       (new-block (append pre-block if-block)))
    new-block)
  :measure (jblock-count-ifs block))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-post-translation-tailrec-elimination
  :parents (atj-post-translation)
  :short "Post-translation step:
          eliminate tail recursions in favor of loops."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is well-known that tail recursions can be turned into loops;
     this process is often called `tail recursion elimination'.
     This post-translation step does that,
     by surrounding the body of a tail-recursive method
     in a @('while (true) { ... }') loop,
     and replacing each recursive call with a @('continue')
     preceded by an assignment to the method's parameters
     of the values passed to the recursive call.")
   (xdoc::p
    "We remark that the assignment to the method's parameters
     is an instance of destructive updates,
     which is idiomatic in Java.")
   (xdoc::p
    "It seems better to realize this as a post-translation step,
     rather than as part of the ACL2-to-Java translation,
     which is already fairly complicated."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-parallel-asg-depgraph ((vars string-listp)
                                   (exprs jexpr-listp))
  :guard (= (len vars) (len exprs))
  :returns (graph alistp)
  :short "Calculate a dependency graph for a parallel assignment."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since Java does not have parallel assignment,
     in order to assign the expressions @('exprs') to the variables @('vars'),
     we attempt to topologically order these assignments
     according to their dependencies.
     This function calculates the dependency graph,
     in a form suitable for "
    (xdoc::seetopic "depgraph::depgraph" "this dependency graph library")
    ".")
   (xdoc::p
    "We go through the variables in order,
     and for each we construct an association pair
     for the graph represented as an alist.
     For each variable,
     we collect all the variables in the corresponding expression,
     but we exclude the variable itself
     and any variable not in the initial set.
     Thus, we use an auxiliary function that has the unchanging initial set
     as an additional argument."))
  (atj-parallel-asg-depgraph-aux vars exprs vars)

  :prepwork

  ((define atj-parallel-asg-depgraph-aux ((vars string-listp)
                                          (exprs jexpr-listp)
                                          (all-vars string-listp))
     :guard (= (len vars) (len exprs))
     :returns (graph alistp)
     (b* (((when (endp vars)) nil)
          (var (car vars))
          (expr (car exprs))
          (deps (remove-equal var
                              (intersection-equal (jexpr-vars expr)
                                                  all-vars)))
          (rest-alist (atj-parallel-asg-depgraph-aux (cdr vars)
                                                     (cdr exprs)
                                                     all-vars)))
       (acons var deps rest-alist))

     ///

     (defret atj-parallel-asg-depgraph-aux-subsetp-vars
       (subsetp-equal (alist-keys graph) vars)
       :hints (("Goal" :in-theory (enable alist-keys))))))

  ///

  (defret atj-parallel-asg-depgraph-subsetp-vars
    (subsetp-equal (alist-keys graph) vars)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-serialize-parallel-asg ((serialization string-listp)
                                    (vars string-listp)
                                    (exprs jexpr-listp))
  :guard (and (= (len vars) (len exprs))
              (subsetp-equal serialization vars))
  :returns (block jblockp)
  :short "Generate a block that performs a parallel assignment
          of the given expressions to the given variables,
          according to the supplied serialization."
  :long
  (xdoc::topstring
   (xdoc::p
    "When the dependencies in a parallel assignment are not circular,
     it is possible to realize the parallel assignment
     via a sequence of single assignment that respects the dependencies.
     This function does that, based on the given serialization,
     which is calculated elsewhere via a topological sort.")
   (xdoc::p
    "We go through the serialization, and for each element (i.e. variable name)
     we find the position in the @('names') list,
     and use that position to pick the corresponding expression
     to use in the assignment."))
  (b* (((when (endp serialization)) nil)
       (var (car serialization))
       (pos (acl2::index-of var vars))
       (expr (nth pos exprs))
       (first-asg (jblock-asg (jexpr-name var) expr))
       (rest-asg (atj-serialize-parallel-asg (cdr serialization) vars exprs)))
    (append first-asg rest-asg)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-make-parallel-asg ((vars string-listp)
                               (types jtype-listp)
                               (exprs jexpr-listp))
  :guard (and (= (len vars) (len types))
              (= (len types) (len exprs)))
  :returns (block jblockp)
  :short "Generate a block that performs a parallel assignment
          of the given expressions to the given variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in the context of turning tail-recursions into loops,
     but it is more general.")
   (xdoc::p
    "A recursive method call performs, in substance,
     a parallel assignment of the actual arguments to the formal parameters,
     and then proceeds to re-execute the method's body.
     When we turn such a recursive call into a @('continue')
     so that we can re-execute the (loop's) body,
     we first need to assign, to the method's formal parameters,
     the expressions for the actual arguments.
     This function generates that assignment.")
   (xdoc::p
    "As mentioned before, the assignment must be parallel:
     in general we cannot assign the new values in order,
     because earlier assignments may incorrectly change
     the value of expressions for later assignments.
     We first attempt to topologically sort the variables
     according to their dependencies:
     if there are no circularities,
     we perform the assignments in the topological order
     (note that we need to reverse the ordered list
     returned by @(tsee depgraph::toposort),
     which starts with variables that do not depend on other variables,
     and which we must assign last).
     If instead there are circularities,
     for now we use a very simple strategy:
     we create temporary variables for all the method's arguments,
     we initialize them with the expressions,
     and then we assign the temporary variables to the method's parameters.
     This can be improved,
     by reducing the number of temporary variables
     to just where there are circular dependencies.")
   (xdoc::p
    "The temporary variables are called @('$1'), @('$2'), etc.,
     which does not conflict with any other variables
     generated by ATJ's translation.
     Their types are the same as the ones of the method's parameters,
     which are passed to these function along with their names,
     and the expressions to assign.")
   (xdoc::p
    "We use a recursive auxiliary function that produces
     the block with the temporary variable declarations and initializations
     separately from the block with the assignments to the parameters.
     The main function concatenates them into an overall block."))
  (b* ((graph (atj-parallel-asg-depgraph vars exprs))
       ((mv acyclicp serialization) (depgraph::toposort graph))
       ((unless (string-listp serialization))
        (raise "Internal error: ~
                topological sort of graph ~x0 of strings ~
                has generated non-strings ~x1."
               graph serialization))
       (serialization (rev serialization))
       ((when acyclicp) (atj-serialize-parallel-asg serialization vars exprs))
       ((mv tmp-block asg-block)
        (atj-make-parallel-asg-aux vars types exprs 1)))
    (append tmp-block asg-block))

  :prepwork

  ((local (include-book "std/typed-lists/string-listp" :dir :system))

   (define atj-make-parallel-asg-aux ((vars string-listp)
                                      (types jtype-listp)
                                      (exprs jexpr-listp)
                                      (i posp))
     :guard (and (= (len vars) (len types))
                 (= (len types) (len exprs)))
     :returns (mv (tmp-block jblockp)
                  (asg-block jblockp))
     (b* (((when (endp vars)) (mv nil nil))
          (var (car vars))
          (type (car types))
          (expr (car exprs))
          (tmp (str::cat "$" (str::natstr i)))
          (first-tmp (jblock-locvar type tmp expr))
          (first-asg (jblock-asg (jexpr-name var)
                                 (jexpr-name tmp)))
          ((mv rest-tmp
               rest-asg) (atj-make-parallel-asg-aux (cdr vars)
                                                    (cdr types)
                                                    (cdr exprs)
                                                    (1+ i))))
       (mv (append first-tmp rest-tmp)
           (append first-asg rest-asg))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-elim-tailrec-in-jstatems+jblocks
  :short "Eliminate all the tail-recursive calls in a method's
          statement or block."
  :long
  (xdoc::topstring
   (xdoc::p
    "We recursively traverse the statements and blocks
     and replace each call of the given method name
     with a parallel assignment to the method parameters
     followed by a @('continue').")
   (xdoc::p
    "Since we only apply this post-translation step to tail-recursive methods,
     we know that recursive calls may only appear as @('return') expressions;
     otherwise, the call would not be tail-recursive.
     Thus, we only need to look for @('return') statements
     whose expression is a recursive call,
     and replace such statements as outlined above.")
   (xdoc::p
    "Since a single statement may be replaced by a block,
     we systematically turn statements into blocks (often singletons),
     and handle the transformation of blocks appropriately."))

  (define atj-elim-tailrec-in-jstatem ((statem jstatemp)
                                       (method-params jparam-listp)
                                       (method-name stringp))
    :returns (new-block jblockp :hyp (jstatemp statem))
    (jstatem-case
     statem
     :locvar (list statem)
     :expr (list statem)
     :return (if (and (jexprp statem.expr?)
                      (jexpr-case statem.expr? :method)
                      (equal (jexpr-method->name statem.expr?)
                             method-name))
                 (b* ((names (jparam-list->names method-params))
                      (types (jparam-list->types method-params))
                      (exprs (jexpr-method->args statem.expr?))
                      ((unless (= (len names) (len exprs))) ; just for guards
                       (raise "Internal error: ~
                               call of method ~s0 has ~x1 parameters ~
                               but is called with ~x2 arguments."
                              method-name (len names) (len exprs))))
                   (append
                    (atj-make-parallel-asg names types exprs)
                    (jblock-continue)))
               (list statem))
     :throw (list statem)
     :break (list statem)
     :continue (list statem)
     :if (jblock-if statem.test
                    (atj-elim-tailrec-in-jblock statem.then
                                                method-params
                                                method-name))
     :ifelse (jblock-ifelse statem.test
                            (atj-elim-tailrec-in-jblock statem.then
                                                        method-params
                                                        method-name)
                            (atj-elim-tailrec-in-jblock statem.else
                                                        method-params
                                                        method-name))
     :while (jblock-while statem.test
                          (atj-elim-tailrec-in-jblock statem.body
                                                      method-params
                                                      method-name))
     :do (jblock-do (atj-elim-tailrec-in-jblock statem.body
                                                method-params
                                                method-name)
                    statem.test)
     :for (jblock-for statem.init
                      statem.test
                      statem.update
                      (atj-elim-tailrec-in-jblock statem.body
                                                  method-params
                                                  method-name)))
    :measure (jstatem-count statem))

  (define atj-elim-tailrec-in-jblock ((block jblockp)
                                      (method-params jparam-listp)
                                      (method-name stringp))
    :returns (new-block jblockp :hyp (jblockp block))
    (cond ((endp block) nil)
          (t (append (atj-elim-tailrec-in-jstatem (car block)
                                                  method-params
                                                  method-name)
                     (atj-elim-tailrec-in-jblock (cdr block)
                                                 method-params
                                                 method-name))))
    :measure (jblock-count block))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-elim-tailrec-in-jstatem))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-elim-tailrec ((name stringp)
                          (params jparam-listp)
                          (body jblockp))
  :returns (new-block jblockp)
  :short "Turn the body of a tail-recursive method into a loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called only on tail-recursive methods.
     We replace the recursive calls in the block
     and we surround the block with a @('while') loop with test @('true');
     the loop is actually exited when a @('return') is executed.")
   (xdoc::p
    "Under suitable conditions,
     it should be possible to generate more idiomatic @('while') loops,
     with an actual continuation test instead of @('true'),
     and with base cases outside the loop.
     However, the current form always works
     for all possible tail-recursive methods.")
   (xdoc::p
    "Because of the constant @('true') continuation test in the @('while'),
     it is unnecessary to have a dummy @('return') after the loop.
     According to Java's static semantics,
     code after the loop is unreachable."))
  (list (make-jstatem-while
         :test (jexpr-literal-true)
         :body (atj-elim-tailrec-in-jblock body params name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-post-translation-lift-loop-tests
  :parents (atj-post-translation)
  :short "Post-translation step:
          lifting to loop tests."
  :long
  (xdoc::topstring
   (xdoc::p
    "The "
    (xdoc::seetopic "atj-post-translation-tailrec-elimination"
                    "tail recursion elimination step")
    " produces method bodies of the form @('while (true) { ... }').
     When the body of the @('while') is an @('if')
     one of whose branches is a @('return'),
     then it is possible to lift the @('if') tests to the loop test,
     moving the @('return') after the loop.")
   (xdoc::p
    "More precisely, if the method body has the form")
   (xdoc::codeblock
    "while (true) {"
    "    if (<test>) {"
    "        return <expr>;"
    "    } else {"
    "        ..."
    "    }"
    "}")
   (xdoc::p
    "it can be turned into")
   (xdoc::codeblock
    "while (!<test>) {"
    "    ..."
    "}"
    "return <expr>;")
   (xdoc::p
    "Simillarly, if the method body has the form")
   (xdoc::codeblock
    "while (true) {"
    "    if (<test>) {"
    "        ...."
    "    } else {"
    "        return <expr>;"
    "    }"
    "}")
   (xdoc::p
    "it can be turned into")
   (xdoc::codeblock
    "while (<test>) {"
    "    ..."
    "}"
    "return <expr>;")
   (xdoc::p
    "This post-translation step performs these transformations,
     which produce more idiomatic looping code.
     It should be possible to extend the scope of this post-translation step,
     e.g. to cases in which the @('return') is preceded by some statements."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-check-single-return-with-expr ((block jblockp))
  :returns (mv (yes/no booleanp)
               (expr jexprp))
  :short "Check if a Java block consists of
          a single @('return') with an expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the check is successful,
     we return the expression of the @('return').
     If the check is not successful, i.e. the first result is @('nil'),
     the second result is irrelevant."))
  (b* (((fun (fail)) (mv nil (jexpr-name "")))
       ((unless (= (len block) 1)) (fail))
       (statem (car block))
       ((unless (jstatem-case statem :return)) (fail))
       (expr? (jstatem-return->expr? statem))
       ((unless expr?) (fail)))
    (mv t expr?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-check-liftable-loop-test ((block jblockp))
  :returns (mv (yes/no booleanp)
               (test jexprp)
               (return jexprp)
               (body jblockp))
  :short "Check if a Java block is a @('while (true) ...') loop
          with an @('if') body whose test can be lifted to the loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "This checks if a block has one of the two forms described "
    (xdoc::seetopic "atj-post-translation-lift-loop-tests" "here")
    ". If it does, we return its components, i.e.
     the test expression, the return expression,
     and the block that will become the body of the new loop
     (i.e. the `then' or `else' branch that is not a @('return').
     The returned test expression is the one that will become
     the test of the new loop:
     thus, it is either the same as the @('if')
     or its logical negation,
     depending on which branch is the @('return').")
   (xdoc::p
    "If the first result of this function is @('nil'),
     the other results have irrelevant values."))
  (b* (((fun (fail)) (mv nil (jexpr-name "") (jexpr-name "") nil))
       ((unless (= (len block) 1)) (fail))
       (statem (car block))
       ((unless (jstatem-case statem :while)) (fail))
       (while-test (jstatem-while->test statem))
       (while-body (jstatem-while->body statem))
       ((unless (equal while-test (jexpr-literal-true))) (fail))
       ((unless (= (len while-body) 1)) (fail))
       (statem (car while-body))
       ((unless (jstatem-case statem :ifelse)) (fail))
       (test (jstatem-ifelse->test statem))
       (then (jstatem-ifelse->then statem))
       (else (jstatem-ifelse->else statem))
       ((mv then-return-p return) (atj-check-single-return-with-expr then))
       ((when then-return-p) (mv t (negate-boolean-jexpr test) return else))
       ((mv else-return-p return) (atj-check-single-return-with-expr else))
       ((when else-return-p) (mv t test return then)))
    (fail)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-lift-loop-test ((block jblockp))
  :returns (new-block jblockp :hyp :guard)
  :short "Lift an @('if') test to the enclosing loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the block is a loop of the form described "
    (xdoc::seetopic "atj-post-translation-lift-loop-tests" "here")
    ", we transform into the equivalent code also described "
    (xdoc::seetopic "atj-post-translation-lift-loop-tests" "here")
    ". We do it only once, not recursively,
     because ATJ's ACL2-to-Java translation
     currently does not generate nested loops."))
  (b* (((mv matchp test return body) (atj-check-liftable-loop-test block))
       ((unless matchp) block))
    (append (jblock-while test body)
            (jblock-return return))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-post-translation-remove-continue
  :parents (atj-post-translation)
  :short "Post-translation step:
          remove unnecessary @('continue') statements."
  :long
  (xdoc::topstring
   (xdoc::p
    "The "
    (xdoc::seetopic "atj-post-translation-tailrec-elimination"
                    "tail recursion elimination step")
    " produces loops where the recursive calls are replaced with
     @('continue') statements.
     However, when one of these statements
     is the last thing executed in the loop body,
     it is superfluous and can be removed.")
   (xdoc::p
    "This post-translation step performs this removal."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-remove-ending-continue ((block jblockp))
  :returns (new-block jblockp :hyp :guard)
  :verify-guards :after-returns
  :short "Remove any ending @('continue') statements
          from a block that forms a loop body."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called on bodies of loops (which are blocks).
     It removes any ending @('continue'),
     including the ones inside the branches of ending @('if')s,
     recursively.")
   (xdoc::p
    "If the block is empty, we return it unchanged.
     If the block ends with @('continue'),
     we return the block without that last statement.
     If the block ends with @('if') (with or without @('else')),
     we recursively process the branch(es).")
   (xdoc::p
    "We prove that the size of the new block is not greater than
     the size of the original block.
     This is used to prove the termination of
     @(tsee atj-remove-continue-in-jstatem) and
     @(tsee atj-remove-continue-in-jblock)."))
  (b* (((when (endp block)) nil)
       (last-statem (car (last block)))
       (butlast-block (butlast block 1)))
    (case (jstatem-kind last-statem)
      (:continue butlast-block)
      (:if (append butlast-block
                   (list (jstatem-if (jstatem-if->test last-statem)
                                     (atj-remove-ending-continue
                                      (jstatem-if->then last-statem))))))
      (:ifelse (append butlast-block
                       (list
                        (jstatem-ifelse (jstatem-ifelse->test last-statem)
                                        (atj-remove-ending-continue
                                         (jstatem-ifelse->then last-statem))
                                        (atj-remove-ending-continue
                                         (jstatem-ifelse->else last-statem))))))
      (otherwise block)))
  :measure (jblock-count-ifs block)
  ///

  (defruledl atj-remove-ending-continue-does-not-increase-size-lemma-1
    (implies (and (consp block)
                  (jstatem-case (car (last block)) :if))
             (equal (jblock-count block)
                    (+ 4
                       (jblock-count (butlast block 1))
                       (jblock-count (jstatem-if->then (car (last block)))))))
    :enable (jblock-count jstatem-count))

  (defruled atj-remove-ending-continue-does-not-increase-size-lemma-2
    (implies
     (and (consp block)
          (jstatem-case (car (last block)) :ifelse))
     (equal (jblock-count block)
            (+ 5
               (jblock-count (butlast block 1))
               (jblock-count (jstatem-ifelse->then (car (last block))))
               (jblock-count (jstatem-ifelse->else (car (last block)))))))
    :enable (jblock-count jstatem-count))

  (defret atj-remove-ending-continue-does-not-increase-size
    (<= (jblock-count (atj-remove-ending-continue block))
        (jblock-count block))
    :rule-classes :linear
    :hints (("Goal" :in-theory (e/d (atj-remove-ending-continue
                                     jblock-count
                                     jstatem-count)
                                    (butlast)))
            '(:use
              (atj-remove-ending-continue-does-not-increase-size-lemma-1
               atj-remove-ending-continue-does-not-increase-size-lemma-2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-remove-continue-in-jstatems+jblocks
  :short "Remove the ending @('continue') statements
          in all the loops found in statements and blocks."
  :long
  (xdoc::topstring
   (xdoc::p
    "We recursively process all the statements and blocks.
     When we encounter a loop,
     we use @(tsee atj-remove-ending-continue)
     to remove all its ending @('continue')s (if any),
     and then we recursively process the resulting body
     in order to remove @('continue')s from any nested loops.")
   (xdoc::p
    "Currently ATJ's ACL2-to-Java translation does not generate nested loops,
     and none of ATJ's post-translation steps generates nested loops.
     However, making this post-translation step more general
     require only little additional effort."))

  (define atj-remove-continue-in-jstatem ((statem jstatemp))
    :returns (new-statem jstatemp :hyp :guard)
    (jstatem-case
     statem
     :locvar statem
     :expr statem
     :return statem
     :throw statem
     :break statem
     :continue statem
     :if (jstatem-if statem.test
                     (atj-remove-continue-in-jblock statem.then))
     :ifelse (jstatem-ifelse statem.test
                             (atj-remove-continue-in-jblock statem.then)
                             (atj-remove-continue-in-jblock statem.else))
     :while (b* ((body (atj-remove-ending-continue statem.body)))
              (jstatem-while statem.test
                             (atj-remove-continue-in-jblock body)))
     :do (b* ((body (atj-remove-ending-continue statem.body)))
           (jstatem-do (atj-remove-continue-in-jblock body)
                       statem.test))
     :for (b* ((body (atj-remove-ending-continue statem.body)))
            (jstatem-for statem.init
                         statem.test
                         statem.update
                         (atj-remove-continue-in-jblock body))))
    :measure (jstatem-count statem))

  (define atj-remove-continue-in-jblock ((block jblockp))
    :returns (new-block jblockp :hyp :guard)
    (cond ((endp block) nil)
          (t (cons (atj-remove-continue-in-jstatem (car block))
                   (atj-remove-continue-in-jblock (cdr block)))))
    :measure (jblock-count block))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-remove-continue-in-jstatem))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-post-translate ((name stringp)
                            (params jparam-listp)
                            (body jblockp)
                            (tailrecp booleanp))
  :returns (new-body jblockp :hyp :guard)
  :parents (atj-post-translation)
  :short "Post-translate a Java method body generated from an ACL2 function."
  :long
  (xdoc::topstring
   (xdoc::p
    "We always fold @('return')s into @('if')s.")
   (xdoc::p
    "If the method is tail-recursive,
     which is signaled by the @('tailrecp') flag,
     then we replace the tail recursion with a loop.
     It is critical that this step is performed
     after folding @('return')s into @('if')s,
     because tail recursion elimination
     looks for recursive calls in @('return')s.")
   (xdoc::p
    "More post-translation steps could be added, and applied here,
     in the future."))
  (b* ((body (atj-fold-returns body))
       (body (if tailrecp
                 (atj-elim-tailrec name params body)
               body))
       (body (atj-lift-loop-test body))
       (body (atj-remove-continue-in-jblock body)))
    body))
