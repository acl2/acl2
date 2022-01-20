; Java Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "../java-syntax-operations")

(include-book "centaur/depgraph/toposort" :dir :system)
(include-book "std/lists/index-of" :dir :system)

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
     :parents nil
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
     we find the position in the @('vars') list,
     and use that position to pick the corresponding expression
     to use in the assignment.")
   (xdoc::p
    "We exclude trivial assignments of a variable to itself.
     These arise when formal arguments of tail-recursive ACL2 functions
     are passed unchanged as actual arguments to the recursive calls."))
  (b* (((when (endp serialization)) nil)
       (var (car serialization))
       (pos (acl2::index-of var vars))
       (expr (nth pos exprs))
       ((when (jexpr-equiv expr (jexpr-name var)))
        (atj-serialize-parallel-asg (cdr serialization) vars exprs))
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
     :parents nil
     (b* (((when (endp vars)) (mv nil nil))
          (var (car vars))
          (type (car types))
          (expr (car exprs))
          (tmp (str::cat "$" (str::nat-to-dec-string i)))
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

(define atj-elim-tailrec-gen-block ((arg-exprs jexpr-listp)
                                    (method-params jparam-listp))
  :returns (block jblockp)
  :short "Generate the block for eliminating tail recursion."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called by @(tsee atj-elim-tailrec-in-return).
     When we encounter a tail-recursive call of the method
     in a @('return') statement,
     we generate a block consisting of
     (1) a parallel assignment of the call's actual arguments
     to the method's parameters, and
     (2) a @('continue') statement."))
  (b* ((names (jparam-list->names method-params))
       (types (jparam-list->types method-params))
       ((unless (= (len names) (len arg-exprs))) ; just for guards
        (raise "Internal error: ~
                call of tail-recursive method has ~x0 parameters ~
                but is called with ~x1 arguments."
               (len names) (len arg-exprs))))
    (append
     (atj-make-parallel-asg names types arg-exprs)
     (jblock-continue))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-elim-tailrec-in-return ((expr? maybe-jexprp)
                                    (method-params jparam-listp)
                                    (method-name stringp))
  :returns (block jblockp)
  :short "Eliminate any tail-recursive call in a @('return') statement."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called by @(tsee atj-elim-tailrec-in-jstatem)
     when a @('return') statement with an expression is encountered.
     The first input is the optional expression of the @('return').")
   (xdoc::p
    "If the expression is a call of the method,
     we return a block consisting of
     (1) a parallel assignment of the call's actual arguments
     to the method's parameters, and
     (2) a @('continue') statement.")
   (xdoc::p
    "If the expression is a right-associated conditional conjunction
     @('expr1 && (expr2 && (... && exprN)...)'),
     and its rightmost conjunct @('exprN') is a call of the method,
     we return a block of the form")
   (xdoc::codeblock
    "if (expr1 && (expr2 && (... && exprN-1)...)) {"
    "    <parallel-asg>"
    "    continue;"
    "} else {"
    "    return false;"
    "}")
   (xdoc::p
    "In all other cases,
     we return a block consisting of the single @('return') statement
     with the given expression;
     that is, not change to that part of the Java code is made."))
  (b* (((unless (jexprp expr?)) (list (jstatem-return nil)))
       (expr expr?))
    (cond ((and (jexpr-case expr :method)
                (equal (jexpr-method->name expr)
                       method-name))
           (atj-elim-tailrec-gen-block (jexpr-method->args expr)
                                       method-params))
          ((and (jexpr-case expr :binary)
                (jbinop-case (jexpr-binary->op expr) :condand))
           (b* ((exprs (unmake-right-assoc-condand expr))
                ((unless (>= (len exprs) 2))
                 (raise "Internal error: ~
                         expression ~x0 has fewer than 2 conjuncts."
                        exprs)
                 (ec-call (jblock-fix :irrelevant)))
                (rightmost (car (last exprs)))
                (others (butlast exprs 1))
                ((unless (and (jexpr-case rightmost :method)
                              (equal (jexpr-method->name rightmost)
                                     method-name)))
                 (list (jstatem-return expr?))))
             (jblock-ifelse (make-right-assoc-condand others)
                            (atj-elim-tailrec-gen-block
                             (jexpr-method->args rightmost)
                             method-params)
                            (jblock-return (jexpr-literal-false)))))
          (t (list (jstatem-return expr?))))))

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
     :return (atj-elim-tailrec-in-return statem.expr?
                                         method-params
                                         method-name)
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
