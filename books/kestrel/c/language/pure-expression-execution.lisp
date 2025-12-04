; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "dynamic-semantics")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ pure-expression-execution
  :parents (dynamic-semantics)
  :short "Properties about the execution of pure expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce functions to execute
     pure expressions and lists of pure expressions.
     These do not depend on function environments,
     because pure expressions do not have any function calls,
     and do not depend on limits,
     because pure expressions always terminate execution.
     We prove properties that relate these specialized execution functions
     to the general execution functions for expressions and lists thereof."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-expr-pure ((e exprp) (compst compustatep))
  :returns (eval expr-value-resultp)
  :short "Execute a pure expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return an error if we encounter a non-pure expression.
     While function calls do not necessarily have side effects,
     establishing that requires looking at the function.
     Thus, for simplicity, we regard function calls to be non-pure,
     i.e. we return an error if we encounter them here.")
   (xdoc::p
    "We also reject pre/post-increment/decrement expressions,
     which are obviously non-pure.")
   (xdoc::p
    "When executing a ternary expression,
     we drop any object designators
     from the second or third expression's execution,
     because ternary expressions are not lvalues
     [C17:6.5.15/4, footnote 113].")
   (xdoc::p
    "Recall that our C abstract syntax does not cover
     all the possible C expressions yet.
     Thus, we may extend this ACL2 function
     with support for more kinds of pure expressions in the future.")
   (xdoc::p
    "If no error occurs, none of the expressions has side effects.
     Thus, the order in which the subexpressions are evaluated does not matter:
     we just proceed left to right.")
   (xdoc::p
    "We plan to remove this function from our dynamic semantics,
     after we create a new @('exec-expr-list')
     to replace @(tsee exec-expr-pure-list)."))
  (b* ((e (expr-fix e)))
    (expr-case
     e
     :ident (exec-ident e.get compst)
     :const (exec-const e.get)
     :arrsub (b* ((arr (exec-expr-pure e.arr compst))
                  ((when (errorp arr)) arr)
                  (sub (exec-expr-pure e.sub compst))
                  ((when (errorp sub)) sub))
               (exec-arrsub arr sub compst))
     :call (error (list :non-pure-expr e))
     :member (b* ((str (exec-expr-pure e.target compst))
                  ((when (errorp str)) str))
               (exec-member str e.name))
     :memberp (b* ((str (exec-expr-pure e.target compst))
                   ((when (errorp str)) str))
                (exec-memberp str e.name compst))
     :postinc (error (list :non-pure-expr e))
     :postdec (error (list :non-pure-expr e))
     :preinc (error (list :non-pure-expr e))
     :predec (error (list :non-pure-expr e))
     :unary (b* ((arg (exec-expr-pure e.arg compst))
                 ((when (errorp arg)) arg))
              (exec-unary e.op arg compst))
     :cast (b* ((arg (exec-expr-pure e.arg compst))
                ((when (errorp arg)) arg))
             (exec-cast e.type arg))
     :binary (b* (((unless (binop-purep e.op)) (error (list :non-pure-expr e))))
               (case (binop-kind e.op)
                 (:logand
                  (b* ((arg1 (exec-expr-pure e.arg1 compst))
                       ((when (errorp arg1)) arg1)
                       (arg1 (apconvert-expr-value arg1))
                       ((when (errorp arg1)) arg1)
                       (test1 (test-value (expr-value->value arg1)))
                       ((when (errorp test1)) test1)
                       ((when (not test1))
                        (make-expr-value :value (value-sint 0) :object nil))
                       (arg2 (exec-expr-pure e.arg2 compst))
                       ((when (errorp arg2)) arg2)
                       (arg2 (apconvert-expr-value arg2))
                       ((when (errorp arg2)) arg2)
                       (test2 (test-value (expr-value->value arg2)))
                       ((when (errorp test2)) test2))
                    (if test2
                        (make-expr-value :value (value-sint 1) :object nil)
                      (make-expr-value :value (value-sint 0) :object nil))))
                 (:logor
                  (b* ((arg1 (exec-expr-pure e.arg1 compst))
                       ((when (errorp arg1)) arg1)
                       (arg1 (apconvert-expr-value arg1))
                       ((when (errorp arg1)) arg1)
                       (test1 (test-value (expr-value->value arg1)))
                       ((when (errorp test1)) test1)
                       ((when test1)
                        (make-expr-value :value (value-sint 1) :object nil))
                       (arg2 (exec-expr-pure e.arg2 compst))
                       ((when (errorp arg2)) arg2)
                       (arg2 (apconvert-expr-value arg2))
                       ((when (errorp arg2)) arg2)
                       (test2 (test-value (expr-value->value arg2)))
                       ((when (errorp test2)) test2))
                    (if test2
                        (make-expr-value :value (value-sint 1) :object nil)
                      (make-expr-value :value (value-sint 0) :object nil))))
                 (t (b* ((arg1 (exec-expr-pure e.arg1 compst))
                         ((when (errorp arg1)) arg1)
                         (arg2 (exec-expr-pure e.arg2 compst))
                         ((when (errorp arg2)) arg2))
                      (exec-binary-strict-pure e.op arg1 arg2)))))
     :cond (b* ((test (exec-expr-pure e.test compst))
                ((when (errorp test)) test)
                (test (apconvert-expr-value test))
                ((when (errorp test)) test)
                (test (test-value (expr-value->value test)))
                ((when (errorp test)) test))
             (if test
                 (b* ((eval (exec-expr-pure e.then compst))
                      ((when (errorp eval)) eval)
                      (eval (apconvert-expr-value eval))
                      ((when (errorp eval)) eval))
                   (change-expr-value eval :object nil))
               (b* ((eval (exec-expr-pure e.else compst))
                    ((when (errorp eval)) eval)
                    (eval (apconvert-expr-value eval))
                    ((when (errorp eval)) eval))
                 (change-expr-value eval :object nil))))))
  :measure (expr-count e)
  :hints (("Goal" :in-theory (enable o-p o< o-finp)))
  :verify-guards nil ; done below

  ///

  (defret expr-value-resultp-of-exec-expr-pure-forward
    (expr-value-resultp eval)
    :rule-classes ((:forward-chaining
                    :trigger-terms ((exec-expr-pure e compst)))))

  (verify-guards exec-expr-pure
    :hints (("Goal" :in-theory (enable binop-strictp (:e tau-system)))))

  (defruled not-call-when-exec-expr-pure-not-error
    (implies (not (errorp (exec-expr-pure expr compst)))
             (not (equal (expr-kind expr) :call)))
    :induct t)

  (defruled not-asg-when-exec-expr-pure-not-error
    (implies (not (errorp (exec-expr-pure expr compst)))
             (not (and (equal (expr-kind expr) :binary)
                       (equal (binop-kind (expr-binary->op expr)) :asg))))
    :induct t
    :enable binop-purep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-expr-pure-list ((es expr-listp) (compst compustatep))
  :returns (result
            value-list-resultp
            :hints (("Goal"
                     :induct t
                     :in-theory
                     (enable
                      valuep-when-value-resultp-and-not-errorp
                      value-listp-when-value-list-resultp-and-not-errorp))))
  :short "Execute a list of pure expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given that the expressions have no side effects (if there is no error),
     the order of evaluation does not matter.
     Thus, we proceed left to right.")
   (xdoc::p
    "This ACL2 function is only used in situations
     in which we are interested in the values of the expressions,
     not their expression values (i.e. object designators, if any).
     Thus, we just return lists of values here.")
   (xdoc::p
    "In the situations in which this ACL2 function is used,
     we also need to perform array-to-pointer conversion [C17:6.3.2.1/3]."))
  (b* (((when (endp es)) nil)
       (eval (exec-expr-pure (car es) compst))
       ((when (errorp eval)) eval)
       (eval (apconvert-expr-value eval))
       ((when (errorp eval)) eval)
       (val (expr-value->value eval))
       (vals (exec-expr-pure-list (cdr es) compst))
       ((when (errorp vals)) vals))
    (cons val vals))
  :guard-hints (("Goal" :in-theory (enable (:e tau-system)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-pure-limit ((expr exprp))
  :guard (expr-purep expr)
  :returns (limit posp :rule-classes (:rewrite :type-prescription))
  :short "Limit to pass to @(tsee exec-expr)
          for the execution of the given pure expression to terminate."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function @(tsee exec-expr) handles possible non-termination
     via the artificial limit input to the execution functions.
     However, pure expressions always terminate,
     and we can calculate, for each pure expression,
     a limit value that we can pass to @(tsee exec-expr)
     for execution to terminate.
     Here we define such calculation.")
   (xdoc::p
    "The execution of the expression may terminate with an error,
     depending on the computation state and possibly function environment.
     However, here we are solely concerned with @(tsee exec-expr)
     not failing the @('(zp limit)') test.")
   (xdoc::p
    "For variables and constants, we just need 1,
     because we just need to pass the initial test,
     and then there is no recursive call of @(tsee exec-expr).
     For expressions with a single sub-expression,
     we add 1 to the limit for the sub-expression.
     For expressions with two or three sub-expressions,
     we add 1 to the maximum of the limits of the sub-expressions.")
   (xdoc::p
    "Note that currently type names do not undergo execution
     in our formal dynamic semantics,
     so for cast expressions we are only concerned with the sub-expression.")
   (xdoc::p
    "For strict expressions, the limit returned by this function
     is the minimum one for which execution does not fail (due to the limit):
     a smaller value would fail, because all sub-expressions are executed.
     For non-strict expressions, this is not necessarily the minimum:
     for instance, a @('&&') expression could have
     a first sub-expression that needs a much smaller limit than the second,
     and that first sub-expression may suffice to evaluate the expression."))
  (expr-case
   expr
   :ident 1
   :const 1
   :arrsub (1+ (max (expr-pure-limit expr.arr)
                    (expr-pure-limit expr.sub)))
   :member (1+ (expr-pure-limit expr.target))
   :memberp (1+ (expr-pure-limit expr.target))
   :unary (1+ (expr-pure-limit expr.arg))
   :cast (1+ (expr-pure-limit expr.arg))
   :binary (1+ (max (expr-pure-limit expr.arg1)
                    (expr-pure-limit expr.arg2)))
   :cond (1+ (max (expr-pure-limit expr.test)
                  (max (expr-pure-limit expr.then)
                       (expr-pure-limit expr.else))))
   :otherwise (prog2$ (impossible) 1))
  :measure (expr-count expr)
  :hints (("Goal" :in-theory (enable o-p o-finp o<)))
  :verify-guards :after-returns
  :guard-hints (("Goal" :expand (expr-purep expr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-list-pure-limit ((exprs expr-listp))
  :guard (expr-list-purep exprs)
  :returns (limit posp :rule-classes (:rewrite :type-prescription))
  :short "Limit to pass to @(tsee exec-expr-list)
          for the execution of the given list of pure expressions to terminate."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the list is empty, we still need 1 because
     @(tsee exec-expr-list) checks the limit against @(tsee zp)
     before examining the list.
     If the list is not empty, we additionally need enough
     to execute the first and the rest, so we take the maximum."))
  (cond ((endp exprs) 1)
        (t (1+ (max (expr-pure-limit (car exprs))
                    (expr-list-pure-limit (cdr exprs)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define induct-exec-expr-of-pure ((expr exprp) (limit natp))
  :short "Induction scheme for @(tsee exec-expr) applied to a pure expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "This concerns both the expression structure and the limit."))
  (expr-case expr
             :ident nil
             :const nil
             :arrsub (list (induct-exec-expr-of-pure expr.arr (1- limit))
                           (induct-exec-expr-of-pure expr.sub (1- limit)))
             :member (induct-exec-expr-of-pure expr.target (1- limit))
             :memberp (induct-exec-expr-of-pure expr.target (1- limit))
             :unary (induct-exec-expr-of-pure expr.arg (1- limit))
             :cast (induct-exec-expr-of-pure expr.arg (1- limit))
             :binary (list (induct-exec-expr-of-pure expr.arg1 (1- limit))
                           (induct-exec-expr-of-pure expr.arg2 (1- limit)))
             :cond (list (induct-exec-expr-of-pure expr.test (1- limit))
                         (induct-exec-expr-of-pure expr.then (1- limit))
                         (induct-exec-expr-of-pure expr.else (1- limit)))
             :otherwise nil)
  :measure (expr-count expr)
  :hints (("Goal" :in-theory (enable o-p o< o-finp)))
  :verify-guards nil
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define induct-exec-expr-list-of-pure ((exprs expr-listp) (limit natp))
  :short "Induction scheme for @(tsee exec-expr-list)
          applied to a list of pure expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This concerns both the list structure and the limit."))
  (cond ((endp exprs) nil)
        (t (induct-exec-expr-list-of-pure (cdr exprs) (1- limit))))
  :verify-guards nil
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled exec-expr-to-exec-expr-pure-when-expr-pure-limit
  :short "Reduction of @(tsee exec-expr) to @(tsee exec-expr-pure),
          under a hypothesis about the limit."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given a pure expression and a sufficient limit for it,
     the first result of @(tsee exec-expr) is
     the same as the (only) result of @(tsee exec-expr-pure)
     (whether it is an error or not),
     and the second result of @(tsee exec-expr) is
     the unchanged computation state."))
  (implies (and (expr-purep expr)
                (>= (nfix limit) (expr-pure-limit expr)))
           (equal (exec-expr expr compst fenv limit)
                  (mv (exec-expr-pure expr compst)
                      (compustate-fix compst))))
  :induct (induct-exec-expr-of-pure expr limit)
  :expand ((exec-expr-pure expr compst)
           (expr-purep expr))
  :enable (induct-exec-expr-of-pure
           exec-expr
           expr-pure-limit
           binop-strictp
           nfix
           max))

;;;;;;;;;;;;;;;;;;;;

(defruled exec-expr-to-exec-expr-pure-when-not-errorp
  :short "Reduction of @(tsee exec-expr) to @(tsee exec-expr-pure),
          under a hypothesis about the absence of errors."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @(tsee exec-expr) on a pure expression does not return an error,
     then it returns the same result as @(tsee exec-expr-pure),
     and the computation state is unchanged."))
  (implies (and (expr-purep expr)
                (not (errorp
                      (mv-nth 0 (exec-expr expr compst fenv limit)))))
           (equal (exec-expr expr compst fenv limit)
                  (mv (exec-expr-pure expr compst)
                      (compustate-fix compst))))
  :induct (induct-exec-expr-of-pure expr limit)
  :expand ((exec-expr-pure expr compst)
           (expr-purep expr))
  :enable (induct-exec-expr-of-pure
           exec-expr
           binop-strictp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled exec-expr-list-to-exec-expr-pure-list-when-expr-pure-list-limit
  :short "Reduction of @(tsee exec-expr-list) to @(tsee exec-expr-pure-list)
          under a hypothesis about the limit."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given a list of pure expressions and a sufficient limit for it,
     the first result of @(tsee exec-expr-list) is
     the same as the (only) result of @(tsee exec-expr-pure-list)
     (whether it is an error or not),
     and the second result of @(tsee exec-expr-list) is
     the unchanged computation state."))
  (implies (and (expr-list-purep exprs)
                (>= (nfix limit) (expr-list-pure-limit exprs)))
           (equal (exec-expr-list exprs compst fenv limit)
                  (mv (exec-expr-pure-list exprs compst)
                      (compustate-fix compst))))
  :induct (induct-exec-expr-list-of-pure exprs limit)
  :enable (induct-exec-expr-list-of-pure
           exec-expr-list
           exec-expr-pure-list
           expr-list-pure-limit
           exec-expr-to-exec-expr-pure-when-expr-pure-limit
           nfix
           max))

;;;;;;;;;;;;;;;;;;;;

(defruled exec-expr-list-to-exec-expr-pure-list-when-not-errorp
  :short "Reduction of @(tsee exec-expr-list) to @(tsee exec-expr-pure-list),
          under a hypothesis about the absence of errors."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @(tsee exec-expr-list) on a pure expression does not return an error,
     then it returns the same result as @(tsee exec-expr-pure-list),
     and the computation state is unchanged."))
  (implies (and (expr-list-purep exprs)
                (not (errorp
                      (mv-nth 0 (exec-expr-list exprs compst fenv limit)))))
           (equal (exec-expr-list exprs compst fenv limit)
                  (mv (exec-expr-pure-list exprs compst)
                      (compustate-fix compst))))
  :induct (induct-exec-expr-list-of-pure exprs limit)
  :expand (exec-expr-list exprs compst fenv limit)
  :enable (induct-exec-expr-list-of-pure
           exec-expr-list
           exec-expr-pure-list
           exec-expr-to-exec-expr-pure-when-not-errorp))
