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
    "As discussed in @(tsee exec-expr-pure),
     we are planning to move away from that function
     in favor of (an extended version of) @(tsee exec-expr).
     However, while we have both versions, here we prove
     properties that relate the two execution functions on pure expressions.
     We also define some more general concepts
     that may survive after the elimination of @(tsee exec-expr-pure)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-pure-limit ((expr exprp))
  :guard (expr-purep expr)
  :returns (limit natp)
  :short "Minimum limit to pass to @(tsee exec-expr)
          for the execution of the given pure expression to terminate."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function @(tsee exec-expr-pure) handles possible non-termination
     via the artificial limit input to the execution functions.
     However, pure expressions always terminate,
     and we can calculate, for each pure expression,
     the minimum limit value that we can pass to @(tsee exec-expr)
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
     and then there is no recursive call of @(tsee exec-expr).")
   (xdoc::p
    "For unary and cast expressions, we add 1 to the limit for the argument,
     because we need one more to reach the recursive call
     of @(tsee exec-expr) applied to the argument.
     Note that currently type names do not undergo execution
     in our formal dynamic semantics.")
   (xdoc::p
    "For binary pure expressions, we add 1 to
     the maximum of the limits for the sub-expressions.")
   (xdoc::p
    "For all the other kinds of expressions we just need 1 currently,
     because we delegate to @(tsee exec-expr-pure)."))
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
   :binary (if (binop-strictp expr.op)
               (1+ (max (expr-pure-limit expr.arg1)
                        (expr-pure-limit expr.arg2)))
             1)
   :cond 1
   :otherwise (prog2$ (impossible) 0))
  :measure (expr-count expr)
  :hints (("Goal" :in-theory (enable o-p o-finp o<)))
  :verify-guards :after-returns
  :guard-hints (("Goal"
                 :in-theory (enable binop-strictp)
                 :expand (expr-purep expr))))

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
             :binary (if (binop-strictp expr.op)
                         (list (induct-exec-expr-of-pure expr.arg1 (1- limit))
                               (induct-exec-expr-of-pure expr.arg2 (1- limit)))
                       nil)
             :otherwise nil)
  :measure (expr-count expr)
  :hints (("Goal" :in-theory (enable o-p o< o-finp)))
  :verify-guards nil
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled exec-expr-to-exec-expr-pure
  :short "Reductio of @(tsee exec-expr) to @(tsee exec-expr-pure)."
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pure-limit-bound-when-exec-expr-not-error
  :short "Bound on the limit
          if the execution of a pure expression does not fail."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @(tsee exec-expr) applied to a pure expression
     does not return an error,
     the limit must be at least the minimum one for the expression.
     Otherwise execution would yield a (limit) error."))
  (b* (((mv eval &) (exec-expr expr compst fenv limit)))
    (implies (and (expr-purep expr)
                  (not (errorp eval)))
             (>= (nfix limit) (expr-pure-limit expr))))
  :rule-classes ((:linear :trigger-terms ((expr-pure-limit expr))))
  :induct (induct-exec-expr-of-pure expr limit)
  :expand (exec-expr expr compst fenv limit)
  :enable (induct-exec-expr-of-pure
           exec-expr-to-exec-expr-pure
           expr-pure-limit
           expr-purep
           binop-strictp
           nfix
           max))
