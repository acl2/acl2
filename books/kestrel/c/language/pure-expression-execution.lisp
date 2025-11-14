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
    "For now the definition is relatively simple,
     because @(tsee exec-expr) only handles a few expressions directly
     (i.e. via the cases of the fixtype of expressions),
     and more expressions indirectly
     (i.e. in the @(':otherwise') case.
     However, as we extend @(tsee exec-expr) with more explicit cases
     (as part of our moving away from @(tsee exec-expr-pure)),
     this calculation will become correspondingly richer.")
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
    "Call expressions currently need just 1,
     because, for the arguments, we use @(tsee exec-expr-pure-list);
     but eventually we will extend this case
     to recursively call @(tsee exec-expr),
     and we will update the calculation of the limit.")
   (xdoc::p
    "Most other kinds of expressions also just need 1 currently,
     because after passing the initial test,
     we call @(tsee exec-expr-pure) and not @(tsee exec-expr);
     this will also change as we extend @(tsee exec-expr)."))
  (expr-case
   expr
   :ident 1
   :const 1
   :arrsub 1
   :member 1
   :memberp 1
   :unary (1+ (expr-pure-limit expr.arg))
   :cast (1+ (expr-pure-limit expr.arg))
   :binary 1
   :cond 1
   :otherwise (prog2$ (impossible) 0))
  :measure (expr-count expr)
  :hints (("Goal" :in-theory (enable o-p o-finp o<)))
  :guard-hints (("Goal" :expand (expr-purep expr))))

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
             :call nil
             :unary (induct-exec-expr-of-pure expr.arg (1- limit))
             :cast (induct-exec-expr-of-pure expr.arg (1- limit))
             :otherwise nil)
  :measure (expr-count expr)
  :hints (("Goal" :in-theory (enable o-p o< o-finp)))
  :verify-guards nil)

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
  :expand (exec-expr-pure expr compst)
  :enable (induct-exec-expr-of-pure
           exec-expr
           expr-pure-limit
           expr-purep
           nfix))

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
  (b* (((mv eval &) (c::exec-expr expr compst fenv limit)))
    (implies (and (c::expr-purep expr)
                  (not (c::errorp eval)))
             (>= (nfix limit) (c::expr-pure-limit expr))))
  :rule-classes ((:linear :trigger-terms ((c::expr-pure-limit expr))))
  :induct (c::induct-exec-expr-of-pure expr limit)
  :enable (c::induct-exec-expr-of-pure
           c::exec-expr
           c::expr-pure-limit
           c::expr-purep
           nfix))
