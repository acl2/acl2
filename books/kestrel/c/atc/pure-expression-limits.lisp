; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../language/dynamic-semantics")

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ pure-expression-limits
  :parents (atc-event-and-code-generation)
  :short "Limit calculation for pure expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "As discussed in @(tsee exec-expr-pure),
     we are planning to move away from that function
     in favor of (an extended version of) @(tsee exec-expr).
     The latter function handles possible non-termination
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
     this calculation will become correspondingly richer."))
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
    "See @(see pure-expression-limits) for motivation.
     The execution of the expression may terminate with an error,
     depending on the computation state and possibly function environment.
     However, here we are solely concerned with @(tsee exec-expr)
     not failing the @('(zp limit)') test.")
   (xdoc::p
    "For variables and constants, we just need 1,
     because we just need to pass the initial test,
     and then there is no recursive call of @(tsee exec-expr).")
   (xdoc::p
    "For unary expressions, we add 1 to the limit for the argument,
     because we need one more to reach the recursive call
     of @(tsee exec-expr) applied to the argument.")
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
     this will also change as we extend @(tsee exec-expr).")
   (xdoc::p
    "But there is already one case that needs a more complex calculation,
     namely the case of an assignment whose left side is a variable,
     because in that case we use @(tsee exec-expr) for the right side.
     So we recursively calculate the limit for the right side,
     and we add 1 for the initial test performed when
     @(tsee exec-expr) is called on the assignment."))
  (expr-case
   expr
   :ident 1
   :const 1
   :arrsub 1
   :member 1
   :memberp 1
   :unary (1+ (expr-pure-limit expr.arg))
   :cast 1
   :binary 1
   :cond 1
   :otherwise (prog2$ (impossible) 0))
  :measure (expr-count expr)
  :hints (("Goal" :in-theory (enable o-p o-finp o<)))
  :guard-hints (("Goal" :expand (expr-purep expr))))
