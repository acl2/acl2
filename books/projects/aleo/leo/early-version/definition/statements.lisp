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

(include-book "expressions")
(include-book "types")

(include-book "std/basic/two-nats-measure" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ statements
  :parents (abstract-syntax)
  :short "Leo statements."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we formalize an abstract syntactic representation
     of all the Leo statements."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod vardecl
  :short "Fixtype of variable declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "A variable declaration consists of
     a name (identifier),
     a type,
     and an (initializing) expression."))
  ((name identifier)
   (type type)
   (init expression))
  :tag :vardecl
  :pred vardeclp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult vardecl-result
  :short "Fixtype of errors and Leo variable declarations."
  :ok vardecl
  :pred vardecl-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod constdecl
  :short "Fixtype of constant declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "A constant declaration has the same structure as a variable declaration,
     but we introduce a different type because
     variables and constants are different entities
     and also so that it is easier to extend variable or constant declarations
     independently from each other, should the need arise."))
  ((name identifier)
   (type type)
   (init expression))
  :tag :constdecl
  :pred constdeclp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult constdecl-result
  :short "Fixtype of errors and Leo constant declarations."
  :ok constdecl
  :pred constdecl-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum asgop
  :short "Fixtype of Leo assignment operators."
  :long
  (xdoc::topstring
   (xdoc::p
    "These consist of a simple assignment (i.e. @('='))
     and 13 compound assignments such as @('+=').")
   (xdoc::p
    "We formalize these assignment operators
     separately from the binary operators formalized by @(tsee binop)
     because they appear in Leo statements, not in Leo expressions.
     Thus, it is more convenient to have a separate syntactic category."))
  (:asg ())
  (:asg-add ())
  (:asg-sub ())
  (:asg-mul ())
  (:asg-div ())
  (:asg-rem ())
  (:asg-pow ())
  (:asg-shl ())
  (:asg-shr ())
  (:asg-bitand ())
  (:asg-bitior ())
  (:asg-bitxor ())
  (:asg-and ())
  (:asg-or ())
  :pred asgopp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult asgop-result
  :short "Fixtype of errors and Leo assignment operators."
  :ok asgop
  :pred asgop-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define asgop-to-binop ((op asgopp))
  :guard (not (asgop-case op :asg))
  :returns (bop binopp)
  :short "Map each Leo compound assignment operator
          to the corresponding binary operator."
  (asgop-case op
              :asg (prog2$ (impossible) (ec-call (binop-fix :irrelevant)))
              :asg-add (binop-add)
              :asg-sub (binop-sub)
              :asg-mul (binop-mul)
              :asg-div (binop-div)
              :asg-rem (binop-rem)
              :asg-pow (binop-pow)
              :asg-shl (binop-shl)
              :asg-shr (binop-shr)
              :asg-bitand (binop-bitand)
              :asg-bitior (binop-bitior)
              :asg-bitxor (binop-bitxor)
              :asg-and (binop-and)
              :asg-or (binop-or)
              )
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum console
  :short "Fixtype of Leo console calls."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are a kind of statements (see @(tsee statement)).")
   (xdoc::p
    "There is an assertion call that takes an expression as argument.")
   (xdoc::p
    "There are two calls (for errors and logging) that take
     a string (literal) and zero or more expressions as arguments."))
  (:assert ((arg expression)))
  (:error ((string char-list)
           (exprs expression-list)))
  (:log ((string char-list)
         (exprs expression-list)))
  :pred consolep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult console-result
  :short "Fixtype of errors and Leo console function calls."
  :ok console
  :pred console-resultp
  :prepwork ((local (in-theory (e/d (console-kind) (consolep))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes statement-fixtypes
  :short "Mutually recursive fixtypes of Leo statements."

  (fty::deftagsum statement
    :parents (abstract-syntax statement-fixtypes)
    :short "Fixtype of Leo statements."
    :long
    (xdoc::topstring
     (xdoc::p
      "There are
       variable and constant declarations,
       assignments,
       return statements,
       loops,
       conditionals,
       console calls,
       and blocks.")
     (xdoc::p
      "We use arbitrary expressions on the left side of assignments,
       even though only a subset of expressions may be used:
       the subset is enforced by type checking.")
     (xdoc::p
      "We formalize conditionals as consisting of a sequence of branches
       (tests and expressions) and a final @('else') block.
       The first branch contains
       the first condition and the @('then') statements.
       Each successive branch contains the condition after an @('else if')
       and the block following the additional @('then').
       The final @('else') block is empty if there is no bare @('else')
       at the end, i.e., if every @('else') is followed by another @('if').
       There must be at least one branch;
       this is not captured in our abstract syntax,
       but delegated to static and dynamic semantics.")
     (xdoc::p
      "We formalize blocks as lists of statements.
       We do not introduce wrappers for blocks
       (aside from the tag @(':block') in the @('statement') fixtype)."))
    (:let ((get vardecl)))
    (:const ((get constdecl)))
    (:assign ((op asgop)
              (left expression)
              (right expression)))
    (:return ((value expression)))
    (:for ((name identifier)
           (type type)
           (from expression)
           (to expression)
           (inclusivep bool)
           (body statement-list)))
    (:if ((branches branch-list
                    :reqfix (if (consp branches)
                                branches
                              (list (branch-fix :irrelevant))))
          (else statement-list))
     :require (consp branches))
    (:console ((get console)))
    (:block ((get statement-list)))
    (:finalize ((arguments expression-list)))
    (:increment ((mapping identifier)
                 (index expression)
                 (amount expression)))
    (:decrement ((mapping identifier)
                 (index expression)
                 (amount expression)))
    :pred statementp
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::deflist statement-list
    :parents (abstract-syntax statement-fixtypes)
    :short "Fixtype of lists of Leo statements."
    :elt-type statement
    :true-listp t
    :elementp-of-nil nil
    :pred statement-listp
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::defprod branch
    :parents (abstract-syntax statement-fixtypes)
    :short "Fixtype of Leo branches."
    :long
    (xdoc::topstring
     (xdoc::p
      "We formalize a branch as consisting of
       a test expression and a list of statements.
       These branches are constituents of conditional statements."))
    ((test expression)
     (body statement-list))
    :pred branchp
    :measure (two-nats-measure (acl2-count x) 1))

  (fty::deflist branch-list
    :parents (abstract-syntax statement-fixtypes)
    :short "Fixtype of lists of Leo branches."
    :elt-type branch
    :true-listp t
    :elementp-of-nil nil
    :pred branch-listp
    :measure (two-nats-measure (acl2-count x) 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult statement-result
  :short "Fixtype of errors and Leo statement."
  :ok statement
  :pred statement-resultp
  :prepwork ((local (in-theory (e/d (statement-kind) (statementp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult statement-list-result
  :short "Fixtype of errors and lists of Leo statements."
  :ok statement-list
  :pred statement-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult branch-result
  :short "Fixtype of errors and Leo branches."
  :ok branch
  :pred branch-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult branch-list-result
  :short "Fixtype of errors and lists of Leo branches"
  :ok branch-list
  :pred branch-list-resultp)
