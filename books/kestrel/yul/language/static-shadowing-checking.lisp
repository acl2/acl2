; Yul Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "abstract-syntax")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ static-shadowing-checking
  :parents (static-semantics)
  :short "Static shadowing checking of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to [Yul: Specification of Yul: Scoping Rules],
     a variable declaration cannot shadow a variable
     that is visible at the point in which the variable declaration occurs.
     The notion of `visible' applies
     not only to variables declared in outer blocks in the same function,
     but also to variables declared in blocks in outer functions:
     the former variables are accessible, while the latter are not.")
   (xdoc::p
    "For instance, consider the following Yul code:")
   (xdoc::codeblock
    "function f () {"
    "  let x"
    "  function g () {"
    "    let y"
    "    // here"
    "  }"
    "}"
    )
   (xdoc::p
    "At the point marked as `here',
     @('x') is visible but not accessible,
     while @('y') is both visible and accessible.")
   (xdoc::p
    "The non-shadowing of outer variables in the same function
     (e.g. the non-shadowing of @('y') in function @('g'))
     is checked as part of the safety checks
     formalized in @(see static-safety-checking).
     This is necessary for safety,
     because the dynamic semantics has
     a single variable scope (not a stack of scopes),
     as formalized in @(see static-safety-checking).")
   (xdoc::p
    "The non-shadowing of outer variables in different functions
     (e.g. the non-shadowing of @('x') in function @('g'))
     is not needed for safe execution,
     because when the body of a function (e.g. @('g')) is executed,
     a new variable scope is started,
     and the function has no access to outside variables (e.g. to @('x')).
     Nonetheless, it is part of the Yul static semantics:
     the Yul team has explained that its purpose is
     just to prevent human error.
     Thus, we formalize these checks here,
     separately from the safety checks.")
   (xdoc::p
    "The shadowing restrictions formalized here
     only apply to variables, not to functions.
     Variables and functions are subject to
     different visibility and accessibility rules;
     all the rules that apply to functions
     are parts of the safety checks."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-shadow-statements/blocks/cases/fundefs
  :short "Check the additional shadowing constraints on
          statements, blocks, cases, and function definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We recursively visit statements, blocks, etc.,
     accumulating all the variables declared so far,
     which form all the visible variables,
     both accessible and inaccessble.
     We check that each declared variable is not already visible.")
   (xdoc::p
    "Note that these checks overlap with the safety checks,
     for what concerns visible and accessible variables,
     while they are additional checks
     for what concerns visible but inaccessible variables.
     Restricting the checks to just visible but inaccessible variables
     would be more complicated than checking all the visible variables."))

  (define check-shadow-statement ((stmt statementp) (vars identifier-setp))
    :returns (new-vars identifier-set-resultp)
    :short "Check variable shadowing in a statement."
    :long
    (xdoc::topstring
     (xdoc::p
      "If the check is successful,
       we return a possibly updated set of visible variables.
       The set is actually updated only by variable declarations.")
     (xdoc::p
      "Since the scope of a loop's initialization block
       extends to the whole loop,
       we first check the list of statments of the initialization block,
       obtaining a possibly updated set of visible variables,
       which is used to check the update and body blocks of the loop."))
    (statement-case
     stmt
     :block (b* (((okf &) (check-shadow-block stmt.get vars)))
              (identifier-set-fix vars))
     :variable-single (if (set::in stmt.name (identifier-set-fix vars))
                          (reserrf (list :shadowed-var stmt.name))
                        (set::insert stmt.name (identifier-set-fix vars)))
     :variable-multi (b* ((declared (set::mergesort stmt.names))
                          (shadowed (set::intersect declared
                                                    (identifier-set-fix vars))))
                       (if (set::emptyp shadowed)
                           (set::union declared (identifier-set-fix vars))
                         (reserrf (list :shadowed-vars shadowed))))
     :assign-single (identifier-set-fix vars)
     :assign-multi (identifier-set-fix vars)
     :funcall (identifier-set-fix vars)
     :if (b* (((okf &) (check-shadow-block stmt.body vars)))
           (identifier-set-fix vars))
     :for (b* ((stmts (block->statements stmt.init))
               ((okf vars1) (check-shadow-statement-list stmts vars))
               ((okf &) (check-shadow-block stmt.update vars1))
               ((okf &) (check-shadow-block stmt.body vars1)))
            (identifier-set-fix vars))
     :switch (b* (((okf &) (check-shadow-swcase-list stmt.cases vars))
                  ((okf &) (check-shadow-block-option stmt.default vars)))
               (identifier-set-fix vars))
     :leave (identifier-set-fix vars)
     :break (identifier-set-fix vars)
     :continue (identifier-set-fix vars)
     :fundef (b* (((okf &) (check-shadow-fundef stmt.get vars)))
               (identifier-set-fix vars)))
    :measure (statement-count stmt))

  (define check-shadow-statement-list ((stmts statement-listp)
                                       (vars identifier-setp))
    :returns (new-vars identifier-set-resultp)
    :short "Check variable shadowing in a list of statements."
    (b* (((when (endp stmts)) (identifier-set-fix vars))
         ((okf vars) (check-shadow-statement (car stmts) vars))
         ((okf vars) (check-shadow-statement-list (cdr stmts) vars)))
      vars)
    :measure (statement-list-count stmts))

  (define check-shadow-block ((block blockp) (vars identifier-setp))
    :returns (_ reserr-optionp)
    :short "Check variable shadowing in a block."
    :long
    (xdoc::topstring
     (xdoc::p
      "We return no information in case of success,
       because the variables declared in a block
       are not visible after the block."))
    (b* (((okf &) (check-shadow-statement-list (block->statements block) vars)))
      nil)
    :measure (block-count block))

  (define check-shadow-block-option ((block? block-optionp)
                                     (vars identifier-setp))
    :returns (_ reserr-optionp)
    :short "Check variable shadowing in an optional block."
    (block-option-case
     block?
     :none nil
     :some (check-shadow-block block?.val vars))
    :measure (block-option-count block?))

  (define check-shadow-swcase ((case swcasep) (vars identifier-setp))
    :returns (_ reserr-optionp)
    :short "Check variable shadowing in a case."
    (check-shadow-block (swcase->body case) vars)
    :measure (swcase-count case))

  (define check-shadow-swcase-list ((cases swcase-listp) (vars identifier-setp))
    :returns (_ reserr-optionp)
    :short "Check variable shadowing in a list of cases."
    (b* (((when (endp cases)) nil)
         ((okf &) (check-shadow-swcase (car cases) vars))
         ((okf &) (check-shadow-swcase-list (cdr cases) vars)))
      nil)
    :measure (swcase-list-count cases))

  (define check-shadow-fundef ((fundef fundefp) (vars identifier-setp))
    :returns (_ reserr-optionp)
    :short "Check variable shadowing in a function definition."
    :long
    (xdoc::topstring
     (xdoc::p
      "First we ensure that the function's inputs and outputs
       are not already visible.
       We add them to the visible variables,
       and we check the body."))
    (b* ((inputs (fundef->inputs fundef))
         (outputs (fundef->outputs fundef))
         (declared (set::mergesort (append inputs outputs)))
         (shadowed (set::intersect declared (identifier-set-fix vars)))
         ((unless (set::emptyp shadowed))
          (reserrf (list :shadowed-vars shadowed)))
         (vars (set::union (identifier-set-fix vars) declared)))
      (check-shadow-block (fundef->body fundef) vars))
    :measure (fundef-count fundef))

  :verify-guards nil ; done below

  ///

  (verify-guards check-shadow-statement)

  (fty::deffixequiv-mutual check-shadow-statements/blocks/cases/fundefs))
