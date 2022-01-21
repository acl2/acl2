; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "../language/abstract-syntax")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dead-code-eliminator
  :parents (transformations)
  :short "The @('DeadCodeEliminator') transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is described in
     [Solidity: Internals: The Optimizer: Yul-Based Optimizer Module:
      Statement-Scale Simplifications: DeadCodeEliminator].
     The description mentions not only @('break'), @('continue') and @('leave'),
     but also other constructs that are presumably part of the EVM dialect;
     since they are not part of our formalization,
     we do not handle the latter for now.")
   (xdoc::p
    "We define this transformation assuming that
     @('FunctionHoister') and @('FunctionGrouper') have already run:
     this means that all the functions are all
     immediately contained in the top-level block,
     where `immediately' means that
     there are no intervening blocks in between,
     i.e. the function definitions are not contained in nested blocks.
     This condition is formalized in @(see no-function-definitions)
     (actually, for now only part of those conditions is formalized there,
     but we plan to extend that formalization).
     We do not represent this condition in the guards,
     for greater flexibility and simplicity,
     but the correctness theorems for this tranformation
     use that condition as hypothesis.")
   (xdoc::p
    "Here is some elaboration on not representing that condition in the guards.
     If we used @(tsee block-nofunp) as guard of @(tsee block-dead),
     then we could not use @(tsee block-dead) for the top-level block,
     which does not satisfy @(tsee block-nofunp).
     Also, as we need to extend the @('...-dead') transformations
     from syntactic to semantics entities in "
    (xdoc::seetopic "dead-code-eliminator-execution"
                    "the proof of dynamic correctness")
    ", we would have to extend the @('-...-nofunp') functions
     to those semantics entities as well in order to verify the guards.
     For these reasons, i.e. flexibility and simplicity respectively,
     we do not use @('...-nofunp') as guards in @('...-dead')."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines statements/blocks/cases/fundefs-dead
  :short "Mutually recursive functions to eliminate dead code in
          statements, blocks, cases, and function definitions."

  (define statement-dead ((stmt statementp))
    :returns (new-stmt statementp)
    :short "Eliminate dead code in statements."
    :long
    (xdoc::topstring
     (xdoc::p
      "Note that the @('break'), @('continue'), and @('leave') statements
       are retained;
       it is the statements following them that are discarded
       (see @(tsee statement-list-dead)).")
     (xdoc::p
      "When we encounter a function definition, we transform its body.
       As discussed in @(see dead-code-eliminator),
       this only happens in the top-level block."))
    (statement-case
     stmt
     :block (statement-block (block-dead stmt.get))
     :variable-single (statement-fix stmt)
     :variable-multi (statement-fix stmt)
     :assign-single (statement-fix stmt)
     :assign-multi (statement-fix stmt)
     :funcall (statement-fix stmt)
     :if (make-statement-if :test stmt.test
                            :body (block-dead stmt.body))
     :for (make-statement-for :init (block-dead stmt.init)
                              :test stmt.test
                              :update (block-dead stmt.update)
                              :body (block-dead stmt.body))
     :switch (make-statement-switch :target stmt.target
                                    :cases (swcase-list-dead stmt.cases)
                                    :default (block-option-dead stmt.default))
     :leave (statement-leave)
     :break (statement-break)
     :continue (statement-continue)
     :fundef (statement-fundef (fundef-dead stmt.get)))
    :measure (statement-count stmt))

  (define statement-list-dead ((stmts statement-listp))
    :returns (new-stmt statement-listp)
    :short "Eliminate dead code in lists of statements."
    :long
    (xdoc::topstring
     (xdoc::p
      "We go through the statements, recursively transforming them.
       If we reach a @('break'), @('continue'), or @('leave') we stop,
       dropping the remaining statements.
       This is correct because
       there cannot be function definitions among the statements,
       as discussed in @(see dead-code-eliminator).
       Without this assumption,
       we would still have to retain the function definitions
       after the @('break'), @('continue'), or @('leave')."))
    (b* (((when (endp stmts)) nil)
         (stmt (car stmts))
         (new-stmt (statement-dead stmt))
         ((when (or (statement-case stmt :leave)
                    (statement-case stmt :break)
                    (statement-case stmt :continue)))
          (list new-stmt)))
      (cons new-stmt
            (statement-list-dead (cdr stmts))))
    :measure (statement-list-count stmts))

  (define block-dead ((block blockp))
    :returns (new-block blockp)
    :short "Eliminate dead code in blocks."
    (block (statement-list-dead (block->statements block)))
    :measure (block-count block))

  (define block-option-dead ((block? block-optionp))
    :returns (new-block? block-optionp)
    :short "Eliminate dead code in optional blocks."
    (block-option-case block?
                       :some (block-dead block?.val)
                       :none nil)
    :measure (block-option-count block?))

  (define swcase-dead ((case swcasep))
    :returns (new-case swcasep)
    :short "Eliminate dead code in switch cases."
    (make-swcase :value (swcase->value case)
                 :body (block-dead (swcase->body case)))
    :measure (swcase-count case))

  (define swcase-list-dead ((cases swcase-listp))
    :returns (new-cases swcase-listp)
    :short "Eliminate dead code in lists of switch cases."
    (cond ((endp cases) nil)
          (t (cons (swcase-dead (car cases))
                   (swcase-list-dead (cdr cases)))))
    :measure (swcase-list-count cases))

  (define fundef-dead ((fundef fundefp))
    :returns (new-fdef fundefp)
    :short "Eliminate dead code in function definitions."
    (make-fundef :name (fundef->name fundef)
                 :inputs (fundef->inputs fundef)
                 :outputs (fundef->outputs fundef)
                 :body (block-dead (fundef->body fundef)))
    :measure (fundef-count fundef))

  :flag-local nil

  :verify-guards nil ; done below
  ///
  (verify-guards statement-dead)

  (fty::deffixequiv-mutual statements/blocks/cases/fundefs-dead)

  (defrule statement-kind-of-statement-dead
    (equal (statement-kind (statement-dead stmt))
           (statement-kind stmt))
    :expand (statement-dead stmt))

  (defrule block->statements-of-block-dead
    (equal (block->statements (block-dead block))
           (statement-list-dead (block->statements block)))
    :enable block-dead)

  (defrule block-option-dead-iff
    (iff (block-option-dead block?)
         block?)
    :expand (block-option-dead block?))

  (defrule swcase->value-of-swcase-dead
    (equal (swcase->value (swcase-dead case))
           (swcase->value case))
    :expand (swcase-dead case))

  (defrule consp-of-swcase-list-dead
    (equal (consp (swcase-list-dead cases))
           (consp cases))
    :expand (swcase-list-dead cases))

  (defrule fundef->name-of-fundef-dead
    (equal (fundef->name (fundef-dead fdef))
           (fundef->name fdef))
    :expand (fundef-dead fdef)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule swcase-list->value-list-of-swcase-list-dead
  (equal (swcase-list->value-list (swcase-list-dead cases))
         (swcase-list->value-list cases))
  :enable (swcase-list->value-list
           swcase-list-dead))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection fundef-list-dead ((x fundef-listp))
  :returns (new-fundefs fundef-listp)
  :short "Eliminate dead code in lists of function definitions."
  (fundef-dead x)
  ///
  (fty::deffixequiv fundef-list-dead))
