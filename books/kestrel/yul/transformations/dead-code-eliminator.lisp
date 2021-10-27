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
     The description mentions not only @('leave'), @('break') and @('continue'),
     but also other constructs that are presumably part of the EVM dialect;
     since they are not part of our formalization,
     we do not handle the latter for now."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines statements/blocks/cases/fundefs-dead
  :short "Mutually recursive functions to eliminate dead code in
          statements, blocks, cases, and function definitions."

  (define statement-dead ((stmt statementp))
    :returns (new-stmt statementp)
    :short "Eliminate dead code in statements."
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

  (define statement-list-dead ((stmts statement-listp) (afterp booleanp))
    :returns (new-stmt statement-listp)
    :short "Eliminate dead code in lists of statements."
    :long
    (xdoc::topstring
     (xdoc::p
      "This function takes a flag saying whether
       the statements being examined come after (hence the name)
       a @('leave'), @('break'), or @('continue') statement.
       The flag is initially false (set by @(tsee block-dead)),
       and becomes true when we encounter one of those three statements.
       So long as the flag is false, we keep the statements,
       recursively transforming them.
       When the flag is true, we only keep function definitions,
       recursively transforming them.")
     (xdoc::p
      "Note that we cannot simply stop
       when we encounter a @('leave'), @('break'), or @('continue')
       and discard everything after it,
       because we still need to keep the function definitions."))
    (b* (((when (endp stmts)) nil)
         (stmt (car stmts))
         (next-afterp (or afterp
                          (statement-case stmt :leave)
                          (statement-case stmt :break)
                          (statement-case stmt :continue))))
      (if (or (not afterp)
              (statement-case stmt :fundef))
          (cons (statement-dead stmt)
                (statement-list-dead (cdr stmts) next-afterp))
        (statement-list-dead (cdr stmts) next-afterp)))
    :measure (statement-list-count stmts))

  (define block-dead ((block blockp))
    :returns (new-block blockp)
    :short "Eliminate dead code in blocks."
    (block (statement-list-dead (block->statements block) nil))
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

  (define fundef-dead ((fdef fundefp))
    :returns (new-fdef fundefp)
    :short "Eliminate dead code in function definitions."
    (make-fundef :name (fundef->name fdef)
                 :inputs (fundef->inputs fdef)
                 :outputs (fundef->outputs fdef)
                 :body (block-dead (fundef->body fdef)))
    :measure (fundef-count fdef))

  :flag-local nil

  :verify-guards nil ; done below
  ///
  (verify-guards statement-dead)

  (fty::deffixequiv-mutual statements/blocks/cases/fundefs-dead)

  (defrule statement-kind-of-statement-dead
    (equal (statement-kind (statement-dead stmt))
           (statement-kind stmt))
    :expand (statement-dead stmt))

  (defrule statement-fundef->get-of-statement-dead
    (implies (statement-case stmt :fundef)
             (equal (statement-fundef->get (statement-dead stmt))
                    (fundef-dead (statement-fundef->get stmt))))
    :enable statement-dead)

  (defruled block->statements-of-block-dead
    (equal (block->statements (block-dead block))
           (statement-list-dead (block->statements block) nil))
    :enable block-dead)

  (defrule swcase->value-of-swcase-dead
    (equal (swcase->value (swcase-dead case))
           (swcase->value case))
    :expand (swcase-dead case))

  (defrule fundef->name-of-fundef-dead
    (equal (fundef->name (fundef-dead fdef))
           (fundef->name fdef))
    :expand (fundef-dead fdef)))
