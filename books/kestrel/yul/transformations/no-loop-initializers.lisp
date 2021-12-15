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

(defxdoc+ no-loop-initializers
  :parents (transformations)
  :short "The condition in which loop initialization blocks are empty."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('ForLoopInitRewriter') transformation
     moves the statements in each loop's initialization block
     just before the loop.
     This makes all the loop initialization blocks empty.
     Here we formalize this condition,
     which is needed to prove the correctness of certain transformations."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines statements/blocks/cases/fundefs-noloopinitp
  :short "Mutually recursive functions that check
          the emptiness of loop initialization blocks in
          statements, blocks, cases, and function definitions."

  (define statement-noloopinitp ((stmt statementp))
    :returns (yes/no booleanp)
    :short "Check that a statement has empty loop initialization blocks."
    (statement-case
     stmt
     :block (block-noloopinitp stmt.get)
     :variable-single t
     :variable-multi t
     :assign-single t
     :assign-multi t
     :funcall t
     :if (block-noloopinitp stmt.body)
     :for (and (endp (block->statements stmt.init))
               (block-noloopinitp stmt.update)
               (block-noloopinitp stmt.body))
     :switch (and (swcase-list-noloopinitp stmt.cases)
                  (block-option-noloopinitp stmt.default))
     :leave t
     :break t
     :continue t
     :fundef (fundef-noloopinitp stmt.get))
    :measure (statement-count stmt))

  (define statement-list-noloopinitp ((stmts statement-listp))
    :returns (yes/no booleanp)
    :short "Check that a list of statements
            has empty loop initialization blocks."
    (or (endp stmts)
        (and (statement-noloopinitp (car stmts))
             (statement-list-noloopinitp (cdr stmts))))
    :measure (statement-list-count stmts))

  (define block-noloopinitp ((block blockp))
    :returns (yes/no booleanp)
    :short "Check that a block has empty loop initialization blocks."
    (statement-list-noloopinitp (block->statements block))
    :measure (block-count block))

  (define block-option-noloopinitp ((block? block-optionp))
    :returns (yes/no booleanp)
    :short "Check that an optional block has empty loop initialization blocks."
    (block-option-case block?
                       :some (block-noloopinitp block?.val)
                       :none t)
    :measure (block-option-count block?))

  (define swcase-noloopinitp ((case swcasep))
    :returns (yes/no booleanp)
    :short "Check that a switch case has empty loop initialization blocks."
    (block-noloopinitp (swcase->body case))
    :measure (swcase-count case))

  (define swcase-list-noloopinitp ((cases swcase-listp))
    :returns (yes/no booleanp)
    :short "Check that a list of switch cases
            has empty loop initialization blocks."
    (or (endp cases)
        (and (swcase-noloopinitp (car cases))
             (swcase-list-noloopinitp (cdr cases))))
    :measure (swcase-list-count cases))

  (define fundef-noloopinitp ((fundef fundefp))
    :returns (yes/no booleanp)
    :short "Check that a function definition
            has empty loop initialization blocks."
    (block-noloopinitp (fundef->body fundef))
    :measure (fundef-count fundef))

  :flag-local nil

  ///

  (fty::deffixequiv-mutual statements/blocks/cases/fundefs-noloopinitp)

  (defrule block-option-noloopinitp-when-blockp
    (implies (blockp block)
             (equal (block-option-noloopinitp block)
                    (block-noloopinitp block)))
    :enable block-option-some->val))
