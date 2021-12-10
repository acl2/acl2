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

(defxdoc+ no-function-definitions
  :parents (transformations)
  :short "The condition in which function definitions are elsewhere."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('FunctionHoister') transformation, described in
     [Solidity: Internals: The Optimizer: Yul-Based Optimizer Module:
      Preprocessing: FuntionHoister],
     moves all the function definitions to the top-level block.
     The @('FunctionGrouper') transformation, described in
     [Solidity: Internals: The Optimizer: Yul-Based Optimizer Module:
      Preprocessing: FuntionGrouper],
     further moves them to the end of the top-level block,
     putting the rest of the top-level block into a nested block
     at the beginning of the top-level block.
     An important property that these transformations establish
     is that, aside from the top-level block,
     there are no function definitions in statements and blocks.")
   (xdoc::p
    "Here we capture this property,
     which is used as precondition for certain transformations."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines statements/blocks/cases/fundefs-nofunp
  :short "Mutually recursive functions that check
          the absence of function definitions in
          statements, blocks, cases, and function definitions."

  (define statement-nofunp ((stmt statementp))
    :returns (yes/no booleanp)
    :short "Check that a statement has no function definitions."
    :long
    (xdoc::topstring
     (xdoc::p
      "We disallow statements that are function definitions obviously,
       and we recursive check all the nested blocks and switch cases."))
    (statement-case
     stmt
     :block (block-nofunp stmt.get)
     :variable-single t
     :variable-multi t
     :assign-single t
     :assign-multi t
     :funcall t
     :if (block-nofunp stmt.body)
     :for (and (block-nofunp stmt.init)
               (block-nofunp stmt.update)
               (block-nofunp stmt.body))
     :switch (and (swcase-list-nofunp stmt.cases)
                  (block-option-nofunp stmt.default))
     :leave t
     :break t
     :continue t
     :fundef nil)
    :measure (statement-count stmt))

  (define statement-list-nofunp ((stmts statement-listp))
    :returns (yes/no booleanp)
    :short "Check that a list of statements has no function definitions."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check each statement in the list."))
    (or (endp stmts)
        (and (statement-nofunp (car stmts))
             (statement-list-nofunp (cdr stmts))))
    :measure (statement-list-count stmts))

  (define block-nofunp ((block blockp))
    :returns (yes/no booleanp)
    :short "Check that a block has no function definitions."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check the statements in the block."))
    (statement-list-nofunp (block->statements block))
    :measure (block-count block))

  (define block-option-nofunp ((block? block-optionp))
    :returns (yes/no booleanp)
    :short "Check that an optional block has no function definitions."
    :long
    (xdoc::topstring
     (xdoc::p
      "The check succeeds if there is no block.
       If there is a block, we check it."))
    (block-option-case block?
                       :some (block-nofunp block?.val)
                       :none t)
    :measure (block-option-count block?))

  (define swcase-nofunp ((case swcasep))
    :returns (yes/no booleanp)
    :short "Check that a switch case has no function definitions."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check the underlying block."))
    (block-nofunp (swcase->body case))
    :measure (swcase-count case))

  (define swcase-list-nofunp ((cases swcase-listp))
    :returns (yes/no booleanp)
    :short "Check that a list of switch cases has no function definitions."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check each switch case in the list."))
    (or (endp cases)
        (and (swcase-nofunp (car cases))
             (swcase-list-nofunp (cdr cases))))
    :measure (swcase-list-count cases))

  (define fundef-nofunp ((fundef fundefp))
    :returns (yes/no booleanp)
    :short "Check that a function definition has no function definitions."
    :long
    (xdoc::topstring
     (xdoc::p
      "The function definition itself is okay:
       we just check that its body has no function definitions.
       This is the condition of all the function definitions
       after the @('FunctionHoister') transformation."))
    (block-nofunp (fundef->body fundef))
    :measure (fundef-count fundef))

  :flag-local nil

  ///

  (fty::deffixequiv-mutual statements/blocks/cases/fundefs-nofunp))
