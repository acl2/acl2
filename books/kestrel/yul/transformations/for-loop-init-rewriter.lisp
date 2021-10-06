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

(defxdoc+ for-loop-init-rewriter
  :parents (transformations)
  :short "The @('ForLoopInitRewriter') transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is described in
     [Solidity: Internals: The Optimizer: Yul-Based Optimizer Module:
      Preprocessing: ForLoopInitRewriter]."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines statements/blocks/cases/fundefs-loopinit
  :short "Mutually recursive functions to move loop initializers before loops in
          statements, blocks, cases, and function definitions."

  (define statement-loopinit ((stmt statementp))
    :returns (new-stmt statementp)
    :short "Move loop initializers before loops in statements."
    :long
    (xdoc::topstring
     (xdoc::p
      "A loop statement is turned into a block,
       consisting of the statements in the loop's initialization block
       followed by a copy of the loop but with an empty initialization block.
       Note that the initialization statments,
       the update block, and the body block
       are recursively transformed, as they may contain loop statements."))
    (statement-case
     stmt
     :block (statement-block (block-loopinit stmt.get))
     :variable-single (statement-fix stmt)
     :variable-multi (statement-fix stmt)
     :assign-single (statement-fix stmt)
     :assign-multi (statement-fix stmt)
     :funcall (statement-fix stmt)
     :if (make-statement-if :test stmt.test
                            :body (block-loopinit stmt.body))
     :for (statement-block
           (block
            (append
             (statement-list-loopinit (block->statements stmt.init))
             (list
              (make-statement-for :init (block nil)
                                  :test stmt.test
                                  :update (block-loopinit stmt.update)
                                  :body (block-loopinit stmt.body))))))
     :switch (make-statement-switch
              :target stmt.target
              :cases (swcase-list-loopinit stmt.cases)
              :default (block-option-loopinit stmt.default))
     :leave (statement-leave)
     :break (statement-break)
     :continue (statement-continue)
     :fundef (statement-fundef (fundef-loopinit stmt.get)))
    :measure (statement-count stmt))

  (define statement-list-loopinit ((stmts statement-listp))
    :returns (new-stmt statement-listp)
    :short "Move loop initializers before loops in lists of statements."
    (cond ((endp stmts) nil)
          (t (cons (statement-loopinit (car stmts))
                   (statement-list-loopinit (cdr stmts)))))
    :measure (statement-list-count stmts))

  (define block-loopinit ((block blockp))
    :returns (new-block blockp)
    :short "Move loop initializers before loops in blocks."
    (block (statement-list-loopinit (block->statements block)))
    :measure (block-count block))

  (define block-option-loopinit ((block? block-optionp))
    :returns (new-block? block-optionp)
    :short "Move loop initializers before loops in optional blocks."
    (block-option-case block?
                       :some (block-loopinit block?.val)
                       :none nil)
    :measure (block-option-count block?))

  (define swcase-loopinit ((case swcasep))
    :returns (new-case swcasep)
    :short "Move loop initializers before loops in switch cases."
    (make-swcase :value (swcase->value case)
                 :body (block-loopinit (swcase->body case)))
    :measure (swcase-count case))

  (define swcase-list-loopinit ((cases swcase-listp))
    :returns (new-cases swcase-listp)
    :short "Move loop initializers before loops in lists of switch cases."
    (cond ((endp cases) nil)
          (t (cons (swcase-loopinit (car cases))
                   (swcase-list-loopinit (cdr cases)))))
    :measure (swcase-list-count cases))

  (define fundef-loopinit ((fdef fundefp))
    :returns (new-fdef fundefp)
    :short "Move loop initializers before loops in function definitions."
    (make-fundef :name (fundef->name fdef)
                 :inputs (fundef->inputs fdef)
                 :outputs (fundef->outputs fdef)
                 :body (block-loopinit (fundef->body fdef)))
    :measure (fundef-count fdef))

  :verify-guards nil ; done below
  ///
  (verify-guards statement-loopinit)

  (fty::deffixequiv-mutual statements/blocks/cases/fundefs-loopinit))
