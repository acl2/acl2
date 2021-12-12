; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "dead-code-eliminator")
(include-book "no-loop-initializers")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dead-code-eliminator-no-loop-initializers
  :parents (transformations)
  :short "Proof that the @('DeadCodeEliminator') transformation preserves
          the condition in which loop initialization blocks are empty."

  (defthm-statements/blocks/cases/fundefs-dead-flag

    (defthm statement-noloopinitp-of-statement-dead
      (implies (statement-noloopinitp stmt)
               (statement-noloopinitp (statement-dead stmt)))
      :flag statement-dead)

    (defthm statement-list-noloopinitp-of-statement-list-dead
      (implies (statement-list-noloopinitp stmts)
               (statement-list-noloopinitp (statement-list-dead stmts)))
      :flag statement-list-dead)

    (defthm block-noloopinitp-of-block-dead
      (implies (block-noloopinitp block)
               (block-noloopinitp (block-dead block)))
      :flag block-dead)

    (defthm block-option-noloopinitp-of-block-option-dead
      (implies (block-option-noloopinitp block?)
               (block-option-noloopinitp (block-option-dead block?)))
      :flag block-option-dead)

    (defthm swcase-noloopinitp-of-swcase-dead
      (implies (swcase-noloopinitp case)
               (swcase-noloopinitp (swcase-dead case)))
      :flag swcase-dead)

    (defthm swcase-list-noloopinitp-of-swcase-list-dead
      (implies (swcase-list-noloopinitp cases)
               (swcase-list-noloopinitp (swcase-list-dead cases)))
      :flag swcase-list-dead)

    (defthm fundef-noloopinitp-of-fundef-dead
      (implies (fundef-noloopinitp fundef)
               (fundef-noloopinitp (fundef-dead fundef)))
      :flag fundef-dead)

    :hints (("Goal"
             :in-theory (enable statement-dead
                                statement-list-dead
                                block-dead
                                block-option-dead
                                swcase-dead
                                swcase-list-dead
                                fundef-dead
                                statement-noloopinitp
                                statement-list-noloopinitp
                                block-noloopinitp
                                block-option-noloopinitp
                                swcase-noloopinitp
                                swcase-list-noloopinitp
                                fundef-noloopinitp)))))
