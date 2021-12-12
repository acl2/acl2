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
(include-book "no-function-definitions")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dead-code-eliminator-no-function-definitions
  :parents (transformations)
  :short "Proof that the @('DeadCodeEliminator') transformation preserves
          the condition in which functions are defined elsewhere."

  (defthm-statements/blocks/cases/fundefs-dead-flag

    (defthm statement-nofunp-of-statement-dead
      (implies (statement-nofunp stmt)
               (statement-nofunp (statement-dead stmt)))
      :flag statement-dead)

    (defthm statement-list-nofunp-of-statement-list-dead
      (implies (statement-list-nofunp stmts)
               (statement-list-nofunp (statement-list-dead stmts)))
      :flag statement-list-dead)

    (defthm block-nofunp-of-block-dead
      (implies (block-nofunp block)
               (block-nofunp (block-dead block)))
      :flag block-dead)

    (defthm block-option-nofunp-of-block-option-dead
      (implies (block-option-nofunp block?)
               (block-option-nofunp (block-option-dead block?)))
      :flag block-option-dead)

    (defthm swcase-nofunp-of-swcase-dead
      (implies (swcase-nofunp case)
               (swcase-nofunp (swcase-dead case)))
      :flag swcase-dead)

    (defthm swcase-list-nofunp-of-swcase-list-dead
      (implies (swcase-list-nofunp cases)
               (swcase-list-nofunp (swcase-list-dead cases)))
      :flag swcase-list-dead)

    (defthm fundef-nofunp-of-fundef-dead
      (implies (fundef-nofunp fundef)
               (fundef-nofunp (fundef-dead fundef)))
      :flag fundef-dead)

    :hints (("Goal"
             :in-theory (enable statement-dead
                                statement-list-dead
                                block-dead
                                block-option-dead
                                swcase-dead
                                swcase-list-dead
                                fundef-dead
                                statement-nofunp
                                statement-list-nofunp
                                block-nofunp
                                block-option-nofunp
                                swcase-nofunp
                                swcase-list-nofunp
                                fundef-nofunp)))))
