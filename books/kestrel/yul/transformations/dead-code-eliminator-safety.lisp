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
(include-book "dead-code-eliminator-nofun")
(include-book "no-loop-initializers")

(include-book "../language/static-safety-checking")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dead-code-eliminator-static-safety
  :parents (transformations)
  :short "Proof that the @('DeadCodeEliminator') transformation preserves
          the static safety checks."

  (defthm-check-safe-statements/blocks/cases/fundefs-flag

    (defthm check-safe-statement-of-statement-dead
      (implies (and (statement-nofunp stmt)
                    (statement-noloopinitp stmt))
               (b* ((varsmodes (check-safe-statement stmt varset funtab))
                    (varsmodes-dead
                     (check-safe-statement (statement-dead stmt)
                                           varset
                                           funtab)))
                 (implies (not (resulterrp varsmodes))
                          (and (not (resulterrp varsmodes-dead))
                               (equal
                                (vars+modes->vars varsmodes-dead)
                                (vars+modes->vars varsmodes))
                               (set::subset
                                (vars+modes->modes varsmodes-dead)
                                (vars+modes->modes varsmodes))))))
      :flag check-safe-statement)

    (defthm check-safe-statement-list-of-statement-list-dead
      (implies (and (statement-list-nofunp stmts)
                    (statement-list-noloopinitp stmts))
               (b* ((varsmodes
                     (check-safe-statement-list stmts varset funtab))
                    (varsmodes-dead
                     (check-safe-statement-list (statement-list-dead stmts)
                                                varset
                                                funtab)))
                 (implies (not (resulterrp varsmodes))
                          (and (not (resulterrp varsmodes-dead))
                               (set::subset
                                (vars+modes->modes varsmodes-dead)
                                (vars+modes->modes varsmodes))))))
      :flag check-safe-statement-list)

    (defthm check-safe-block-of-block-dead
      (implies (and (block-nofunp block)
                    (block-noloopinitp block))
               (b* ((modes (check-safe-block block varset funtab))
                    (modes-dead (check-safe-block (block-dead block)
                                                  varset
                                                  funtab)))
                 (implies (not (resulterrp modes))
                          (and (not (resulterrp modes-dead))
                               (set::subset modes-dead modes)))))
      :flag check-safe-block)

    (defthm check-safe-block-option-of-block-option-dead
      (implies (and (block-option-nofunp block?)
                    (block-option-noloopinitp block?))
               (b* ((modes (check-safe-block-option block? varset funtab))
                    (modes-dead
                     (check-safe-block-option (block-option-dead block?)
                                              varset
                                              funtab)))
                 (implies (not (resulterrp modes))
                          (and (not (resulterrp modes-dead))
                               (set::subset modes-dead modes)))))
      :flag check-safe-block-option)

    (defthm check-safe-swcase-of-swcase-dead
      (implies (and (swcase-nofunp case)
                    (swcase-noloopinitp case))
               (b* ((modes (check-safe-swcase case varset funtab))
                    (modes-dead (check-safe-swcase (swcase-dead case)
                                                   varset
                                                   funtab)))
                 (implies (not (resulterrp modes))
                          (and (not (resulterrp modes-dead))
                               (set::subset modes-dead modes)))))
      :flag check-safe-swcase)

    (defthm check-safe-swcase-list-of-swcase-list
      (implies (and (swcase-list-nofunp cases)
                    (swcase-list-noloopinitp cases))
               (b* ((modes (check-safe-swcase-list cases varset funtab))
                    (modes-dead (check-safe-swcase-list (swcase-list-dead cases)
                                                        varset
                                                        funtab)))
                 (implies (not (resulterrp modes))
                          (and (not (resulterrp modes-dead))
                               (set::subset modes-dead modes)))))
      :flag check-safe-swcase-list)

    (defthm check-safe-fundef-of-fundef-dead
      (implies (and (fundef-nofunp fundef)
                    (fundef-noloopinitp fundef)
                    (not (resulterrp (check-safe-fundef fundef funtab))))
               (not (resulterrp
                     (check-safe-fundef (fundef-dead fundef) funtab))))
      :flag check-safe-fundef)

    :hints (("Goal"
             :in-theory
             (enable check-safe-statement
                     check-safe-statement-list
                     check-safe-block
                     check-safe-block-option
                     check-safe-swcase
                     check-safe-swcase-list
                     check-safe-fundef
                     statement-dead
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
                     fundef-nofunp
                     statement-noloopinitp
                     statement-list-noloopinitp
                     block-noloopinitp
                     block-option-noloopinitp
                     swcase-noloopinitp
                     swcase-list-noloopinitp
                     fundef-noloopinitp
                     set::subset-in-2
                     not-resulterrp-when-mode-setp
                     mode-setp-when-mode-set-resultp-and-not-resulterrp
                     set::subset-of-union-and-union
                     set::union-subset-x
                     set::subset-transitive)
             :expand (check-safe-statement stmt varset funtab)))))
