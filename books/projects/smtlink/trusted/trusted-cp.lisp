;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "prove")
(set-state-ok t)

(defsection SMT-trusted-cp
  :parents (trusted)
  :short "The trusted clause processor"

  (defstub SMT-prove-stub (term smtlink-hint state) (mv t nil state))

  (program)
  (defttag :Smtlink)

  (progn

; We wrap everything here in a single progn, so that the entire form is
; atomic.  That's important because we want the use of push-untouchable to
; prevent anything besides SMT-proves-stub from calling SMT-prove.

    (progn!

     (set-raw-mode-on state)

     (defun SMT-prove-stub (term smtlink-hint state)
       (SMT-prove term smtlink-hint state)))

    (define SMT-trusted-cp-main ((cl pseudo-term-listp)
                                 (smtlink-hint)
                                 state)
      :stobjs state
      :mode :program
      (b* (((mv res precond state)
            (SMT-prove-stub (disjoin cl) smtlink-hint state))
           ;; should I return just precond, or precond and precond\or/goal?
           (subgoal-lst `(,@precond
                          ;; ((hint-please
                          ;;   '(:in-theory (enable hint-please
                          ;;                        type-hyp)
                          ;;     :expand ((:free (x) (hide x)))))
                          ;;  ,@precond
                          ;;  ,(disjoin cl))
                          )))
        (if res
            (prog2$ (cw "Proved!~%") (mv nil subgoal-lst state))
          (mv (cons "NOTE: Unable to prove goal with ~
                      SMT-trusted-cp and indicated hint." nil)
              (list cl) state))))

    (push-untouchable SMT-prove-stub t)
    )

  (logic)

  (define SMT-trusted-cp ((cl pseudo-term-listp)
                          (smtlink-hint smtlink-hint-p)
                          state)
    :mode :program
    :stobjs state
    (prog2$ (cw "Using default SMT-trusted-cp...~%")
            (SMT-trusted-cp-main cl smtlink-hint state)))

  (define SMT-trusted-cp-custom ((cl pseudo-term-listp)
                                 (smtlink-hint smtlink-hint-p)
                                 state)
    :mode :program
    :stobjs state
    (prog2$ (cw "Using custom SMT-trusted-cp...~%")
            (SMT-trusted-cp-main cl smtlink-hint state)))

  (define-trusted-clause-processor
    SMT-trusted-cp
    nil
    :ttag Smtlink)

  (define-trusted-clause-processor
    SMT-trusted-cp-custom
    nil
    :ttag Smtlink-custom)
  )
