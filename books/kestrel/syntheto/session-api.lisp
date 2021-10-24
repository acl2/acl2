; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;

(define top-command-number-fn (state)
  ;; :verbosep t
  :returns (num integerp)
  :verify-guards nil
  :short "Returns the number of the most recent top-level ACL2 command."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a new @(tsee command) is accepted by the ACL2 top-level interface,
     the top command number is incremented and assigned to the new command.")
   (xdoc::p
    "You can see the numbers assigned to your commands with the @(tsee pbt)
     history function.")
   (xdoc::p
    "Some @(tsee history) functions that can change the top command number include
     @(tsee u), @(tsee ubu!), and (tsee reset-prehistory), for example."))
  (let* ((wrld (w state))
         (base-info (global-val 'command-number-baseline-info wrld))
         (command-number-base (access command-number-baseline-info base-info :current))
         (command-number-current (access-command-tuple-number (cddar wrld)))
         (user-command-number-current (- command-number-current command-number-base)))
    (if (integerp user-command-number-current)
        user-command-number-current
      0)))

(defmacro top-command-number ()
  '(top-command-number-fn state))

(set-state-ok t)

(defun undo-commands-fn (number-of-commands-to-undo state)
  (declare (xargs :mode :program)) ; because ubt!-ubu!-fn is program mode
  (if (not (natp number-of-commands-to-undo))
      (prog2$ (cw "bad argument to undo-commands-fn")
              (mv nil nil state))
    (let* ((current-top (top-command-number-fn state))
           (goal-top (- current-top number-of-commands-to-undo)))
      (if (< goal-top 0)
          (prog2$ (cw "undoing into prehistory not supported")
                  (mv nil nil state))
        (ubu! goal-top)))))

(defmacro undo-commands (num-commands)
  `(undo-commands-fn ,num-commands state))
