; This examples in this book were produced by Claude and passed along by Eric
; Smith.  They illustrates unsoundness, fixed before ACL2 Version 8.8, due to
; some proof-builder state globals not being untouchable.

(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

; Example 1

(must-fail
 (defthm pcb-nil
   nil
   :rule-classes nil
   :instructions ((:sequence nil nil nil
                             (pprogn (pc-assign state-stack
                                                (list (change-pc-state
                                                       (car (state-stack))
                                                       :goals nil)))
                                     (mv nil t state))))))

; Example 2

(must-fail
 (defthm pcb-nil3
   nil
   :rule-classes nil
   :hints (("Goal" :instructions
            ((:sequence nil nil nil
                        (pprogn (pc-assign state-stack
                                           (list (change-pc-state
                                                  (car (state-stack))
                                                  :goals nil)))
                                (mv nil t state))))))))

; Example 3

(program)
(set-state-ok t)
(must-fail
 (define-pc-macro pcb-clobber ()
   (pprogn (pc-assign state-stack
                      (list (change-pc-state (car (state-stack)) :goals nil)))
           (value 'comment))))
; The rest of this exampole is irrelevant, since the pc-macro pcb-clobber was
; not admitted.
#|
(logic)
(must-fail (defthm pcb-nil2 nil :rule-classes nil :instructions (pcb-clobber)))
|#
