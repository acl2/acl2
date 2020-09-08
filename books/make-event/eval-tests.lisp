; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann (sometime before that)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Here we illustrate the must-succeed and must-fail macros, which use
; make-event to check that a form evaluates as expected.

; While we're at it, we also illustrate the use of state globals to manage
; information about expansions and check that expansion does not modify the
; world.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed" :dir :system)

; A simple test:
(must-succeed
 (defthm eval-bar
   (equal x (car (cons x y)))
   :rule-classes nil))

; The defthm just above was evaluated during expansion.  Recall that the ACL2
; logical world is reverted after expansion to its pre-expansion value, before
; the generated event is executed.  In this case, the generated event is simply
; (value-triple t).  So eval-bar should be gone from the logical world.  We
; check that now by executing a different event with name eval-bar and
; observing that there is no redefinition error.
(defun eval-bar (x) x)

; The following should not generate any output.  An interesting thing to do is
; (assign make-event-debug t) to see the expansion process.
(must-fail ; See note about ld-skip-proofsp in the definition of must-fail.
 (with-output :off :all
              (thm (equal x (cons x x)))))

; The following should not generate any output, and illustrates that we can
; nest macros that use make-event.  An interesting thing to do is (assign
; make-event-debug t) to see the expansion process.
(must-succeed
 (must-fail ; See note about ld-skip-proofsp in the definition of must-fail.
  (with-output :off :all
               (thm (equal x (cons x x))))))

; Check that a failure implies a failure of a failure of a failure (!).  While
; we're at it, we save the length of the ACL2 logical world into our own state
; global variable, for use later.
(must-succeed
 (with-output
  :off :all
  (pprogn
   (f-put-global 'saved-world-length (length (w state)) state)
   (must-fail
    (must-fail
     (must-fail ; See note about ld-skip-proofsp in the definition of must-fail.
      (with-output
       :off :all
       (thm (equal x (cons x x))))))))))

; Here we drive home the point made with eval-bar above, that expansion does
; not change the world.  The next form after this one checks that the length of
; the world is the same as it was before this one.
(must-succeed
 (defthm temp
   (equal (car (cons x y)) x)))

; See comment above.
(must-fail
 (mv (equal (f-get-global 'saved-world-length state)
            (length (w state)))
     nil
     state))

; Just beating to death the point made above.  Note that if we execute
; (defun abc (x) x)
; then this will fail.
(must-succeed
 (with-output
  :off error
  (cond ((not (eql (f-get-global 'saved-world-length state)
                   (length (w state))))
         (with-output
          :on error
          (er soft 'test-failure
              "World length changed from ~x0 to ~x1."
              (f-get-global 'saved-world-length state)
              (length (w state)))))
        (t
         (must-fail
          (must-fail
           (must-fail ; See note about ld-skip-proofsp in the definition of must-fail.
            (with-output
             :off error
             (thm (equal x (cons x x)))))))))))

; Should fail because the shape is wrong, as expansion expects an ordinary
; value or else (mv erp val state ...) where "..." denotes optional stobjs.
(must-fail
 (make-event (mv nil '(value-triple nil))))

; Above is as opposed to:
(must-succeed
 (make-event (mv nil '(value-triple nil) state)))

; We should manually inspect the .out file to see that the expansion errors are
; as expected for the following.

; Generic expansion error: "MAKE-EVENT expansion for (MV T NIL STATE) caused an
; error."
(must-fail
 (make-event
  (mv t nil state)))

; Should print "Sample Expansion Error".
(must-fail
 (make-event
  (mv "Sample Expansion Error" nil state)))

; Should print "Sample Expansion Error: 17, howdy 23".
(must-fail
 (make-event
  (mv (msg "Sample Expansion Error: ~x0, ~@1"
           17
           (msg "howdy ~x0"
                23))
      nil
      state)))
