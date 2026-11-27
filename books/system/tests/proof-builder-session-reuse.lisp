; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug fixed before ACL2 Version 8.8.

; Inside the interactive proof-builder loop, the :instructions of an event
; were not run; instead, the event was accepted when the current proof-builder
; session had no remaining goals.  That shortcut is intended for the event
; submitted by the proof-builder's exit command, but it did not check that the
; session was for the event's goal, or that the session had been carried out
; in a world that the current world extends.  Below, the loop is entered by
; calling verify-fn during make-event expansion.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

; A defthm of nil, submitted with the proof-builder's lisp command, was
; accepted because the session for (equal x x) was complete.

(must-fail
 (make-event
  (er-progn
   (verify-fn '(equal x x) t nil nil
              '(:prove
                (:lisp (defthm bad1 nil
                         :rule-classes nil
                         :instructions (:prove)))
                :exit)
              state)
   (thm nil :hints (("Goal" :use bad1)))
   (value '(value-triple :nil-proved)))))

; A session completed in a world that was then undone (here, by leaving the
; encapsulate) was used by exit to prove the session's goal in a world where
; it is false.

(encapsulate
  ()
  (local (defun f (x) (declare (ignore x)) 1))
  (local (defthm f-is-1 (equal (f x) 1) :instructions (:prove))))

(defun f (x) (declare (ignore x)) 2)

(must-fail
 (make-event
  (er-progn
   (verify-fn nil nil nil nil '((:exit bad2 nil t) :exit) state)
   (thm nil :hints (("Goal" :use (:instance bad2 (x 0)))))
   (value '(value-triple :nil-proved)))))

; Exit still stores the theorem proved by the session, also when resuming a
; session in an extension of its world.

(defun g (x) (declare (ignore x)) 3)

(defthm g-is-3 (equal (g x) 3) :instructions (:prove))

(defun h (x) x)

(make-event
 (er-progn
  (verify-fn nil nil nil nil '((:exit g-is-3-again nil t) :exit) state)
  (verify-fn '(equal (g (h x)) 3) t nil nil
             '(:prove (:exit g-h-is-3 nil t) :exit)
             state)
  (if (and (getpropc 'g-is-3-again 'theorem nil (w state))
           (getpropc 'g-h-is-3 'theorem nil (w state)))
      (value '(value-triple :ok))
    (er soft 'proof-builder-session-reuse
        "Exit failed to store a theorem."))))
