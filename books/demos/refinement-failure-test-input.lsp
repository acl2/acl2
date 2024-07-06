; Copyright (C) 2024, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This script carries out the three experiments described :DOC
; refinement-failure.

; Experiment 1: We constrain the relevant functions to have all the properties
; allowing a certain proof to succeed.  We then invoke THM after installing a
; monitor on RULE.  When RULE is tried the :condition component of the monitor
; issues the :PATH+ command to display the path (which includes the geneqv at
; each active rewrite frame) and then proceeds with :GO.  The proof succeeds.

; Experiment 2: We ``forget'' to prove that g2eq1 refines g2eq1, and repeat
; the same THM.  We get a refinement failure break and the :path+ reveals
; that g2eq1! is not a refinement of the geneqv (g2eq1 g2eq2).

; Experiment 3: Instead of forgetting the refinement property we ``forget'' to
; prove the congruence property linking g2eq1 to feq.  Repeating the THM
; reveals that the geneqv is now just (g2eq2), which should inform the user of
; the missing congruence rule.

; On the Structure of this Script: We use constrained functions here simply to
; avoid unnecessary details, e.g., what does the equivalence relation g2eq2
; actually test?  It doesn't matter, as long as it provides the necessary
; congruence relation.  But the use of constrained functions sort of limits our
; demo.  We demonstrate success in experiment 1 and then demonstrate two
; failure modes in experiments 2 and 3.  A more ``natural'' demo might be to
; define all the equivalence relations concretely but omit to prove, say, the
; refinement property.  Then we could demonstrate the thm failing, prove the
; refinement property, and demonstrate that it fixes the problem.  But we can't
; incrementally add constraints.  So we have to undo the complete set of
; constraints and redo the new ones.  (Obscurely relevant remark for experts:
; refinement rules cannot be disabled.)

; Arrange for *standard-co* to be (standard-co state), so that we can see the
; output from brr (via brr-wormhole).
(defttag :refinement-failure)
(set-raw-mode t)
(defvar *saved-standard-co* *standard-co*)
(progn (setq *standard-co* (standard-co state)) ; avoid output
       t)
(set-raw-mode nil)
(u) ; undo the defttag form

; Experiment 1: Show success.

(encapsulate (((p *) => *)
              ((f *) => *)
              ((g * *) => *)
              ((peq * *) => *)
              ((feq * *) => *)
              ((g2eq1 * *) => *)
              ((g2eq1! * *) => *)
              ((g2eq2 * *) => *)
              ((beta *) => *)
              ((gamma *) => *))
  (local (defun p (x) (equal x (car (cons x x)))))
  (local (defun f (x) x))
  (local (defun g (x y) (declare (ignore x)) y))
  (local (defun peq (x y) (equal x y)))
  (local (defun feq (x y) (equal x y)))
  (local (defun g2eq1 (x y) (equal x y)))
  (local (defun g2eq1! (x y) (equal x y)))
  (local (defun g2eq2 (x y) (equal x y)))
  (local (defun beta (x) x))
  (local (defun gamma (x) x))
  (defequiv peq)
  (defequiv feq)
  (defequiv g2eq1)
  (defequiv g2eq1!)
  (defequiv g2eq2)
  (defrefinement g2eq1! g2eq1)
  (defcong peq iff (p x) 1)
  (defcong feq peq (f x) 1)
  (defcong g2eq1 feq (g x y) 2)
  (defcong g2eq2 feq (g x y) 2)
  (defthm rule (g2eq1! (beta x) (gamma x)))
  (defthm done (p (f (g x (gamma y)))))
  )

(brr t)
(monitor 'rule
         '(:condition (and (equal (brr@ :target) '(BETA B))
                           '(:path+ :go))
           :rf t))
(thm (p (f (g a (beta b))))
     :hints (("Goal" :do-not '(preprocess))))

; Note: The hint above is required since we've monitored a simple abbreviation
; rule.  See :DOC monitor.

; Next we do an undo.  The brr, monitor, and thm commands just above did not
; change the logical world, so the undo command below actually erases the
; encapsulate, leaving brr still enabled and leaving a monitor on the now
; non-existent rule.  But we'll define RULE again.

(u)

; Experiment 2: Show refinement failure due to lack of a refinement rule.

(encapsulate (((p *) => *)
              ((f *) => *)
              ((g * *) => *)
              ((peq * *) => *)
              ((feq * *) => *)
              ((g2eq1 * *) => *)
              ((g2eq1! * *) => *)
              ((g2eq2 * *) => *)
              ((beta *) => *)
              ((gamma *) => *))
  (local (defun p (x) (equal x (car (cons x x)))))
  (local (defun f (x) x))
  (local (defun g (x y) (declare (ignore x)) y))
  (local (defun peq (x y) (equal x y)))
  (local (defun feq (x y) (equal x y)))
  (local (defun g2eq1 (x y) (equal x y)))
  (local (defun g2eq1! (x y) (equal x y)))
  (local (defun g2eq2 (x y) (equal x y)))
  (local (defun beta (x) x))
  (local (defun gamma (x) x))
  (defequiv peq)
  (defequiv feq)
  (defequiv g2eq1)
  (defequiv g2eq1!)
  (defequiv g2eq2)
; (defrefinement g2eq1! g2eq1)  ; <-- We ``forgot'' to prove this!
  (defcong peq iff (p x) 1)
  (defcong feq peq (f x) 1)
  (defcong g2eq1 feq (g x y) 2)
  (defcong g2eq2 feq (g x y) 2)
  (defthm rule (g2eq1! (beta x) (gamma x)))
  (defthm done (p (f (g x (gamma y)))))
  )

(thm (p (f (g a (beta b))))
     :hints (("Goal" :do-not '(preprocess))))

; We showed in Experiment 1 that had we proved the missing refinement rule, the
; proof would succeed.

; undo the encapsulate

(u)

; Experiment 3: Show refinement failure due to lack of a congruence rule.

(encapsulate (((p *) => *)
              ((f *) => *)
              ((g * *) => *)
              ((peq * *) => *)
              ((feq * *) => *)
              ((g2eq1 * *) => *)
              ((g2eq1! * *) => *)
              ((g2eq2 * *) => *)
              ((beta *) => *)
              ((gamma *) => *))
  (local (defun p (x) (equal x (car (cons x x)))))
  (local (defun f (x) x))
  (local (defun g (x y) (declare (ignore x)) y))
  (local (defun peq (x y) (equal x y)))
  (local (defun feq (x y) (equal x y)))
  (local (defun g2eq1 (x y) (equal x y)))
  (local (defun g2eq1! (x y) (equal x y)))
  (local (defun g2eq2 (x y) (equal x y)))
  (local (defun beta (x) x))
  (local (defun gamma (x) x))
  (defequiv peq)
  (defequiv feq)
  (defequiv g2eq1)
  (defequiv g2eq1!)
  (defequiv g2eq2)
  (defrefinement g2eq1! g2eq1)
  (defcong peq iff (p x) 1)
  (defcong feq peq (f x) 1)
; (defcong g2eq1 feq (g x y) 2)  ; <-- We ``forgot'' to prove this!
  (defcong g2eq2 feq (g x y) 2)
  (defthm rule (g2eq1! (beta x) (gamma x)))
  (defthm done (p (f (g x (gamma y)))))
  )

(thm (p (f (g a (beta b))))
     :hints (("Goal" :do-not '(preprocess))))

; We showed in Experiment 1 that had we proved the missing congruence rule, the
; proof would succeed.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defttag :refinement-failure)
(set-raw-mode t)
(setq *standard-co* *saved-standard-co*)
(set-raw-mode nil)
(u) ; undo the defttag form

