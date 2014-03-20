; Copyright (C) 2014, Regents of the University of Texas
; Written by Matt Kaufmann and Nathan Wetzler (original date March, 2014)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; ===================================================================

; When event is a successful event (defthm name (implies ...) ...)  then the
; form (remove-hyps event) results in storing a modified version of this event
; in which, essentially, the hypotheses have been reduced to a minimal set.

; Possible enhancements include:

; - Printing the final event if hypotheses were eliminated

; - Hiding the output (optionally)

; - Supporting a mode where the new event isn't actually submitted

; - Taking advantage of the :OR feature of make-event to avoid repeated
;   evaluation in some cases

; - Using the :DO-PROOFS feature of make-event to ensure proper operation event
;   when skipping proofs (e.g., calling rebuild)

; - Using the :EXPANSION? feature of make-event to avoid storing the make-event
;   expansion in the certificate, in the common case where no hypotheses are
;   eliminated

; - Adding documentation (via the XDOC system)

; - Moving event destruction to a separate function (similar to event
;   construction now

; - Support for other forms such as defrule

;; ===================================================================

(in-package "ACL2")

;; We will be programming with state.
(set-state-ok t)
;; This is a utility and we do not wish to reason about termination.
(program)


;; ============================ HEURISTIC ============================

;; This function provides a limit on the number of steps for any derivative of
;; the original theorem.  We want to avoid a situation where removing some
;; hypothesis places the prover in a state where it is "out to lunch".  This
;; puts an upper bound on the number of prover steps (and hopefully time) the
;; remove-hyps tool will use.
(defun remove-hyps-formula-steps (steps)
  (+ 1000 (* 3 steps)))


;; ======================= DEFTHM CONSTRUCTION =======================

;; The dumb-implicate function constructs an implicate based on a list of
;; hypotheses.  If there are no hypotheses, the implicate is simply the
;; conclusion.  If there is exactly one hypothesis, we don't need to splice in
;; an "and".  Finally, if there is more than one hypothesis, an "and" is used
;; to conjoin the hypotheses.
(defun dumb-implicate (hyps concl)
  (cond ((null hyps) concl)
        ((null (cdr hyps)) `(implies ,(car hyps) ,concl))
        (t `(implies (and ,@hyps) ,concl))))

;; This function creates a defthm event using the dumb-implicate function to
;; create the form.
(defun make-defthm (name hyps concl kwd-alist)
  `(defthm ,name
     ,(dumb-implicate hyps concl)
     ,@kwd-alist))


;; ======================== DEFTHM EXECUTION =========================

;; The event-steps function performs two tasks.  The first is testing a
;; (defthm) form for success/failure.  The second is calculating the number of
;; prover steps used in a successful event.  Thus, the presence/absence of a
;; return value indicates the success/failure of the form.
(defun event-steps (form state)
  (let ((new-form
         ; The progn will revert the state if one of the events fails, which we
         ; guarantee with an ill-formed event.
         `(progn ; First set a global variable to nil in case of failure.
                 (make-event (pprogn (f-put-global 'our-steps nil state)
                                     (value '(value-triple nil))))
                 ; Try to execute a given form.
                 ,form
                 ; Record the number of prover steps used in the last event.
                 (make-event (pprogn (f-put-global 'our-steps
                                                   (last-prover-steps state)
                                                   state)
                                     (value '(value-triple nil))))
                 ; Cause a failure by using an ill-formed defconst event.
                 (defconst *bad*) ; Note: no args!
                 )))

    (er-progn
     ; Evaluate the new form constructed above.
     (trans-eval new-form 'event-steps state t)
     ; Return the value stored in the global variable.
     (value (f-get-global 'our-steps state)))))


;; ====================== REMOVE-HYPS ALGORITHM ======================

;; The main procedure of remove-hyps.  This function takes a list of necessary
;; hypotheses and a list of unknown hypotheses, the second and third arguments
;; respectively.  It then appends the two lists of hypotheses with the first
;; element of the unknown list removed.  This creates an event with all
;; hypotheses deemed necessary so far conjoined with all remaining hypotheses
;; to be tested (minus the hypothesis being tested).
(defun remove-hyps-formula-1 (name rev-init-hyps rest-hyps concl kwd-alist
                                   steps state)

  (cond
   ; If there are no more hypotheses to test, then return the reverse of the
   ; necessary hypotheses.
   ((endp rest-hyps) (value (reverse rev-init-hyps)))
   ; Create a new form by appending the necessary hypotheses to the cdr of the
   ; unknown hypotheses.  Limit the number of steps based on the heuristic
   ; above.
   (t (let ((form `(with-prover-step-limit
                    ,steps
                    ,(make-defthm name
                                  (revappend rev-init-hyps (cdr rest-hyps))
                                  concl kwd-alist))))
        ; Try the new event.
        (er-let* ((event-steps (event-steps form state)))
          ; Recur with the cdr of the unknown hypotheses, but...
          (remove-hyps-formula-1
           name
           ; Modify the necessary hypotheses based on the result of the last
           ; event.
           (cond ((null event-steps)
                  (cons (car rest-hyps) rev-init-hyps))
                 (t rev-init-hyps))
           (cdr rest-hyps)
           concl kwd-alist steps state))))))

;; This function obtains a count for the number of steps the original form (if
;; it even succeeds!) and then calls a recursive procedure to try the form
;; without each hypothesis.
(defun remove-hyps-formula (form name hyps concl kwd-alist ctx state)
  ; Try the original event and obtain the number of steps.
  (er-let* ((steps (event-steps form state)))
    (cond
     ; If the original event failed, then we don't need to remove hypotheses.
     ((null steps)
      ; So signal an error.
      (er soft ctx
          "Original theorem failed!"))
     ; Else, call a recursive procedure to remove hypotheses
     (t (mv-let
         (erp final-hyps state)
         ; Note that the second and third argument represent necessary and
         ; unknown hypotheses.  We start with an empty list of necessary
         ; hypotheses and a full list of unknown hypotheses.
         (remove-hyps-formula-1 name nil hyps concl kwd-alist steps state)
         (cond (erp
                ; Signal an error (if one of the sub-events had an error)
                (mv erp final-hyps state))
               ; Else, return the new event with hypotheses removed.
               (t (value (make-defthm name final-hyps concl kwd-alist)))))))))

;; This function takes the original form and then calls remove-hyps-function to
;; create a new form with, potentially, fewer hypotheses.  A test is then
;; performed to see if any hypotheses were removed.  If so, the new form is
;; printed to the terminal.  Finally, after the form is printed, the new form
;; is submitted silently.
(defun remove-hyps-fn (form name hyps concl kwd-alist)
  `(make-event
    ; Obtain a new form with a subset of the hypotheses.
    (er-let* ((new-form
               (remove-hyps-formula ',form ',name ',hyps ',concl ',kwd-alist
                                    'remove-hyps state)))
      ; Test the new form versus the old form.
      (pprogn (cond ((equal new-form ',form)
                     ; If no hypotheses were removed, print this to the terminal.
                     (fms "Note: REMOVE-HYPS left its input unchanged.  Now ~
                           silently submitting the original form.~|"
                          nil (standard-co state) state nil))
                    ; If some hypotheses were removed, print the new form.
                    (t (fms "New form from REMOVE-HYPS:~|~%~x0~|~%Now silently ~
                             submitting the above form.~|"
                            (list (cons #\0 new-form))
                            (standard-co state) state nil)))
              ; Now submit the new form with all output disabled.
              (value `(with-output
                       :off :all
                       :gag-mode t
                       ,new-form))))))

;; The remove-hyps macro takes a defthm form and attempts to match the case
;; based on the number of hypotheses.  Note that defthms with no implicate or
;; no hypotheses are signaled as an error.
(defmacro remove-hyps (defthm-form)
  (case-match defthm-form
    ; Form with multiple hypotheses bound by "and"
    (('defthm name
       ('implies ('and . hyps) concl)
       . kwd-alist)
     (remove-hyps-fn defthm-form name hyps concl kwd-alist))
    ; Form with one hypothesis.  Create a list with this hypothesis.
    (('defthm name
       ('implies hyp concl)
       . kwd-alist)
     (remove-hyps-fn defthm-form name (list hyp) concl kwd-alist))
    ; Unknown form.  Signal error.
    (& `(er soft 'remove-hyps
            "Illegal argument to remove-hyps:~|~%~y0"
            ',defthm-form))))

;; Return to logic mode.
(logic)



;; ===================================================================
;; ============================= EXAMPLE =============================
;; ===================================================================

;; Include the arithmetic books for a theorem about nth.
(local (include-book "arithmetic/top" :dir :system))

;; Remove hyps from the nth-append defthm event and submit the reduced form.
(local
 (remove-hyps
  (defthm nth-append
    (implies (and (true-listp x)
                  (natp n)
                  (true-listp y))
             (equal (nth n (append x y))
                    (if (< n (len x))
                        (nth n x)
                      (nth (- n (len x)) y)))))))

;; Set enforce-redundancy so to ensure the next event has the same form as the
;; last event.
(set-enforce-redundancy t)

;; Resubmit the reduced event to demonstrate that it was produced by
;; remove-hyps.
(local
 (defthm nth-append
   (implies (natp n)
            (equal (nth n (append x y))
                   (if (< n (len x))
                       (nth n x)
                     (nth (- n (len x)) y))))))
