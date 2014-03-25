; Copyright (C) 2014, Regents of the University of Texas
; Written by Matt Kaufmann and Nathan Wetzler (original date March, 2014)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;;; General comments:

;;; Lisp commenting conventions generally expect ";;;" at the start of a line,
;;; ";;" for indented comments, and ";" at the end of a line after code.  But J
;;; and I typically use ";" instead of ";;;" for the beginning of a line.
;;; Actually ";;" is kind of important to use instead of ";", in order for
;;; control-meta-q and <TAB> to work as expected in Emacs.  But I won't change
;;; any of these, since that would make your diff or (meta-x compare-windows)
;;; more awkward.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;; ===================================================================

(defxdoc remove-hyps
  :parents (debugging)
  :short "Macro for defining a theorem with a minimal set of hypotheses"
  :long "<p>Suppose E is an admissible event of the form @('(defthm
  name (implies hyps ...))').  Then submitting instead the form @('(remove-hyps
  E)') results in storing a modified version of E, in which @('hyps') has been
  reduced to a minimal set of hypotheses.</p>

 <p>This tool is available in @('tools/remove-hyps.lisp').</p>")

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

; - Further develop documentation, e.g., moving example into it.

; - Moving event destructuring out of remove-hyps to a separate function
;   (in analogy to event construction using make-defthm)

; - Support for other forms besides defthm, such as defrule


;; ===================================================================

;; We will be programming with state.
(set-state-ok t)
;; This is a utility and we do not wish to reason about termination.  Moreover,
;; if we were to put all the functions into :logic mode, then either we would
;; need to verify their guards or we would get slower performance (because of
;; the use of executable-counterpart functions).
(program)


;; ============================ HEURISTIC ============================

;; This function provides a limit on the number of steps for any derivative of
;; the original theorem.  We want to avoid a situation where removing some
;; hypothesis places the prover in a state where it is "out to lunch".  This
;; puts an upper bound on the number of prover steps (and hopefully time) the
;; remove-hyps tool will use.  The limit is rather arbitrary and there might
;; well be better limits to use.
(defun remove-hyps-formula-steps (steps)
  (+ 1000 (* 3 steps)))


;; ======================= DEFTHM CONSTRUCTION =======================

;; The dumb-implicate function constructs an "implication" based on a list of
;; hypotheses.  If there are no hypotheses, the result is simply the
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

;; The event-steps function performs two tasks.  The first is testing a defthm
;; form for success/failure.  The second is calculating the number of prover
;; steps used in a successful event.  This function returns an error triple (mv
;; erp val state).  In the typical case, erp is nil; then if val is nil then
;; the event failed, and otherwise the event succeeded with val prover steps.
;; If erp is not nil, then all bets are off (but this should be rare).
(defun event-steps (form state)
  (let ((new-form
         ; The progn will revert the state if one of the events fails, which we
         ; guarantee with an ill-formed event (the defconst event below).
         `(progn ; First set a state global variable to nil in case of failure.
                 (make-event (pprogn (f-put-global 'our-steps nil state)
                                     (value '(value-triple nil))))
                 ; Execute the given form.
                 ,form
                 ; Record the number of prover steps used in the last event, if
                 ; it succeeded (otherwise we won't get this far).
                 (make-event (pprogn (f-put-global 'our-steps
                                                   (last-prover-steps state)
                                                   state)
                                     (value '(value-triple nil))))
                 ; Cause a failure by using an ill-formed defconst event.
                 (defconst *bad*) ; Note the missing second argument!
                 )))
    (er-progn
     ; Evaluate the new form constructed above.
     (trans-eval new-form 'event-steps state t)
     ; Return the value stored in the global variable.
     (value (f-get-global 'our-steps state)))))


;; ====================== REMOVE-HYPS ALGORITHM ======================

;; The main procedure of remove-hyps.  This function takes a list of necessary
;; hypotheses (presumably reversed from the original order) and an additional
;; list of hypotheses, the second and third arguments respectively.  It recurs
;; through the "additional" list, accumulating into the "necessary" list those
;; "additional" hypotheses that are necessary, ultimately returning the reverse
;; of the accumulated list.
(defun remove-hyps-formula-1 (name rev-init-hyps rest-hyps concl kwd-alist
                                   steps state)

  (cond
   ; If there are no more hypotheses to test, then return the reverse of the
   ; necessary hypotheses.
   ((endp rest-hyps) (value (reverse rev-init-hyps)))
   ; Create a new form by appending the necessary hypotheses to the cdr of the
   ; additional hypotheses.  Evaluate the form, limiting the number of steps
   ; based on the heuristic above.  Then recur using the cdr of the additional
   ; hypotheses and with the list of necessary hypotheses perhaps extended, as
   ; follows: If evaluation of the form succeeds, then the car of the
   ; additional hypotheses is not necessary, so do not accumulate it into the
   ; necessary hypotheses; otherwise, accumulate it.
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
           (cond ((null event-steps) ; the removed hypothesis was necessary
                  (cons (car rest-hyps) rev-init-hyps))
                 (t rev-init-hyps))
           (cdr rest-hyps)
           concl kwd-alist steps state))))))

;; This function returns an error triple whose value, in the non-error case, is
;; a defthm form for the given hyps, concl, and kwd-alist -- except, hypotheses
;; may be removed from hyps to provide a form whose proof nevertheless succeeds.
(defun remove-hyps-formula (form name hyps concl kwd-alist ctx state)
  ; Try the original event and obtain the number of steps.
  (er-let* ((steps (event-steps form state)))
    (cond
     ; If the original event failed, then we simply fail.
     ((null steps)
      ; So signal an error.
      (er soft ctx
          "Original theorem failed!"))
     ; Else, call a recursive procedure to remove hypotheses.
     (t (er-let*
         ((final-hyps
           ; Note that the second and third argument represent necessary and
           ; additional hypotheses.  We start with an empty list of necessary
           ; hypotheses and a full list of additional hypotheses.
           (remove-hyps-formula-1 name nil hyps concl kwd-alist steps state)))
         (value (make-defthm name final-hyps concl kwd-alist)))))))

;; This function takes the original form and then calls remove-hyps-function to
;; create a new form with, potentially, fewer hypotheses.  A test is then
;; performed to see if any hypotheses were removed.  If so, the new form is
;; printed to the terminal.  Finally, after the form is printed, the new form
;; is submitted silently.  Note that form is essentially (defthm name (implies
;; hyps concl) . kwd-alist).
(defun remove-hyps-fn (form name hyps concl kwd-alist)
  `(make-event
    ; Obtain a new form with a minimal subset of the hypotheses.
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
              (value (list 'with-output
                           :off :all
                           :gag-mode t
                           new-form))))))

;; The remove-hyps macro takes a defthm form and attempts to match the case
;; based on the number of hypotheses.  Note that an error occurs if the formula
;; of the defthm is not an implication.
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


;; ============================= EXAMPLE =============================

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
                      (nth (- n (len x)) y))))
    :rule-classes nil)))

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
                     (nth (- n (len x)) y))))
   :rule-classes nil))

; Here is a (rather dumb) variant where all the hypotheses are removed.

(set-enforce-redundancy nil)

(local
 (remove-hyps
  (defthm nth-append-alt
    (implies (and (true-listp x)
                  (natp n)
                  (true-listp y))
             (equal (nth n (append x y))
                    (if (not (natp n)) (car (append x y))
                      (if (< n (len x))
                          (nth n x)
                        (nth (- n (len x)) y)))))
    :rule-classes nil)))

(set-enforce-redundancy t)

;; Resubmit the reduced event to demonstrate that it was produced by
;; remove-hyps.
(local
 (defthm nth-append-alt
   (equal (nth n (append x y))
          (if (not (natp n)) (car (append x y))
            (if (< n (len x))
                (nth n x)
              (nth (- n (len x)) y))))
   :rule-classes nil))
