; Copyright (C) 2014, Regents of the University of Texas
; Written by Matt Kaufmann and Nathan Wetzler (original date March, 2014)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; When event is a successful event (defthm name (implies ...) ...)  then the
; form (remove-hyps event) results in storing a modified version of this event
; in which, essentially, the hypotheses have been reduced to a minimal set.
; Documentation may come later....

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

(in-package "ACL2")

(set-state-ok t)

(program)

(defun remove-hyps-formula-steps (steps)
  (+ 1000 (* 3 steps)))

(defun dumb-implicate (hyps concl)
  (cond ((null hyps) concl)
        ((null (cdr hyps)) `(implies ,(car hyps) ,concl))
        (t `(implies (and ,@hyps) ,concl))))

(defun make-defthm (name hyps concl kwd-alist)
  `(defthm ,name
     ,(dumb-implicate hyps concl)
     ,@kwd-alist))

(defun event-steps (form state)

; Always fails (silently) to install form, which is an event.  Returns (value
; nil) if evaluation of form failed, else (value s) where s is the number of
; prover steps taken on form.

; Note that form is to be evaluated.

  (let ((new-form
         `(progn (make-event (pprogn (f-put-global 'our-steps nil state)
                                     (value '(value-triple nil))))
                 ,form
                 (make-event (pprogn (f-put-global 'our-steps
                                                   (last-prover-steps state)
                                                   state)
                                     (value '(value-triple nil))))
                 (defconst *bad*) ; no args!
                 )))

    (er-progn
     (trans-eval new-form 'event-steps state t)
     (value (f-get-global 'our-steps state)))))

(defun remove-hyps-formula-1 (name rev-init-hyps rest-hyps concl kwd-alist
                                   steps state)

  (cond
   ((endp rest-hyps) (value (reverse rev-init-hyps)))
   (t (let ((form `(with-prover-step-limit
                    ,steps
                    ,(make-defthm name
                                  (revappend rev-init-hyps (cdr rest-hyps))
                                  concl kwd-alist))))
        (er-let* ((event-steps (event-steps form state)))
          (remove-hyps-formula-1
           name
           (cond ((null event-steps)
                  (cons (car rest-hyps) rev-init-hyps))
                 (t rev-init-hyps))
           (cdr rest-hyps)
           concl kwd-alist steps state))))))

; Try proving the indicated theorem with hypotheses removed from rest-hyps.

(defun remove-hyps-formula (form name hyps concl kwd-alist ctx state)
  (er-let* ((steps (event-steps form state)))
    (cond
     ((null steps)
      (er soft ctx
          "Original theorem failed!"))
     (t (mv-let
         (erp final-hyps state)
         (remove-hyps-formula-1 name nil hyps concl kwd-alist steps state)
         (cond (erp ; error in something other than the proof, say
                (mv erp final-hyps state))
               (t (value (make-defthm name final-hyps concl kwd-alist)))))))))

(defun remove-hyps-fn (form name hyps concl kwd-alist)
  `(make-event
    (er-let* ((new-form
               (remove-hyps-formula ',form ',name ',hyps ',concl ',kwd-alist
                                    'remove-hyps state)))
      (pprogn (cond ((equal new-form ',form)
                     (fms "Note: REMOVE-HYPS left its input unchanged.  Now ~
                           silently submitting the original form.~|"
                          nil (standard-co state) state nil))
                    (t (fms "New form from REMOVE-HYPS:~|~%~x0~|~%Now silently ~
                             submitting the above form.~|"
                            (list (cons #\0 new-form))
                            (standard-co state) state nil)))
              (value `(with-output
                       :off :all
                       :gag-mode t
                       ,new-form))))))

(defmacro remove-hyps (defthm-form)
  (case-match defthm-form
    (('defthm name
       ('implies ('and . hyps) concl)
       . kwd-alist)
     (remove-hyps-fn defthm-form name hyps concl kwd-alist))
    (('defthm name
       ('implies hyp concl)
       . kwd-alist)
     (remove-hyps-fn defthm-form name (list hyp) concl kwd-alist))
    (& `(er soft 'remove-hyps
            "Illegal argument to remove-hyps:~|~%~y0"
            ',defthm-form))))

(logic)

; Example:

(local (include-book "arithmetic/top" :dir :system))

(local
 (remove-hyps (defthm nth-append
                (implies (and (true-listp x) (natp n) (true-listp y))
                         (equal (nth n (append x y))
                                (if (< n (len x))
                                    (nth n x)
                                  (nth (- n (len x)) y)))))))

; Check for redundancy:

(set-enforce-redundancy t)

(local
 (defthm nth-append
   (implies (natp n)
            (equal (nth n (append x y))
                   (if (< n (len x))
                       (nth n x)
                     (nth (- n (len x)) y))))))
