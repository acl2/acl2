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

; Possible enhancements include:

; - Supporting a mode where the new event isn't actually submitted (as is
;   already done in the case of THM)

; - Taking advantage of the :OR feature of make-event to avoid repeated
;   evaluation in some cases

; - Using the :DO-PROOFS feature of make-event to ensure proper operation when
;   skipping proofs (e.g., calling rebuild)

; - Using the :EXPANSION? feature of make-event to avoid storing the make-event
;   expansion in the certificate, in the common case where no hypotheses are
;   eliminated

; - Further develop documentation, e.g., moving examples into it

; - Moving event destructuring out of remove-hyps to a separate function
;   (in analogy to event construction using make-defthm)

; - Support for other forms, such as defrule

; - Consider somehow reporting the correct prover-steps for the final defthm,
;   but still reporting the total prover-steps for the entire remove-hyps
;   invocation (as might be done now -- maybe figure that out and document
;   it).

; - Avoid generating ignorable declarations (search below for "ignorable") by
;   using source function translate-cmp, say, to see which variables are used.

;; ===================================================================

(defxdoc remove-hyps
  :parents (proof-automation debugging)
  :short "Macro for defining a theorem with a minimal set of hypotheses"
  :long "<p>For a call of @(tsee defthm), @(tsee defthmd), or @(tsee thm), the
 application of @('remove-hyps') attempts to produce a minimal set of
 hypotheses.  For example:</p>

 @({
 (remove-hyps
  (defthm nth-append
    (implies (and (true-listp x)
                  (natp n)
                  (true-listp y))
             (equal (nth n (append x y))
                    (if (< n (len x))
                        (nth n x)
                      (nth (- n (len x)) y))))
    :rule-classes nil))
 })

 <p>generates:</p>

 @({
 (DEFTHM NTH-APPEND
   (IMPLIES (NATP N)
            (EQUAL (NTH N (APPEND X Y))
                   (IF (< N (LEN X))
                       (NTH N X)
                     (NTH (- N (LEN X)) Y))))
   :RULE-CLASSES NIL)
 })

 <p>Note however that @('remove-hyps') works by removing one hypothesis at a
 time, with each resulting proof attempt made using a limited number of
 steps (see @(see with-prover-step-limit)) that depends on the number of steps
 taken before removing the hypothesis.  So if the removal of a hypothesis
 requires a proof that takes sufficiently many more steps than the original
 proof, or if two or more hypotheses must be removed together for the proof to
 succeed with fewer hypotheses, then the result will not have a minimal set of
 hypotheses.</p>

 <p>Acceptable forms are as follows, where @('HYP') can be a conjunction of
 hypotheses, @('(and HYP1 ... HYPn)'), and ``@('defthm NAME')'' may be
 replaced by ``@('defthmd NAME')'' or ``@('THM')''.</p>

 @({
 (defthm NAME (implies HYP CONCL) ...)
 (defthm NAME CONCL ...)
 (defthm NAME (let ... (implies HYP CONCL)) ...)
 (defthm NAME (let ... CONCL) ...)
 (defthm NAME (let* ... (implies HYP CONCL)) ...)
 (defthm NAME (let* ... CONCL) ...)
 })

 <p>Normally, before using @('remove-hyps'), one succesfully submits the given
 call of @('defthm'), @('defthmd'), or @('thm').  Thus by default,
 @('remove-hyps') evaluates silently.  To see output from proof attempts, add a
 non-nil optional argument.  For example, for event @('E'), use @('(remove-hyps
 E t)').</p>

 <p>Unless there is an error (for example, due to malformed input), then in the
 case of a call of @('thm'), the value returned is the keyword,
 @(':REMOVE-HYPS-COMPLETED'); otherwise, the value returned is the name of the
 theorem.  (Technically, the value returned is an error triple with such a
 value; see @(see error-triple).)</p>

 <p>Consider the case that a call of @('remove-hyps') is made in a context
 where proofs are normally skipped (see @(see ld-skip-proofsp)).  If this
 happens while including a certified book with @(tsee include-book), then
 proofs will indeed be skipped, because the earlier result of this
 @('remove-hyps') call was saved in the book's @(see certificate).  But
 otherwise, the tool temporarily turns off the skipping of proofs (that is,
 restores the act of doing proofs) while it tries to remove hypotheses, to
 avoid the undesirable situation that all hypotheses are removed merely because
 all proofs succeed when skipping proofs.</p>

 <p>Finally, note that when @('remove-hyps') is applied to a call of
 @('defthm') or @('defthmd'), then @('remove-hyps') will conclude by submitting
 the generated event to ACL2.  But since @('thm') does not modify the logical
 @(tsee world), @('remove-hyps') does not perform an extra such call at the end
 for calls of @('thm').</p>")


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
  (min *default-step-limit* ; else with-prover-step-limit causes error
       (+ 1000 (* 3 steps))))


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
(defun make-defthm (deft name hyps concl kwd-alist let/let* bindings)
  (let* ((form0 (dumb-implicate hyps concl))
         (form (if bindings
                   `(,let/let* ,bindings
                               (declare (ignorable ,@(strip-cars bindings)))
                               ,form0)
                 form0)))
    (if (null name)
        (assert$ (eq deft 'thm)
                 `(thm ,form ,@kwd-alist))
      `(,deft ,name ,form ,@kwd-alist))))


;; ======================== DEFTHM EXECUTION =========================

;; The event-steps function performs two tasks.  The first is testing a defthm
;; form for success/failure.  The second is calculating the number of prover
;; steps used in a successful event.  This function returns an error triple (mv
;; erp val state).  In the typical case, erp is nil; then if val is nil then
;; the event failed, and otherwise the event succeeded with val prover steps.
;; If erp is not nil, then all bets are off (but this should be rare).
(defun event-steps (form verbose-p extra-forms state)

; Extra-forms is a list of forms, possibly empty, where each evaluates to state
; and is to be evaluated only if form evaluates successfully.

  (let ((new-form
         ;; The progn will revert the state if one of the events fails, which we
         ;; guarantee with an ill-formed event (the defconst event below).
         `(with-output ; turn off output
            :stack :push
            :off :all
            :gag-mode nil
            (progn ; First set a state global variable to nil in case of failure.
              (make-event (pprogn (f-put-global 'our-steps nil state)
                                  (value '(value-triple nil))))
              ;; Execute the given form.
              ,(if verbose-p
                   `(with-output :stack :pop ,form)
                 form)
              ;; Record the number of prover steps used in the last event, if
              ;; it succeeded (otherwise we won't get this far).  Success could
              ;; involve no prover steps, so we record a number of steps that
              ;; is at least 1 (perhaps 0 would do, but we play it safe).
              (make-event (pprogn (f-put-global 'our-steps
                                                (or (last-prover-steps
                                                     state)
                                                    1)
                                                state)
                                  ,@extra-forms
                                  (value '(value-triple nil))))
              ;; Cause a failure by using an ill-formed defconst event.
              (defconst *bad*) ; Note the missing second argument!
              ))))
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
                                   let/let* bindings steps verbose-p state)

  (cond
   ; If there are no more hypotheses to test, then return the reverse of the
   ; necessary hypotheses.
   ((endp rest-hyps) (value (reverse rev-init-hyps)))
   ; Don't drop syntaxp or bind-free hypotheses.
   ((and (consp (car rest-hyps))
         (member-eq (caar rest-hyps)
                    '(syntaxp bind-free synp)))
    (remove-hyps-formula-1
     name
     (cons (car rest-hyps) rev-init-hyps)
     (cdr rest-hyps)
     concl kwd-alist let/let* bindings steps verbose-p state))
   ; Create a new form by appending the necessary hypotheses to the cdr of the
   ; additional hypotheses.  Evaluate the form, limiting the number of steps
   ; based on the heuristic above.  Then recur using the cdr of the additional
   ; hypotheses and with the list of necessary hypotheses perhaps extended, as
   ; follows: If evaluation of the form succeeds, then the car of the
   ; additional hypotheses is not necessary, so do not accumulate it into the
   ; necessary hypotheses; otherwise, accumulate it.
   (t (let ((form `(with-prover-step-limit
                    ,steps
                    ,(make-defthm 'defthm
                                  name
                                  (revappend rev-init-hyps (cdr rest-hyps))
                                  concl kwd-alist let/let* bindings))))
        ; Try the new event.
        (er-let* ((event-steps (event-steps form verbose-p nil state)))
          ; Recur with the cdr of the unknown hypotheses, but...
          (remove-hyps-formula-1
           name
           ; Modify the necessary hypotheses based on the result of the last
           ; event.
           (cond ((null event-steps) ; the removed hypothesis was necessary
                  (cons (car rest-hyps) rev-init-hyps))
                 (t rev-init-hyps))
           (cdr rest-hyps)
           concl kwd-alist let/let* bindings steps verbose-p state))))))

;; This function returns an error triple whose value, in the non-error case, is
;; a defthm form for the given hyps, concl, and kwd-alist -- except, hypotheses
;; may be removed from hyps to provide a form whose proof nevertheless succeeds.
(defun remove-hyps-formula (form name hyps concl kwd-alist let/let* bindings
                                 verbose-p ctx state)
  (do-proofs?
   t
   (mv-let (thmp name2 kwd-alist+)
     (assert$
      (iff (eq (car form) 'thm)
           (null name))
      (if (null name) ; (eq (car form) 'thm)
          (mv t
              (gen-new-name 'remove-hyps-name (w state))
              (append kwd-alist '(:rule-classes nil)))
        (mv nil name kwd-alist)))
     ;; Try the original event and obtain the number of steps.
     (er-let* ((steps (event-steps (if thmp
                                       `(defthm ,name2
                                          ,@(cdr form)
                                          :rule-classes nil)
                                     form)
                                   verbose-p nil state)))
       (cond
        ((null steps) ; The original event failed; so we simply fail.
         (er soft ctx
             "Original theorem failed!"))
        (t ; Else, call a recursive procedure to remove hypotheses.
         (er-let*
             ((final-hyps
               ;; Note that the second and third argument represent necessary and
               ;; additional hypotheses.  We start with an empty list of necessary
               ;; hypotheses and a full list of additional hypotheses.
               (remove-hyps-formula-1 name2
                                      nil hyps concl kwd-alist+ let/let*
                                      bindings
                                      (remove-hyps-formula-steps steps)
                                      verbose-p state)))
           (value (if (equal (length hyps) (length final-hyps))
                      nil ; no change
                    (make-defthm (car form) name final-hyps concl kwd-alist
                                 let/let* bindings))))))))))

;; This function takes the original form and then calls remove-hyps-function to
;; create a new form with, potentially, fewer hypotheses.  A test is then
;; performed to see if any hypotheses were removed.  If so, the new form is
;; printed to the terminal.  Finally, after the form is printed, the new form
;; is submitted silently.  Note that form is essentially (defthm name (implies
;; hyps concl) . kwd-alist).
(defun remove-hyps-fn (form name hyps concl kwd-alist let/let* bindings
                            verbose-p)
  `(make-event
    ;; Obtain a new form with a minimal subset of the hypotheses.
    (er-let* ((new-form
               (remove-hyps-formula ',form ',name ',hyps ',concl ',kwd-alist
                                    ',let/let* ',bindings ',verbose-p
                                    'remove-hyps state))
              (thmp (value (eq (car ',form) 'thm))))
; Test the new form versus the old form.
      (pprogn (cond ((null new-form) ; no change
; If no hypotheses were removed, print this to the terminal.
                     (fms "Note: REMOVE-HYPS left its input unchanged.~|~@0"
                          (list (cons #\0
                                      (if thmp
                                          ""
                                        "Now silently submitting the original ~
                                         form.~|")))
                          (standard-co state) state nil))
; If some hypotheses were removed, print the new form.
                    (t (fms "New form from REMOVE-HYPS:~|~%~x0~|~%~@1"
                            (list (cons #\0 new-form)
                                  (cons #\1
                                        (if thmp
                                            ""
                                          "Now silently submitting the new ~
                                           form (above).~|")))
                            (standard-co state) state nil)))
; Now submit the new form with all output disabled.
              (value (if thmp
                         '(value-triple :remove-hyps-completed)
                       (list 'with-output
                             :off :all
                             :gag-mode t
                             (or new-form ',form))))))))

;; The remove-hyps macro takes a defthm (or defthmd or thm) form and attempts
;; to match the case based on the number of hypotheses.  Note that an error
;; occurs if the formula of the defthm is not an implication, perhaps within a
;; let or let*.
(defmacro remove-hyps (form &optional verbose-p)
  (or (and (consp form)
           (member-eq (car form) '(defthm defthmd thm))
           (mv-let
             (name form-without-name)
             (if (eq (car form) 'thm)
                 (mv nil (cdr form))
               (mv (cadr form) (cddr form)))
             (case-match form-without-name
               ((('implies hyp concl)
                 . kwd-alist)
                (let ((hyps (if (and (consp hyp)
                                     (eq (car hyp) 'and))
                                (cdr hyp)
                              (list hyp))))
                  (remove-hyps-fn form name hyps concl kwd-alist
                                  nil nil verbose-p)))
               (((let/let* bindings ('implies hyp concl))
                 . kwd-alist)
                (and (member-eq let/let* '(let let* b*))
                     (let ((hyps (if (and (consp hyp)
                                          (eq (car hyp) 'and))
                                     (cdr hyp)
                                   (list hyp))))
                       (remove-hyps-fn form name hyps concl kwd-alist
                                       let/let* bindings verbose-p))))
               (& nil))))
      `(er soft 'remove-hyps
           "Illegal argument to remove-hyps:~|~%~y0"
           ',form)))

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

(set-enforce-redundancy nil)

(local
 (remove-hyps
  (defthm nth-append-alt-2
    (let ((xx x))
      (implies (and (true-listp xx)
                    (natp n)
                    (true-listp y))
               (equal (nth n (append xx y))
                      (if (< n (len x))
                          (nth n x)
                        (nth (- n (len xx)) y)))))
    :hints (("Goal'" :induct t)))))

(set-enforce-redundancy t)

(local
 (defthm nth-append-alt-2
   (let ((xx x))
     (declare (ignorable xx))
     (implies (natp n)
              (equal (nth n (append xx y))
                     (if (< n (len x))
                         (nth n x)
                       (nth (- n (len xx)) y)))))
   :hints (("Goal'" :induct t))))
