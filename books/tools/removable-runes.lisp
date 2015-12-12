; Copyright (C) 2015, ForrestHunt, Inc.
; Written by Matt Kaufmann, November, 2015
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc removable-runes
  :parents (proof-automation debugging)
  :short "Compute @(see rune)s to @(see disable)"
  :long "@({

 Example Form
   (try this after :mini-proveall and (:ubt proper-cons-nest-p)):
 (removable-runes (defun proper-cons-nest-p (x)
                    (declare (xargs :guard (pseudo-termp x)))
                    (cond ((symbolp x) nil)
                          ((fquotep x) (true-listp (cadr x)))
                          ((eq (ffn-symb x) 'cons)
                           (proper-cons-nest-p (fargn x 2)))
                          (t nil)))
                  :verbose-p :minimal)

 General Form:
 (removable-runes event-form
                  :verbose-p  v ; default = :normal
                  :multiplier m ; default = 1)
                  )
 })

 <p>where @('event-form') is an embeddable event (see @(see events)); @('v') is
 @('nil'), @(':minimal'), @(':normal'), or @('t'); and @('m') is a positive
 rational number not exceeding 1.  The value returned is an @(see error-triple)
 @('(mv erp runes state)'), where @('erp') is typically @('nil') and @('runes')
 is a list of @(see rune)s that can be @(see disable)d for the indicated
 @('event-form'), such that the event is admitted with fewer prover
 steps.  (See @(see set-prover-step-limit) for a discussion of prover steps.)
 For example, if the list of runes returned for an event form is
 @('((:definition f1) (:rewrite thm1))'), then the proof of that event form was
 performed successively &mdash; and with fewer steps &mdash; when first
 evaluating the event @('(in-theory (disable (:definition f1) (:rewrite
 thm1)))').</p>

 <p>We now describe the two keyword arguments in turn, and in doing so, we
 explain how the tool works.</p>

 <p>The @(':verbose-p') argument controls the level of output.  We begin By
 describing the default benavior.  The output for the default value
 @(':verbose-p = :normal') is broken into sections for successive ``rounds''.
 Each section appears as follows, other than the initial section, which only
 lists the steps for the original proof attempt.</p>

 @({
 Steps: [steps]
 Steps saved: [steps saved]
 Time: [time]
 Removed: [rune]
 Removable:
 [list of runes]
 [progress line]
 })

 <p>The ``@('Steps')'' field has the number of prover steps taken by that
 round's proof attempt, where the initial ``@('Steps')'' is the number of
 prover steps reported for the original form.  The corresponding ``@('Steps
 saved')'', ``@('Time'), ``@('Removed'), and ``@('Removable')'' fields state
 the following, respectively: the difference between the @('Steps') for the
 previous and current round (and in parentheses, the difference between the
 @('Steps') for the initial event and the current round); the time taken for
 the new event (by default, the run time; see @(see get-internal-time)); the
 rune that was newly disabled for the current round; and the list of runes
 disabled for the current round, which extends the previous round's
 @('Removable') field with that newly disabled rune.  For each round, the event
 was admitted with the @('Removable') runes first disabled by an @(tsee
 in-theory) event.  Finally, the progress line shows attempts to decrease the
 number of steps by disabling one rune per attempt, using @(''.'')  for a
 failed such attempt and @(''+'') for a success.  Each such rune is chosen from
 the list of runes reported for the previous round.</p>

 <p>If @(':verbose-p = :minimal'), then the output will be as described above
 except that the @('Removable') fields are omitted.  If @(':verbose-p = nil'),
 then there is no output.  Finally, if @(':verbose-p = t'), then all the fields
 are printed, but in addition you will see the usual output for each attempt,
 each (except for the initial event) preceded by the corresponding in-theory
 event.</p>

 <p>We now say a bit more about the tool's algorithm as we describe the
 @(':multiplier') argument, which is 1 by default but can also be any rational
 number between 0 and 1.  Recall that each round is an attempt to find a rune
 to disable: specifically, one provides the fewest number of resulting prover
 steps.  The number of steps thus computed for that round is required to be
 less than the number of steps computed for the previous round (or, in the case
 of the first round, less than the number of steps for the initial proof
 attempt).  The multipler says how much less is required: if @('s0') is the
 number of steps for the preceding (or initial) round, then the number of steps
 for the next round is not allowed to exceed @('(1- (ceiling (* m s0) 1))'),
 where @('m') is the value of the @(':multipler') keyword.</p>

 <p>Finally, we expand on a point made above.  When a rune is chosen to add to
 the evolving list of disables, the corresponding proof attempt might actually
 involve runes that were not present in any earlier proof attempt.  Any new
 such runes are then considered for disabling in later rounds.</p>")

(set-state-ok t)

(program)

(defun non-removable-runes (world)
  (append (list *fake-rune-for-anonymous-enabled-rule*
                *fake-rune-for-type-set*
                *fake-rune-for-linear*)
          (union-equal (theory 'definition-minimal-theory)
                       (theory 'executable-counterpart-minimal-theory))))

(defun get-event-data-total-time (state)
  (let ((lst (get-event-data 'time state))) ; (a b c d)
    (let* ((a (car lst))
           (lst (cdr lst)) ; (b c d)
           (b (car lst))
           (lst (cdr lst)) ; (c d)
           (c (car lst))
           (lst (cdr lst)) ; (d)
           (d (car lst)))
      (+ a b c d))))

(defun event-steps-runes-form (disable-form form0 verbose-p ignored-runes)

; When the evaluation of form0 is interrupted, the final value of state global
; 'our-steps will be nil.  Otherwise that value will either be :error, to
; denote a possibly odd failure of form0, or the prover-steps taken for form0.
; It is important to communicate the case that an interrupt took place, because
; trans-eval of the returned form otherwise wouldn't be able to communicate
; whether or not the failure was from an interrupt.

  `(with-output
     :stack :push
     :off :all
     :gag-mode nil
     (progn
       ,@(and disable-form
              (list (if (eq verbose-p t)
                        `(progn ,disable-form
                                (value-triple (cw "~x0~|" ',disable-form)))
                      disable-form)))
       (make-event (mv-let
                     (erp val state)
                     (pprogn (f-put-global 'our-steps nil state)
                             (f-put-global 'our-runes nil state)
                             (f-put-global 'our-time nil state)
                             ,(if (eq verbose-p t)
                                  `(with-output :stack :pop ,form0)
                                form0))
                     (declare (ignore val))
                     (pprogn
                      (cond
                       ((member-eq 'interrupt
                                   (get-event-data 'abort-causes state))
                        (f-put-global 'our-steps
                                      nil ; see comment above
                                      state))
                       (erp (f-put-global 'our-steps
                                          :error ; see comment above
                                          state))
                       (t (pprogn (f-put-global 'our-steps
                                                (or (last-prover-steps state)
                                                    :error) ; see comment above
                                                state)
                                  (f-put-global 'our-runes
                                                (set-difference-equal
                                                 (get-event-data 'rules state)
                                                 ',ignored-runes)
                                                state)
                                  (f-put-global 'our-time
                                                (get-event-data-total-time state)
                                                state))))
                      (silent-error state)))))))

(defun event-steps-runes+ (form steps disables verbose-p ignored-runes state)

; This function is a variant of function event-steps, defined in community book
; books/tools/remove-hyps.lisp.  See that function for comments.  The present
; function returns nil if the form fails to prove, and otherwise returns
; (prover-steps . runes) where prover-steps is the number of steps required and
; runes is the list of runes reported.

  (let* ((form0 (if steps
                    `(with-prover-step-limit ,steps ,form)
                  form))
         (disable-form (and disables `(in-theory (disable ,@disables))))
         (new-form (event-steps-runes-form disable-form form0 verbose-p
                                           ignored-runes)))
    (er-progn
; Evaluate the new form constructed above.
     (trans-eval new-form 'event-steps state t)
; Return the value stored in the global variable.
     (value (list* (f-get-global 'our-steps state)
                   (f-get-global 'our-runes state)
                   (f-get-global 'our-time state))))))

(defconst *rrv-levels*
; Here, "rrv" is mnemonic for "removable-runes-verbosity".
  '(nil :minimal :normal t))

(defmacro rrv (level form)
; Here, "rrv" is mnemonic for "removable-runes-verbosity".
  (declare (xargs :guard (member-eq level *rrv-levels*)))
  `(cond ((>= (position verbose-p *rrv-levels*)
              ,(position level *rrv-levels*))
          ,form)
         (t state)))

(defun removable-runes-next (form steps runes best-rune best-used best-time
                                  disables verbose-p ignored-runes channel
                                  state)

; We search for a rune r in runes that can be disabled, together with disables,
; such that the given event form still succeeds.  If there is no such r, we
; return the value nil.  Otherwise, among such r, let s be the minimum number
; of proof steps, never exceeding the given number.  We return the value (r s
; . used), where used is the list of runes used in the proof that are not among
; r or seen.

  (cond
   ((endp runes)
    (value (and best-rune
                (list* steps best-rune best-used best-time))))
   (t
    (mv-let (erp steps/runes/time state)
      (event-steps-runes+ form steps (cons (car runes) disables)
                          verbose-p ignored-runes state)
      (let ((steps2 (car steps/runes/time))
            (runes2 (cadr steps/runes/time))
            (time2 (cddr steps/runes/time)))
        (cond
         ((null steps2)
          (value (abort!)))
         ((or erp
              (eql steps2 :error) ; see event-steps-runes-form
              (> steps2 steps)    ; impossible?
              )
          (pprogn
           (rrv :minimal (princ$ #\. channel state))
           (removable-runes-next form steps (cdr runes)
                                 best-rune best-used best-time
                                 disables verbose-p ignored-runes channel
                                 state))) 
         (t
          (pprogn
           (rrv :minimal (princ$ #\+ channel state))
           (removable-runes-next form steps2 (cdr runes)
                                 (car runes)
                                 runes2
                                 time2
                                 disables verbose-p ignored-runes channel
                                 state)))))))))

(defun removable-runes-print-status (s d d-total r time
                                       disables verbose-p channel state)
  (mv-let
    (erp time-string state)
    (cond ((null verbose-p) ; don't care
           (value nil))
          (t (rational-to-decimal-string time state)))
    (assert$
     (null erp)
     (cond
      ((null r) ; initial
       (rrv :minimal
            (fms "Steps: ~x0 (initial attempt)~|Time: ~s1~|"
                 (list (cons #\0 s)
                       (cons #\1 time-string))
                 channel state nil)))
      (t
       (pprogn (rrv :minimal
                    (fms "Steps: ~x0~|Steps saved: ~x1 (cumulative: ~
                          ~x2)~|Time: ~s3~|Removed: ~x4"
                         (list (cons #\0 s)
                               (cons #\1 d)
                               (cons #\2 d-total)
                               (cons #\3 time-string)
                               (cons #\4 r))
                         channel state nil))
               (rrv :normal (fms "Removable:~|~y0"
                                 (list (cons #\0 disables))
                                 channel state nil))
; Yuck; rrv isn't sufficiently flexible here, so I'll break that abstraction.
               (cond ((eq verbose-p :minimal)
                      (newline channel state))
                     (t state))))))))

(defun removable-runes-loop (form steps previous-steps init-steps
                                  runes disables seen verbose-p
                                  ignored-runes multiplier channel state)
  (cond
   ((null runes)
    (pprogn (rrv :minimal (newline channel state))
            (value disables)))
   (t
    (er-let* ((s/r/used/time
               (removable-runes-next
                form steps runes nil nil nil
                disables verbose-p ignored-runes channel state)))
      (cond
       ((null s/r/used/time)
        (pprogn (rrv :minimal (newline channel state))
                (value disables)))
       (t
        (let* ((s (car s/r/used/time))
               (r (cadr s/r/used/time))
               (used (caddr s/r/used/time))
               (time (cdddr s/r/used/time))
               (disables (cons r disables)))
          (pprogn
           (removable-runes-print-status s
                                         (- previous-steps s)
                                         (- init-steps s)
                                         r
                                         time
                                         disables verbose-p channel state)
           (assert$
            (and (member-equal r seen)
                 (<= s steps))
            (cond
             ((zp s) (value disables))
             (t
              (removable-runes-loop
               form
               (1- (ceiling (* multiplier s) 1))
               s init-steps
               (union-equal (set-difference-equal used seen)
                            (remove1-equal r runes))
               disables
               (union-equal used seen)
               verbose-p ignored-runes multiplier channel state))))))))))))

(defun removable-runes-fn (form verbose-p multiplier ctx state)
  (let ((channel (proofs-co state))
        (ignored-runes (non-removable-runes (w state))))
    (er-let* ((steps/runes/time (event-steps-runes+ form nil nil verbose-p
                                                    ignored-runes state))
              (steps2 (value (car steps/runes/time)))
              (runes2 (value (cadr steps/runes/time)))
              (time2 (value (cddr steps/runes/time))))
      (cond ((or (null steps2)
                 (eql steps2 :error) ; see event-steps-runes-form
                 )
             (er soft ctx
                 "REMOVABLE-RUNES failed because the following original event ~
                  failed:~x0"
                 form))
            (t (pprogn
                (rrv :minimal
                     (mv-let (col state)
                       (print-string-repeat "-"
                                            (length runes2)
                                            0 channel state)
                       (declare (ignore col))
                       state))
                (removable-runes-print-status steps2
                                              nil nil nil
                                              time2
                                              nil
                                              verbose-p channel state)
                (removable-runes-loop
                 form
                 (1- (ceiling (* multiplier steps2) 1))
                 steps2
                 steps2
                 runes2
                 nil
                 runes2
                 verbose-p ignored-runes multiplier channel state)))))))

(defmacro removable-runes (form &key (verbose-p ':normal) (multiplier '1))

; Note that multiplier is not evaluated.

  (declare (xargs :guard (and (member-eq verbose-p *rrv-levels*)
                              (rationalp multiplier)
                              (< 0 multiplier)
                              (<= multiplier 1))))
  `(removable-runes-fn ',form ,verbose-p ,multiplier 'minimize-theory state))
