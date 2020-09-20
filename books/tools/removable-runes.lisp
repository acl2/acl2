; Copyright (C) 2015, ForrestHunt, Inc.
; Written by Matt Kaufmann, November, 2015
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc removable-runes
  :parents (proof-automation debugging)
  :short "Compute @(see rune)s to @(see disable)"
  :long "@({

 Example Form:
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
 rational number.  The value returned is an @(see error-triple) @('(mv erp
 runes state)'), where @('erp') is typically @('nil') and @('runes') is a list
 of @(see rune)s that can be @(see disable)d for the indicated @('event-form');
 moreover, if the multiplier @('m') is less than 1, then the event is admitted
 with fewer prover steps.  (See @(see set-prover-step-limit) for a discussion
 of prover steps.)  For example, if the list of runes returned for an event
 form is @('((:definition f1) (:rewrite thm1))'), then the proof of that event
 form was performed successfully &mdash; and, for the default @('m') = 1, with
 no more prover steps &mdash; if we first evaluate the event
 @('(in-theory (disable (:definition f1) (:rewrite thm1)))').</p>

 <p>For a related utility, see @(see minimal-runes).</p>

 <p>WARNING: It is generally best to avoid using @(':')@(tsee in-theory) @(see
 hints) in the form you supply to @('removable-runes') or its related utility,
 @('minimal-runes').  We explain why below, after describing how the tool
 works.</p>

 <p>We now describe the two keyword arguments in turn, and in doing so, we
 explain how the tool works.</p>

 <p>The @(':verbose-p') argument controls the level of output.  We begin by
 describing the default behavior.  The output for the default value
 @(':verbose-p = :normal') is broken into sections for successive ``rounds''.
 Each section appears as follows, other than the initial section, which only
 lists the steps for the original proof attempt.</p>

 @({
 New steps: [steps]
 Old steps: [steps] (Initially: [steps])
 Time: [time]
 Removed: [rune]
 Removable:
 [list of runes]
 Used:
 [list of runes]
 [progress line]
 })

 <p>The ``@('New Steps')'' field has the number of prover steps taken by that
 round's proof attempt.  The ``@('Old Steps')'', ``@('Time')'',
 ``@('Removed')'', ``@('Removable')'', and ``@('Used')'' fields state the
 following, respectively: the number of prover steps for the previous round and
 for the initial round (but this line is omitted for the initial round); the
 time taken for the new event (by default, the run time; see @(see
 get-internal-time)); the rune that was newly disabled for the current round;
 the list of runes disabled after the current round, which extends the previous
 round's @('Removable') field with that newly disabled rune; and the list of
 runes used automatically in the proof for the current round.  For all but the
 initial round, the event was admitted in the previous round after disabling
 the @('Removable') runes (with an @(tsee in-theory) event), resulting in a set
 @('S') of runes reported for that event.  The progress line shows attempts in
 the current round to decrease the number of steps by disabling one rune from
 @('S') per attempt, using @(''.'') for a failed such attempt and @(''+'') for
 a success.  Each such rune is chosen from the list of runes reported for the
 previous round.</p>

 <p>If @(':verbose-p = :minimal'), then the output will be as described above
 except that the @('Removable') and @('Used') fields are omitted.  If
 @(':verbose-p = nil'), then there is no output.  Finally, if @(':verbose-p =
 t'), then all the fields are printed, but in addition you will see the usual
 output for each attempt, each (except for the initial event) preceded by the
 corresponding @(tsee in-theory) event.</p>

 <p>We now say a bit more about the tool's algorithm as we describe the
 @(':multiplier') argument, which is 1 by default but can also be any positive
 rational number.  Recall that each round is an attempt to find a rune to
 disable: specifically, one that provides the fewest number of resulting prover
 steps.  The multiplier provides a bound on the number of prover steps: if
 @('s0') is the number of steps for the preceding (or initial) round, then the
 number of steps for the next round is not allowed to exceed @('(floor (* m s0)
 1)'), where @('m') is the value of the @(':multiplier') keyword.  If this
 bound reaches 0 (which can only happen if @('m < 1'), the algorithm
 terminates.</p>

 <p>As promised above, we now explain why it is generally best to avoid using
 @(':')@(tsee in-theory) @(see hints) in the form you supply to
 @('removable-runes') or its related utility, @('minimal-runes').  To see why,
 consider the following example.  First evaluate:</p>

 @({
 (include-book \"tools/removable-runes\" :dir :system)
 (defund foo (x) (cons x x))
 })

 <p>Notice that @('foo') is now @(see disable)d; see @(see defund).  The
 following example may seem surprising; an explanation is below.</p>

 @({
 ACL2 !>(removable-runes
         (thm (equal (foo x) (cons x x))
              :hints ((\"Goal\" :in-theory (enable foo)))))
 -
 New steps: 15 (initial attempt)
 Time: 0.00
 Used: ((:DEFINITION FOO))
 +
 New steps: 15
 Old steps: 15 (Initially: 15)
 Time: 0.00
 Removed: (:DEFINITION FOO)
 Removable:
 ((:DEFINITION FOO))
 Used:
 ((:DEFINITION FOO))

  ((:DEFINITION FOO))
 ACL2 !>
 })

 <p>The result is that the definition of @('foo') is removable, i.e., can be
 disabled; yet clearly that definition is needed for the proof!  To understand
 this possibly surprising result, understand that @('removable-runes') precedes
 each proof attempt by globally disabling the candidate set of removable runes.
 So in essence the proof attempt when attempting to disable the definition of
 @('foo') is really as follows.</p>

 @({
 (progn (in-theory (disable foo))
        (thm (equal (foo x) (cons x x))
             :hints ((\"Goal\" :in-theory (enable foo)))))
 })

 <p>Obviously the hint takes precedence over the initial @('in-theory') event,
 which is why the proof succeeds.  The moral of the story is this: avoid
 @(':in-theory') hints when using @('removable-runes') or its companion tool,
 @(tsee minimal-runes).  Instead, you could do this, for example:</p>

 @({
 (in-theory (enable foo))
 (removable-runes
  (thm (equal (foo x) (cons x x))))
 })

 <p>Finally, we expand on a point made above.  When a rune is chosen to add to
 the evolving list of disables, the corresponding proof attempt might actually
 involve runes that were not present in any earlier proof attempt.  Any new
 such runes are then considered for disabling in later rounds.</p>")

(defxdoc minimal-runes
  :parents (proof-automation debugging)
  :short "Compute @(see rune)s to leave @(see enable)d"
  :long "@({

 Example Form:
 (minimal-runes (defun proper-cons-nest-p (x)
                  (declare (xargs :guard (pseudo-termp x)))
                  (cond ((symbolp x) nil)
                        ((fquotep x) (true-listp (cadr x)))
                        ((eq (ffn-symb x) 'cons)
                         (proper-cons-nest-p (fargn x 2)))
                        (t nil)))
                  :verbose-p :minimal)

 General Form:
 (minimal-runes event-form
                :verbose-p  v ; default = :normal ;
                :multiplier m ; default = 1 ;
                :name       n ; default = nil ;
                )
 })

 <p>where @('event-form') is an embeddable event (see @(see events)); @('v') is
 @('nil'), @(':minimal'), @(':normal'), or @('t'); @('m') is a positive
 rational number; and n is nil or a @(see logical-name).  The value returned is
 an @(see error-triple) @('(mv erp runes state)'), where @('erp') is typically
 @('nil') and @('runes') is a list of @(see rune)s that suffice to admit
 the indicated @('event-form'); moreover, if the multiplier @('m') is less
 than 1, then the event is admitted with fewer prover steps.</p>

 <p>This utility is essentially identical to @('removable-runes') &mdash;
 indeed, they share the same algorithm &mdash; except that instead of returning
 a list of @(see rune)s to disable, it returns a list of runes sufficient for
 admitting the event.  See @(see removable-runes) for detailed documentation.
 There is one other difference: @('minimal-runes') has an extra keyword
 argument, @(':name').  If @(':name') is supplied then its value must be a
 symbol, @('n'), that is a @(see logical-name).  In that case, the list of
 runes returned is modified by first removing all those in @('(current-theory
 n)'); see @(see current-theory).</p>")

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

(defun removable-runes-next (form steps-bound runes
                                  best-rune best-used best-time ; initially nil
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
                (list* steps-bound best-rune best-used best-time))))
   (t
    (mv-let (erp steps/runes/time state)
      (event-steps-runes+ form steps-bound (cons (car runes) disables)
                          verbose-p ignored-runes state)
      (let ((steps2 (car steps/runes/time))
            (runes2 (cadr steps/runes/time))
            (time2 (cddr steps/runes/time)))
        (cond
         ((null steps2)
          (value (abort!)))
         ((or erp
              (eql steps2 :error) ; see event-steps-runes-form
              (> steps2 steps-bound)    ; impossible?
              )
          (pprogn
           (rrv :minimal (princ$ #\. channel state))
           (removable-runes-next form steps-bound (cdr runes)
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

(defun newline-when-minimal-rrv (verbose-p channel state)

; Yuck; rrv isn't sufficiently flexible here, so I'll break that abstraction.

  (cond ((eq verbose-p :minimal)
         (newline channel state))
        (t state)))

(defun removable-runes-print-status (s s-old r used init-s time
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
       (pprogn (rrv :minimal
                    (fms "New steps: ~x0 (initial attempt)~|Time: ~s1"
                         (list (cons #\0 s)
                               (cons #\1 time-string))
                         channel state nil))
               (newline-when-minimal-rrv verbose-p channel state)
               (rrv :normal
                    (fms "Used: ~y0"
                         (list (cons #\0 used))
                         channel state nil))))
      (t
       (pprogn (rrv :minimal
                    (fms "New steps: ~x0~|Old steps: ~x1 (Initially: ~
                          ~x2)~|Time: ~s3~|Removed: ~x4"
                         (list (cons #\0 s)
                               (cons #\1 s-old)
                               (cons #\2 init-s)
                               (cons #\3 time-string)
                               (cons #\4 r))
                         channel state nil))
               (rrv :normal (fms "Removable:~|~y0Used:~|~y1"
                                 (list (cons #\0 disables)
                                       (cons #\1 used))
                                 channel state nil))
               (newline-when-minimal-rrv verbose-p channel state)))))))

(defun removable-or-minimal-runes-loop
    (form steps-bound previous-steps init-steps runes disables seen verbose-p
          ignored-runes multiplier channel state flg)

; Flg is t for removable-runes and nil for minimal-runes.

  (cond
   ((or (null runes)
        (zerop steps-bound))
    (pprogn (rrv :minimal (newline channel state))
            (value (if flg disables runes))))
   (t
    (er-let* ((s/r/used/time
               (removable-runes-next
                form steps-bound runes nil nil nil
                disables verbose-p ignored-runes channel state)))
      (cond
       ((null s/r/used/time)
        (pprogn (rrv :minimal (newline channel state))
                (value (if flg disables runes))))
       (t
        (let* ((s (car s/r/used/time))
               (r (cadr s/r/used/time))
               (used (caddr s/r/used/time))
               (time (cdddr s/r/used/time))
               (disables (cons r disables)))
          (pprogn
           (removable-runes-print-status s
                                         previous-steps
                                         r
                                         used
                                         init-steps
                                         time
                                         disables verbose-p channel state)
           (assert$
            (and (member-equal r seen)
                 (<= s steps-bound))
            (cond
             ((zp s) (value (if flg disables used)))
             (t
              (removable-or-minimal-runes-loop
               form
               (floor (* multiplier s) 1)
               s init-steps
               (union-equal (set-difference-equal used seen)
                            (remove1-equal r runes))
               disables
               (union-equal used seen)
               verbose-p ignored-runes multiplier channel state
               flg))))))))))))

(defun removable-or-minimal-runes-fn (form verbose-p multiplier ctx state flg)
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
                                              nil nil runes2 nil
                                              time2
                                              nil
                                              verbose-p channel state)
                (removable-or-minimal-runes-loop
                 form
                 (floor (* multiplier steps2) 1)
                 steps2
                 steps2
                 runes2
                 nil
                 runes2
                 verbose-p ignored-runes multiplier channel state
                 flg)))))))

(defun minimal-runes-fn (form verbose-p multiplier ctx state name)
  (er-let* ((theory (if name
                        (let ((world (w state)))
                          (value (current-theory name)))
                      (value nil)))
            (runes (removable-or-minimal-runes-fn form verbose-p multiplier ctx
                                                  state nil)))
    (value (if name ; optimization
               (set-difference-equal runes theory)
             runes))))

(defmacro removable-runes (form &key (verbose-p ':normal) (multiplier '1))

; Note that multiplier is not evaluated.

  (declare (xargs :guard (and (member-eq verbose-p *rrv-levels*)
                              (rationalp multiplier)
                              (< 0 multiplier))))
  `(removable-or-minimal-runes-fn ',form ,verbose-p ,multiplier
                                  'minimize-theory state t))

(defmacro minimal-runes (form &key
                                (verbose-p ':normal)
                                (multiplier '1)
                                name)

; Note that multiplier is not evaluated.

  (declare (xargs :guard (and (member-eq verbose-p *rrv-levels*)
                              (rationalp multiplier)
                              (< 0 multiplier))))
  `(minimal-runes-fn ',form ,verbose-p ,multiplier 'minimize-theory state
                     ',name))
