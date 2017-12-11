; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc orelse
  :parents (system-utilities)
  :short "Evaluate an event and, if it fails, then evaluate a second event"
  :long "<p>NOTE: Also see @(see orelse*) for a similar utility that allows any
 number of @(see events).</p>

 @({
 General Form:

 (orelse form1 form2
         :quiet      q ; default nil
         :no-error   n ; default nil
         :expansion? e ; default t
 })

 <p>where @('form1') and @('form2') are @(see events) (see @(see
 embedded-event-form)) and the keywords have the indicated defaults.  The
 behavior is as follows: @('form1') is submitted and if that succeeds &mdash;
 that is, if the result is an @(see error-triple) @('(mv nil val state)')
 &mdash; then the @('orelse') call returns that error-triple.  Otherwise, it
 return the result of evaluating @('form2'), except that if that evaluation
 also fails and if @(':no-error') is @('nil') (the default), then evaluation
 concludes by submitting the event @('(value-triple :failed)').</p>

 <p>If @(':quiet') has a non-@('nil') value, then output is suppressed using
 @(tsee with-output) with argument @(':stack :push'), so that @('form1') and
 @('form2') may recover the original output environment using @('with-output')
 with argument @(':stack :pop').</p>

 <p>The sizes of @(see certificate) files may be reduced with @(':expansion?
 t') (the default).  That argument avoids storing a @(tsee make-event)
 expansion for @('(orelse form1 form2 ...)') when evaluation of the first event
 form succeeds.</p>

 <p>See community book @('kestrel/utilities/orelse.lisp') for an utility,
 @('encapsulate-report-errors'), that employs @('orelse').</p>")

(defxdoc orelse*
  :parents (system-utilities)
  :short "Evaluate a sequence of @(see events), until one succeeds"
  :long "<p>@('Orelse*') behaves as described in the documentation for @(see
 orelse), except that @('orelse*') takes a list of forms, as shown below, and
 its default for @(':expansion?') is @('nil').</p>

 @({
 General Form:

 (orelse* (form1 form2 ...)
          :quiet      q ; default nil
          :no-error   n ; default nil
          :expansion? e ; default nil
 })")

(defun orelse-fn (form-list quiet no-error expansion?p)
  (declare (xargs :guard (true-listp form-list)))
  (let ((ev `(make-event '(:or ,@form-list
                               ,@(and no-error '((value-triple :failed))))
                         ,@(and expansion?p
                                `(:expansion? ,(car form-list)))
                         :on-behalf-of :quiet!)))
    (cond (quiet `(with-output
                    ,@(and (eq quiet :stack-push) '(:stack :push))
                    :gag-mode nil
                    :off :all
                    ,ev))
          (t ev))))

(defmacro orelse* (form-list
                  &key
                  quiet
                  no-error
                  expansion?p)
  (orelse-fn form-list quiet no-error expansion?p))

(defmacro orelse (form1 form2
                        &key
                        quiet
                        no-error
                        (expansion?p 't))
  `(orelse* (,form1 ,form2)
            :quiet ,quiet
            :no-error ,no-error
            :expansion?p ,expansion?p))

; The following sample application of orelse is a drop-in replacement for
; encapsulate.  It replaces each event of the encapsulate with an orelse form
; when a given function supplies the alternative.

(defun formal-map (fn lst)
  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) nil)
        (t (cons `(,fn ,(car lst))
                 (formal-map fn (cdr lst))))))

(mutual-recursion

(defun report-event-when-error-fn (event)

; Consider improving this to give special handling to make-event.  Also consider
; single-step macroexpansion on macros (to expose local, progn, encapsulate, or
; perhaps make-event), though that would require passing in the world, in which
; case report-event-when-error would need to invoke make-event.

  (declare (xargs :guard t))
  (cond ((or (atom event)
             (atom (cdr event))) ; for guard
         event)
        ((eq (car event) 'local)
         (list 'local
               (report-event-when-error-fn (cadr event))))
        ((eq (car event) 'progn)
         (cons 'progn
               (report-event-when-error-fn-lst (cdr event))))
        ((eq (car event) 'encapsulate)
         (list* 'encapsulate
                (cadr event)
                (report-event-when-error-fn-lst (cddr event))))
        (t `(orelse ,event
                    (make-event
                     (with-output
                       (er soft "event processing"
                           "The following event failed:~%~X01"
                           ',event
; The use of 12 below is quite arbitrary.  The goal is to print the entire
; event unless it's truly huge.
                           (evisc-tuple 12 12 nil nil)))
                     :on-behalf-of :quiet)))))

(defun report-event-when-error-fn-lst (lst)
  (cond ((atom lst) nil)
        (t (cons (report-event-when-error-fn (car lst))
                 (report-event-when-error-fn-lst (cdr lst))))))
)

(defmacro report-event-when-error (event)
  (report-event-when-error-fn event))

(defun encapsulate-orelse-fn (fn signature events)
  (declare (xargs :guard (true-listp events)))
  `(make-event (let ((events (formal-map ',fn ',events)))
                 (list* 'encapsulate ,signature events))
               :on-behalf-of :quiet!))

(defmacro encapsulate-orelse (fn signature &rest events)
  (encapsulate-orelse-fn fn signature events))

(defmacro encapsulate-report-errors (signature &rest events)
  `(encapsulate-orelse report-event-when-error ,signature ,@events))
