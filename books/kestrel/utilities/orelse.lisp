; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)
(include-book "kestrel/utilities/user-interface" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)

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

(defmacro on-failure (event &optional (erp 't) val str &rest fmt-args)

; This macro generates an event.  The effect of that event is to try event
; first, stopping if that succeeds, but otherwise failing.  In the failure case
; we return (mv erp val state) and print the input string, str, with fmt
; arguments (cons event fmt-args).  Except, if str is omitted (or nil) then we
; print a default message as shown below.

; All optional arguments are evaluated.

  (mv-let (str fmt-args)
    (cond (str (mv str (cons event fmt-args)))
          (t (mv "The following event failed:~%~X01"
; The use of 12 below is quite arbitrary.  The goal is to print the entire
; event unless it's truly huge.
                 (list event (evisc-tuple 12 12 nil nil)))))
    `(orelse ,event
             (make-event
              (er-soft+ "event processing"
                ,erp   ; erp
                ,val   ; val
                ,str
                ,@(kwote-lst fmt-args))
              :on-behalf-of :quiet))))

; Below is alternate code that takes advantage of the existing implementation
; of try-event.  It seems to me that the code above is a bit simpler; plus, it
; avoids some potential circularity in books, since as things are now, this
; "orelse" book includes the "user-interface" book, which in turn might include
; "orelse" some day since it defines try-event, which generates a call of
; orelse.

#||
(include-book "kestrel/utilities/user-interface" :dir :system)

(defmacro on-failure (event &optional (erp 't) val str &rest fmt-args)

; Msg is a msgp with the first argument missing.  Thus, if msg is the tuple
; ("..." arg1 arg2 ...) then what is actually passed to ~@0 will be ("..."
; event arg1 arg2 ...).  On failure we return (mv erp val state).  All optional
; arguments are evaluated.

  (mv-let (str fmt-args)
    (cond (str (mv str (cons event fmt-args)))
          (t (mv "The following event failed:~%~X01"
; The use of 12 below is quite arbitrary.  The goal is to print the entire
; event unless it's truly huge.
                 (list event (evisc-tuple 12 12 nil nil)))))
    (try-event event "event processing" erp val
; Roughly speaking, we open-code msg here:
               (cons str (pairlis$
                          '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
                          fmt-args)))))
||#

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
        ((eq (car event) 'on-failure)
         event)
        ((eq (car event) 'encapsulate)
         (list* 'encapsulate
                (cadr event)
                (report-event-when-error-fn-lst (cddr event))))
        (t `(on-failure ,event))))

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
