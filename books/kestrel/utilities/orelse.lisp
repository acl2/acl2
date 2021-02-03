; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)
(include-book "kestrel/event-macros/fail-event" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)

(defxdoc orelse
  :parents (system-utilities-non-built-in)
  :short "Evaluate an event and, if it fails, then evaluate a second event"
  :long "<p>NOTE: Also see @(see orelse*) for a similar utility that allows any
 number of @(see events).</p>

 @({
 General Form:

 (orelse form1 form2
         :quiet       q ; default nil
         :no-error    n ; default nil
         :expansion?p e ; default t
 })

 <p>where @('form1') and @('form2') are @(see events) (see @(see
 embedded-event-form)) and the keywords have the indicated defaults.  The
 behavior is as follows: @('form1') is submitted and if that succeeds &mdash;
 that is, if the result is an @(see error-triple) @('(mv nil val state)')
 &mdash; then the @('orelse') call returns that error-triple.  Otherwise, it
 return the result of evaluating @('form2'), except that if that evaluation
 also fails and if @(':no-error') is non-@('nil'), then evaluation concludes by
 submitting the event @('(value-triple :failed)').</p>

 <p>If @(':quiet') has a non-@('nil') value, then output is suppressed using
 @(tsee with-output) with argument @(':stack :push'), so that @('form1') and
 @('form2') may recover the original output environment using @('with-output')
 with argument @(':stack :pop').</p>

 <p>The sizes of @(see certificate) files may be reduced with @(':expansion?p
 t') (the default).  That argument avoids storing a @(tsee make-event)
 expansion for @('(orelse form1 form2 ...)') when evaluation of the first event
 form succeeds.</p>

 <p>See community book @('kestrel/utilities/orelse.lisp') for a utility, @(tsee
 encapsulate-report-errors), that employs @('orelse').</p>")

(defxdoc orelse*
  :parents (system-utilities-non-built-in)
  :short "Evaluate a sequence of @(see events), until one succeeds"
  :long "<p>@('Orelse*') behaves as described in the documentation for @(see
 orelse), except that @('orelse*') takes a list of forms.</p>

 @({
 General Form:

 (orelse* (form1 form2 ...)
          :quiet       q ; default nil
          :no-error    n ; default nil
          :expansion?p e ; default t
 })")

(defxdoc on-failure
  :parents (system-utilities-non-built-in)
  :short "Run an event, printing a custom error message if it fails."
  :long "
 @({
 General Form:

 (on-failure event
             :ctx ctx ; default \"event processing\"
             :erp erp ; default t
             :val val ; default nil
             :msg msg ; default nil
             )
 })

 <p>where @('event') is an @(see embedded-event-form), and the other arguments
 are passed to @(tsee fail-event) as explained below.  Thus, none of the
 arguments is evaluated.  The General Form above expands to the following.</p>

 @({
 (ORELSE EVENT
         (FAIL-EVENT CTX ERP VAL MSG))
 })

 <p>Thus, first @('event') is evaluated &mdash; see @(see orelse) &mdash; and
 either it succeeds or else the indicated error occurs &mdash; see @(see
 fail-event).</p>

 <p>Consider the following example.</p>

 @({
 (on-failure (defund f (x) x)
             :ctx (defund . f) ; see :doc ctx
             :erp t   ; see :doc er-soft+
             :val nil ; see :doc er-soft+
             :msg (\"Failed:~|~%~x0\" (#\\0 . (defun f (x) x))))
 })

 <p>If @('f') is not already defined, then this is essentially equivalent to
 @('(defund f (x) x)').  But if @('f') currently has a conflicting definition,
 then the event will fail and the final error message, unless error output is
 inhibited (see @(see set-inhibit-output-lst)), will be the following.</p>

 @({
 ACL2 Error in (DEFUND F ...):  Failed:

 (DEFUN F (X) X)
 })

 <p>For another example of the use of @('on-failure'), which uses the macro
 @(tsee msg) to construct a @(see msgp), see the definition of function
 @('report-event-when-error-fn') in @(see community-book)
 @('books/kestrel/utilities/orelse.lisp').</p>")

(defxdoc encapsulate-report-errors
  :parents (system-utilities-non-built-in)
  :short "Run @(tsee encapsulate), but with a helpful error at the first
 failure of one of its top-level events (if any)."
  :long "<p>This macro is equivalent to @(see encapsulate) except that it takes
 an extra argument, which is a @(see context), that goes in the first
 position.  Unlike @('encapsulate'), it provides a helpful error if any of its
 given @(see events) fails.  It uses that extra `context' argument in reporting
 that error.  (But the error itself is reported by the event, with the usual
 context constructed for that event.)</p>

 @({
 General Form:

 (encapsulate-report-errors ctx signature-list event1 event2 ... eventk)
 })

 <p>where @('ctx') is a context, @('signature-list') is a list of @(see
 signature)s, and each @('eventi') is an @(see embedded-event-form).  Note that
 none of these arguments is evaluated.  Thus, a typical call might be laid down
 as follows.</p>

 @({
 `(encapsulate-report-errors ,ctx () ,@events)
 })

 <p>Normally, if if any of the given events (shown above as ``@('event1 event2
 ... eventk')'') fails, then the output will conclude as follows, where here we
 write @('<CTX>') to denote the formatted context and @('<EV>') to denote the
 failed event printed in abbreviated form.</p>

 @({
 ACL2 Error in <CTX>:  The following event has caused an
 unexpected error:

 <EV>

 Please contact the implementor of the tool that you are using.
 })

 <p>However, if the event is of the form @('(on-failure ...)'), then the
 specified failure message is printed instead of this generic one.  See @(see
 on-failure).</p>")

(defun orelse-fn (form-list quiet no-error expansion?p)
  (declare (xargs :guard (true-listp form-list)))
  (let ((ev `(make-event '(:or ,@form-list
                               ,@(and no-error '((value-triple :failed))))
                         ,@(and expansion?p
                                `(:expansion? ,(car form-list)))
                         :on-behalf-of :quiet!)))
    (cond (quiet `(with-output
                    :stack :push
                    :gag-mode nil
                    :off :all
                    ,ev))
          (t ev))))

(defmacro orelse* (form-list
                  &key
                  quiet
                  no-error
                  (expansion?p 't))
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

(defun formal-map (fn ctx lst)
  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) nil)
        (t (cons `(,fn ,ctx ,(car lst))
                 (formal-map fn ctx (cdr lst))))))

(defmacro on-failure (event &key
                            (ctx '"event processing")
                            (erp 't)
                            val msg)

; This macro generates an event.  The effect of that event is to try the given
; event first, stopping if that succeeds, but otherwise failing.  In the
; failure case we return (mv erp val state) and print the input string, str,
; with fmt arguments (cons event fmt-args).  Except, if str is omitted (or nil)
; then we print a default message as shown below.

; None of the arguments is evaluated; rather, each is passed as is to suitable
; actuals for calls of orelse and fail-event.

  (let ((msg (or msg
                 (msg "The following event failed:~%~X01"
; The use of 12 below is quite arbitrary.  The goal is to print the entire
; event unless it's truly huge.
                      event
                      (evisc-tuple 12 12 nil nil)))))

; It would be much simpler to use the following below:
; (orelse ,event (fail-event ,ctx ,erp ,val ,msg))
; The problem is that then output from make-event -- specifically, from its
; summary -- can be printed.  The :stack :push from ORELSE by using :quiet t
; prevents that, and the use of :stack :pop below (twice) undoes that ":push"
; so that the ambient output environment is used for each event.

    `(orelse (with-output :stack :pop ; see comment above for explanation
               ,event)
             (with-output :stack :pop ; see comment above for explanation
               (fail-event
                ,ctx
                ,erp ; erp
                ,val ; val
                ,msg))
             :quiet t ; see comment above for explanation
             )))

; Below is alternate code that takes advantage of the existing implementation
; of try-event.  It seems to me that the code above is a bit simpler; plus, it
; avoids some potential circularity in books, since as things are now, this
; "orelse" book is included by the "try-event" book.

#||

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

(defxdoc identity-macro
  :parents (system-utilities-non-built-in)
  :short "The most trivial macro imaginable"
  :long "<p>@('(Identity-macro x)') macroexpands to @('x').</p>")

(defmacro identity-macro (x)
  x)

(mutual-recursion

(defun report-event-when-error-fn (ctx event)

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
               (report-event-when-error-fn ctx (cadr event))))
        ((eq (car event) 'progn)
         (cons 'progn
               (report-event-when-error-fn-lst ctx (cdr event))))
        ((eq (car event) 'on-failure)
         event)
        ((eq (car event) 'identity-macro)
         (cadr event))
        ((eq (car event) 'encapsulate)
         (list* 'encapsulate
                (cadr event)
                (report-event-when-error-fn-lst ctx (cddr event))))
        (t `(on-failure ,event
                        :ctx ,ctx
                        :msg ,(msg "The following event has caused an ~
                                    unexpected error:~|~%~x0.~|~%Please ~
                                    contact the implementor of the tool that ~
                                    you are using."
                                   event)))))

(defun report-event-when-error-fn-lst (ctx lst)
  (cond ((atom lst) nil)
        (t (cons (report-event-when-error-fn ctx (car lst))
                 (report-event-when-error-fn-lst ctx (cdr lst))))))
)

(defmacro report-event-when-error (ctx event)
  (report-event-when-error-fn ctx event))

(defun encapsulate-orelse-fn (fn ctx signature events)
  (declare (xargs :guard (true-listp events)))
  `(make-event (let ((events (formal-map ',fn ',ctx ',events)))
                 (list* 'encapsulate ,signature events))
               :on-behalf-of :quiet!))

(defmacro encapsulate-orelse (fn ctx signature &rest events)
  (encapsulate-orelse-fn fn ctx signature events))

(defmacro encapsulate-report-errors (ctx signature &rest events)

; A typical call could be laid down as follows, where call might be
; (my-utility arg1 arg2 ...).

; `(encapsulate-report-errors ,ctx () ,@events)

; Note that ctx is not evaluated.

  `(encapsulate-orelse report-event-when-error ,ctx ,signature ,@events))
