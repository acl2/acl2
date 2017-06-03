; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc orelse
  :parents (system-utilities)
  :short "Evaluate a sequence of forms, until one succeeds"
  :long "<p>Experimental; documentation will come later.  WARNING: This ~
         utility may change!</p>")

(defun orelse-fn (form-list quiet no-error expansion?p)
  (declare (xargs :guard (true-listp form-list)))
  (let ((ev `(make-event '(:or ,@form-list
                               ,@(and no-error '((value-triple :failed))))
                         ,@(and expansion?p
                                `(:expansion? ,(car form-list))))))
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
                  expansion?p)
  (orelse-fn form-list quiet no-error expansion?p))

(defmacro orelse (form1 form2
                        &rest args
                        &key
                        quiet
                        no-error)
  (declare (ignore quiet no-error))
  `(orelse* (,form1 ,form2) :expansion?p t ,@args))

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
                       :stack :pop ; pop inhibition of errors
                       (er soft "event processing"
                           "The following event failed:~%~X01"
                           ',event
; The use of 12 below is quite arbitrary.  The goal is to print the entire
; event unless it's truly huge.
                           (evisc-tuple 12 12 nil nil))))))))

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
                 (list* 'encapsulate ,signature events))))

(defmacro encapsulate-orelse (fn signature &rest events)
  (encapsulate-orelse-fn fn signature events))

(defmacro encapsulate-report-errors (signature &rest events)
  `(encapsulate-orelse report-event-when-error ,signature ,@events))


