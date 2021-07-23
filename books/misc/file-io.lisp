; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Utilities read-list and write-list:

; (Read-list fname ctx state) returns (mv nil lst state) where lst is the list
; of top-level forms in the file named fname.  Except, if there is an error
; then (mv t nil state) is returned.

; (Write-list list fname ctx state) pretty-prints the given list of forms to
; file fname, except that strings are printed without any formatting.

; In each of the above, ctx is generally a symbol used in error messages that
; indicates the caller, e.g., 'top-level.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc write-list
  :parents (io)
  :short "Write a list to a file"
  :long "@({
 Example Forms:

 (write-list '(a b c) \"foo\" 'top-level state)
 (write-list '(a b c) \"foo\" 'top-level state :quiet t)

 General Form:

 (write-list list x ctx state &key :quiet val)
 })

 <p>where all arguments are evaluated and @('state') must literally be the ACL2
 @(see state), @('STATE').  @('List') is a true-list; @('x') is a filename or a
 list of length 1 containing a filename; and @('ctx') is a context (see @(see
 ctx)).  By default or if :quiet is nil, a message of the form @('\"Writing
 file [x]\"') is printed to @(see standard-co); otherwise, no such message is
 printed.</p>

 <p>Also see @(see print-object$) and @(see print-object$+).</p>")

(program)

(set-state-ok t)

(defun collect-objects (list channel state)
  (mv-let (eofp obj state)
	  (read-object channel state)
	  (if eofp
	      (mv (reverse list) state)
	    (collect-objects (cons obj list) channel state))))

; Return (value result) where result is the list of top-level forms in file
; fname:
(defun read-list (fname ctx state)
  (mv-let (channel state)
	  (open-input-channel fname :object state)
          (if channel
              (mv-let (result state)
                      (collect-objects () channel state)
                      (let ((state (close-input-channel channel state)))
                        (value result)))
            (er soft ctx
                "Unable to open file ~s0 for :object input."
                fname))))

(defun pprint-object-or-string (obj channel state)
  (if (stringp obj)
      (princ$ obj channel state)
    (mv-let (erp val state)
            (state-global-let*
             ((write-for-read t))
             (pprogn (ppr2 (ppr1 obj (print-base) (print-radix) 80 0 state t)
                           0 channel state t)
                     (value nil)))
            (declare (ignore erp val))
            state)))

(defun write-objects (list channel state)
  (if (consp list)
      (pprogn (pprint-object-or-string (car list) channel state)
              (newline channel state)
              (newline channel state)
              (write-objects (cdr list) channel state))
    state))

(defun write-list-body-fn (bangp quietp)
  `(let ((quietp ,quietp))
     (if (not (stringp fname))
         (er soft ctx
             "The filename argument of write-list must evaluate to a string, ~
              but it has evaluated to ~x0.  See :DOC write-list."
             fname)
       (mv-let (channel state)
         ,(if bangp
              '(open-output-channel! fname :character state)
            '(open-output-channel fname :character state))
         (if channel
             (mv-let
               (col state)
               (cond (quietp (mv 0 state))
                     (t (fmt1 "Writing file ~x0~%"
                              (list (cons #\0 fname))
                              0 (standard-co state) state nil)))
               (declare (ignore col))
               (let ((state (write-objects list channel state)))
                 (pprogn (close-output-channel channel state)
                         (value :invisible))))
           (er soft ctx
               "Unable to open file ~s0 for :character output."
               fname))))))

(defmacro write-list-body (bangp quietp)
  (write-list-body-fn bangp quietp))

(defun write-list-fn (list fname ctx state quiet)
  (if quiet
      (write-list-body nil t)
    (write-list-body nil nil)))

; Pretty-print the given list of forms to file fname, except that strings are
; printed without any formatting.
(defmacro write-list (list fname ctx state &key quiet)
  (declare (xargs :guard (eq state 'state)))
  `(write-list-fn ,list ,fname ,ctx ,state ,quiet))

; (Downcase form) causes the execution of form but where printing is in
; :downcase mode.  Form must return an error triple.
(defmacro downcase (form)
  `(state-global-let*
    ((print-case :downcase set-print-case))
    ,form))

; Same as write-list above, but where printing is down in downcase mode:
(defmacro write-list-downcase (list fname ctx state &key quiet)
  (declare (xargs :guard (eq state 'state)))
  `(downcase (write-list ,list ,fname ,ctx ,state :quiet ,quiet)))
