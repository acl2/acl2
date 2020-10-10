; Copyright (C) 2020, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc open-trace-file!
  :parents (trace)
  :short "Redirect trace output to a file, even within events"
  :long "<p>See @(see open-trace-file) for a utility that redirects @(see
 trace) output to a file.  The utility, @('open-trace-file!'), is similar, but
 differs from @('open-trace-file') in the following two ways.</p>

 <ul>

 <li>You can use @('open-trace-file!') within @(tsee make-event) forms, and
 thereby within @(see books).</li>

 <li>An active trust tag is required (see @(see defttag)) when calling
 @('open-trace-file!').</li>

 </ul>

 <p>For example, we can open a trace file as follows, but the second form fails
 to open a trace file if @('open-trace-file!') is replaced by
 @('open-trace-file').</p>

 @({
 (defttag t)
 (make-event
  (pprogn (open-trace-file! \"xx\")
          (value '(value-triple nil))))
 })")

; The uses of trans-eval below is to avoid getting errors from translate -- I
; dare you to try to eliminate either of them!

(defmacro open-trace-file!-1 (filename)
  `(state-global-let*
    ((temp-touchable-vars t set-temp-touchable-vars))
    (trans-eval '(state-global-let*
                  ((writes-okp t))
                  (pprogn (open-trace-file ,filename)
                          (value nil)))
                'open-trace-file! state nil)))

(defmacro open-trace-file! (filename)
  (declare (xargs :guard (stringp filename)))
  `(mv-let (erp val state)
     (cond
      ((ttag (w state))
       (trans-eval '(open-trace-file!-1 ,filename)
                   'open-trace-file! state nil))
      (t (prog2$ (er hard 'open-trace-file!
                     "It is illegal to call open-trace-file! unless there is ~
                      an active trust tag.  See :DOC defttag.")
                 (value nil))))
     (declare (ignore erp val))
     state))
