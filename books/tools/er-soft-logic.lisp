; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc er-soft-logic
  :parents (errors)
  :short "Print an error message and ``cause an error''"
  :long "<p>See @(see er) for relevant background.</p>

 @({
 General Form:
 (er-soft-logic ctx fmt-string arg1 arg2 ... argk)
 })

 <p>The form above has the same effect as</p>

 @({
 (er soft ctx fmt-string arg1 arg2 ... argk)
 })

 <p>but unlike the latter call, the call of @('er-soft-logic') generates
 @(':')@(tsee logic) mode code.  It works by invoking the function call
 @('(error-fms-soft-logic ctx fmt-string alist state)'), where @('alist') is as
 in the @('alist') argument of @(tsee fmt).</p>

 <p>For a similar utility that returns a specified error and value component of
 the returned @(see error-triple), see @(see er-soft+).</p>")

(defun error-fms-soft-logic (ctx str alist state)

; This is modified from ACL2 source function error-fms.

  (declare (xargs :stobjs state))
  (and (f-boundp-global 'abbrev-evisc-tuple state)
       (fmt-to-comment-window "~%~%ACL2 Error in ~x0:  ~@1~%~%"
                              (list (cons #\0 ctx)
                                    (cons #\1 (cons str alist)))
                              0
                              (abbrev-evisc-tuple state))))

(defun error1-logic (ctx str alist state)

; This is modified from ACL2 source function error1.

  (declare (xargs :stobjs state))
  (prog2$ (error-fms-soft-logic ctx str alist state)
          (mv t nil state)))

(defmacro er-soft-logic (ctx str &rest str-args)
  (let ((alist (make-fmt-bindings '(#\0 #\1 #\2 #\3 #\4
                                    #\5 #\6 #\7 #\8 #\9)
                                  str-args)))
    (list 'error1-logic ctx str alist 'state)))
