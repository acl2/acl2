; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)
(include-book "tools/er-soft-logic" :dir :system)

(defxdoc er-soft+
  :parents (errors)
  :short "Print an error message and ``cause an error''"
  :long "<p>See @(see er) for relevant background.</p>

 @({
 General Form:
 (er-soft+ ctx erp val fmt-string arg1 arg2 ... argk)
 })

 <p>The form above has the same effect as</p>

 @({
 (er soft ctx fmt-string arg1 arg2 ... argk)
 })

 <p>but unlike the latter call, the call of @('er-soft+') generates
 @(':')@(tsee logic) mode code and returns the @(see error-triple) @('(mv erp
 val state)') instead of always returning @('(mv t nil state)').  Note that if
 @('erp') is @('nil') then this error-triple does not signify an error.</p>

 <p>For a simpler utility that also produces @(':logic') mode code but always
 returns @('(mv t nil state)'), see @(see er-soft-logic).</p>")

(defun error1+ (ctx erp val str alist state)

; This is modified from ACL2 source function error1.

  (declare (xargs :stobjs state))
  (prog2$ (error-fms-soft-logic ctx str alist state)
          (mv erp val state)))

(defmacro er-soft+ (ctx erp val str &rest str-args)
  (let ((alist (make-fmt-bindings '(#\0 #\1 #\2 #\3 #\4
                                    #\5 #\6 #\7 #\8 #\9)
                                  str-args)))
    (list 'error1+ ctx erp val str alist 'state)))

(defxdoc convert-soft-error
  :parents (errors)
  :short "Convert a soft error to have a specified @('(mv erp val state)')"
  :long "<p>See @(see er) for relevant background.</p>

 @({
 General Form:
 (convert-soft-error erp val form)
 })

 <p>where @('form') evaluates to an @(see error-triple).  The macro call above
 is equivalent to @('form'), except that if @('form') evaluates to @('(mv erp0
 val0 state)') where the value of @('erp0') is not @('nil') and @('val0') is
 arbitrary, then @('erp') and @('val') are evaluated and their respective
 values @('e') and @('v') are returned in the resulting error-triple @('(mv erp
 val form)').  Note that it is legal for @('erp') to have value @('nil'), in
 which case that error-triple will not designate an error after all.</p>")

(defmacro convert-soft-error (erp val form)
  `(mv-let (er-convert-soft-error-use-nowhere-else-erp
            er-convert-soft-error-use-nowhere-else-val
            state)
     ,form
     (cond
      (er-convert-soft-error-use-nowhere-else-erp
       (check-vars-not-free
        (er-convert-soft-error-use-nowhere-else-erp
         er-convert-soft-error-use-nowhere-else-val)
        (mv ,erp ,val state)))
      (t (mv er-convert-soft-error-use-nowhere-else-erp
             er-convert-soft-error-use-nowhere-else-val
             state)))))


