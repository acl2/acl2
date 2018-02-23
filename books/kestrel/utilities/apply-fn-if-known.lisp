; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defun apply-fn-if-known (fn-pkg fn-name args state)
  (declare (xargs :stobjs state :mode :program))
  (cond ((null (find-package-entry fn-pkg (known-package-alist state)))
         (value nil))
        (t (let ((fn (intern$ fn-name fn-pkg))
                 (wrld (w state))
                 (ctx 'apply-pkg-fn))
             (cond ((not (function-symbolp fn wrld))
                    (value nil))
                   ((not (all-nils (stobjs-in fn wrld)))
                    (er soft ctx
                        "The function symbol ~x0 takes a stobj argument, so ~
                         it is illegal to call ~x1 for the fn-pkg and fn-name ~
                         arguments of ~x2 and ~x3, respectively."
                        fn 'apply-fn-if-known fn-pkg fn-name))
                   (t (er-let* ((stobjs-out/replaced-val
                                 (trans-eval `(,fn ,@(kwote-lst args))
                                             ctx
                                             state
                                             t)))
                        (value (cdr stobjs-out/replaced-val)))))))))

(defxdoc apply-fn-if-known
  :parents (kestrel-utilities)
  :short "Apply a function, expressed as a package and a name, if it exists."
  :long "
 @({
 General Form:

 (apply-fn-if-known fn-pkg fn-name args state)
 })

 <p>where @('fn-pkg') and @('fn-name') are strings.</p>

 <p>This utility attempts to apply @('fn-pkg::fn-name') to args, returning an
 error triple as described below.  Here is an example.</p>

 @({
 ACL2 !>(apply-fn-if-known \"ACL2\" \"NTH\" '(2 (a b c d)) state)
  C
 ACL2 !>
 })

 <p>But @('fn-pkg') might not exist!  Even if it exists, @('fn-pkg::fn-name')
 might not be a known function symbol, or it might take a @(see stobj)
 argument.  In any of these cases, we return @('(value nil)').  Otherwise we
 apply @('fn-pkg::fn-name') to the given arguments, @('args'), to obtain a
 result @('val'), returning @('(value val)') &mdash; unless that application
 causes an error, in which case we return an error triple @('(mv e v state)')
 where @('e') is non-@('nil').</p>")
