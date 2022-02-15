; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc prover-steps-counted
  :parents (system-utilities-non-built-in)
  :short "The prover steps counted for the most recently completed event"
  :long "<p>The @(see summary) printed for an @(see event) typically includes a
 line showing the prover steps counted, for example as follows.</p>

 @({
 Prover steps counted:  7240
 })

 <p>The call @('(prover-steps-counted state)') generally returns the number of
 prover steps counted for the most recently completed event, which is generally
 a positive number.  However, if the most recently completed event fails to
 invoke the prover &mdash; such as @(tsee in-theory) events, most @(tsee table)
 events, and so on, and even trivial proof attempts as with @('(thm (equal x
 x))') &mdash; then @('(prover-steps-counted state)') returns @('nil').
 Finally, if a @(see step-limit) has been installed and is exceeded by the most
 recently completed event, then @('(prover-steps-counted state)') returns a
 negative number whose absolute value is the number of prover steps available
 at the start of that event.</p>

 <p>Note that the ``most recently completed event'' in this sense includes
 compound events.  Consider the following example.</p>

 @({
 (progn (thm (equal (append (append x y) z) (append x y z)))
        (thm (equal (car (cons x y)) x)))
 })

 <p>The summaries show (in some ACL2 versions, at least) 435 steps for the
 first call of @('thm') and 7 steps for the second call of @('thm'), with 442
 steps thus shown in the summary for the entire @('progn') call.  Subsequent
 evaluation of @('(prover-steps-counted state)') returns 442.  On the other
 hand, suppose that @('(set-prover-step-limit 440)') is evaluated immediately
 before evaluating the @('progn') call above.  Then the summaries show the
 following for the two @('thm') calls and the @('progn') call, in order as
 follows.</p>

 @({
 Prover steps counted:  435
 Prover steps counted:  More than 5
 Prover steps counted:  More than 440
 })

 <p>Since the most recently completed event is the @('progn') call, then
 @('(prover-steps-counted state)') returns -440.</p>")

(defun prover-steps-counted (state)
  (declare (xargs :stobjs state
                  :guard (alistp (f-get-global 'last-event-data state))
                  :guard-hints (("Goal" :in-theory (enable state-p1)))))
  (cdr (assoc-eq 'prover-steps-counted
                 (f-get-global 'last-event-data state))))
