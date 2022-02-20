; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc prover-steps-counted
  :parents (system-utilities-non-built-in)
  :short "The prover steps counted for the most recently completed event"
  :long "<p>This tool is deprecated, and may be eliminated soon, because it is
 the same as @('last-prover-steps'), which should be used instead.  See @(see
 last-prover-steps).</p>")

(defun prover-steps-counted (state)
  (declare (xargs :stobjs state
                  :guard (alistp (f-get-global 'last-event-data state))
                  :guard-hints (("Goal" :in-theory (enable state-p1)))))
  (cdr (assoc-eq 'prover-steps-counted
                 (f-get-global 'last-event-data state))))
