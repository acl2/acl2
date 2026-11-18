; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "../erl-in-acl2")

; Some rules about the scheduler

(defrule erl-step-when-terminated
  (implies
    (and (network-p net) (terminated? net))
    (equal (erl-step net) net))
  :enable erl-step)

(defrule erl-step-when-stutter
  (implies
    (and (network-p net)
         (equal (scheduling-kind (schedule net)) :stutter))
    (equal (erl-step net) net))
  :enable erl-step)

(defrule not-terminated?-when-runnable-or-outbox
  (implies
    (and (network-p net) (omap::assoc pid net)
         (or (equal (proc->ps (omap::lookup pid net)) :idle)
             (equal (proc->ps (omap::lookup pid net)) :receive)
             (proc->outbox (omap::lookup pid net))))
    (not (terminated? net)))
  :enable (terminated? omap::lookup))