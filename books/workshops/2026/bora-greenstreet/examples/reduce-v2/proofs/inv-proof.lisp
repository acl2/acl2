; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")

(include-book "run/top")
(include-book "deliver")
(include-book "termination")

(defrule inv-of-erl-step-of-assoc
  (implies
    (and (network-p net) (inv-all net)
         (omap::assoc pid (erl-step net)))
    (inv pid (erl-step net)))
  :use ((:instance inv-of-erl-step-of-run)
        (:instance inv-of-erl-step-of-deliver))
  :disable
    (inv-of-erl-step-of-run
     inv-of-erl-step-of-deliver))

(defrule inv-all0-of-erl-step-general
  (implies
    (and (network-p net) (network-p sub) (inv-all net)
         (omap::submap sub (erl-step net)))
    (inv-all0 sub (erl-step net)))
  :enable inv-all0)

(defrule inv-all-of-erl-step
  (implies
    (and (network-p net) (inv-all net))
    (inv-all (erl-step net)))
  :enable inv-all)

(defrule inv-all-of-erl-runner
  (implies
    (and (network-p net) (inv-all net))
    (inv-all (erl-runner net fuel)))
  :enable erl-runner)

; GrandTotal = sum_of_nats(n - 1).
; TODO: rename sum to sum_of_nats
(defrule grand-total-when-terminated
  (implies
    (and (network-p net) (inv-all net) 
         (terminated? net)
         (pid-p pid) (omap::assoc pid net)
         (root-p (omap::lookup pid net)))
    (equal (erl-state->in (proc->s (omap::lookup pid net)))
           (make-erl-val-integer :val (sum (- (omap::size net) 1)))))
  :do-not-induct t
  :disable (inv-of-inv-all wtree-node-p-when-wtree-p)
  :expand ((inv pid net) (wtree-node-p pid net)
           (rightmost-child pid net)
           (rightmost-child0 pid net (omap::size net)))
  :use ((:instance inv-of-inv-all)
        (:instance wtree-node-p-when-wtree-p)))
  
