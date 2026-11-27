; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "wtree/create-wtree")
(include-book "../../scheduler/examples/util")

(local (defun cfs (n) (/ (* n (1+ n)) 2)))

; Remark: index starts at 0, so the trees compute the sum up to (1- index)

; Example 1: Reduce network with 10 processes, running for 40 steps.
; See the whole result with: (print-omap-values (erl-runner (create-wtree 10) 40))
(assert-equal
  (erl-state->in (proc->s (omap::head-val (erl-runner (create-wtree 10) 40))))
  (make-erl-val-integer :val (cfs 9)))

; Example 2: Reduce network with 100 processes.
(assert-equal
  (erl-state->in (proc->s (omap::head-val (erl-runner (create-wtree 100) 400))))
  (make-erl-val-integer :val (cfs 99)))

; Example 3: redyce network with 1000 processes.
(assert-equal
  (erl-state->in (proc->s (omap::head-val (erl-runner (create-wtree 1000) 4000))))
  (make-erl-val-integer :val (cfs 999)))