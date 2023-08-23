; A variant of last-prover-steps that returns 0 instead of nil for easy proofs.
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(verify-termination get-event-data-1) ; can't verify guards
(verify-termination get-event-data)
(verify-termination last-prover-steps)

;; Like last-prover-steps but returns 0 instead of nil for very simple proofs.
;; Still returns the negation of the step-limit, if the step-limit was reached.
(defund last-prover-steps$ (state)
  (declare (xargs :stobjs state
                  :verify-guards nil))
  (let ((steps (last-prover-steps state)))
    ;; replace nil, which can happen for very trivial theorems, with 0:
    (or steps 0)))
