; AIR Library
; Model 0: Dynamic Semantics
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "AIR-M0")

(include-book "dynamic-semantics")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Example
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Example program: INCR, INCR, INCR, DECR, HALT
;; Starting with acc=0, this computes: 0 -> 1 -> 2 -> 3 -> 2 -> halt
(defconst *example-program*
  (list (opcode-incr)
        (opcode-incr)
        (opcode-incr)
        (opcode-decr)
        (opcode-halt)))

;; Verify execution
(assert-event
 (equal (vm-state->acc
         (run (initial-state 0) *example-program* 10))
        2))

(assert-event
 (vm-state->halted
  (run (initial-state 0) *example-program* 10)))
