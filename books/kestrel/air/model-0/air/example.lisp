; AIR Library
; Model 0: Execution Traces
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "AIR-M0")

(include-book "traces")

(include-book "../language/example")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Example Trace
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *example-trace*
  (generate-trace (initial-state 0) *example-program* 10))

;; The trace should have 6 rows (5 steps + final halted state)
(assert-event (equal (len *example-trace*) 6))

;; First row: pc=0, acc=0, opcode=INCR, halted=nil
(assert-event
 (and (equal (trace-row->pc (trace-first-row *example-trace*)) 0)
      (equal (trace-row->acc (trace-first-row *example-trace*)) 0)
      (not (trace-row->halted (trace-first-row *example-trace*)))))

;; Last row: acc=2, halted=t
(assert-event
 (and (equal (trace-row->acc (trace-last-row *example-trace*)) 2)
      (trace-row->halted (trace-last-row *example-trace*))))
