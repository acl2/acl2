; Proofs about generalization
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Soundness of the clause built by ACL2's generalization process
;; (generalize-clause, via generalize1), stated using the evaluator
;; generalize-ev.  See README.md.

(include-book "generalize-proofs")
(include-book "generalize-clause-processor")
