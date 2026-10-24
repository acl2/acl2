; Proofs about irrelevance elimination
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Soundness of ACL2's irrelevance elimination process
;; (eliminate-irrelevance-clause), stated using the evaluator irrelevance-ev.
;; See README.md.

(include-book "irrelevance-proofs")
(include-book "irrelevance-clause-processor")
