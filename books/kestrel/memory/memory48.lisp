; Memory region machinery for a 48-bit address space
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "make-memory-region-machinery")

;; Make the machinery for a 48-bit address space (e.g., for the canonical
;; region of memory in x86):
(x::make-memory-region-machinery 48)
