; Memory region machinery for a 32-bit address space
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/x86/portcullis" :dir :system)
(include-book "make-memory-region-machinery")

;; Make the machinery for a 32-bit address space (e.g., for RISC-V in 32-bit
;; mode):
(make-memory-region-machinery 32 "X")
