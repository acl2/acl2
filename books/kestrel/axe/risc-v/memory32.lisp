; Memory region machinery for a 32-bit address space
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/axe/risc-v/portcullis" :dir :system)
(include-book "kestrel/memory/make-memory-region-machinery" :dir :system)

;; Make the machinery for a 32-bit address space (e.g., for RISC-V in 32-bit
;; mode):
(make-memory-region-machinery 32 "R")
