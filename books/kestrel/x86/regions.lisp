; Disjointness of memory regions
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "kestrel/memory/make-memory-region-machinery" :dir :system)

;; Make the machinery for the 48-bit usable x86 address space:
(make-memory-region-machinery 48)

;; Make the machinery for the full 65-bit x86 address space, to support
;; reasoning about canonical addresses:
(make-memory-region-machinery 64)
