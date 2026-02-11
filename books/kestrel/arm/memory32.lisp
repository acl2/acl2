; ARM32 memory regions
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

(include-book "portcullis")
(include-book "kestrel/memory/make-memory-region-machinery" :dir :system)

(acl2::make-memory-region-machinery 32 "ARM") ; todo: same as the version in the R package for risc-v ; todo: use the A package?
