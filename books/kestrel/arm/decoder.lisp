; A decoder for ARM32 instructions
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

(include-book "decoder-tools")
(include-book "encodings")

;; This makes a decoder called arm32-decode that decodes a USB32 into an
;; instruction (any of the instructions in the *patterns*):
(make-event (make-decoder 'arm32-decode *desugared-patterns*))
