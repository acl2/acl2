; Top-level book for Kestrel x86 library
;
; Copyright (C) 2021-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "portcullis")
(include-book "parsers/top")
(include-book "tools/top")

;; These could be added to books/projects/x86isa:
(include-book "linear-memory")
(include-book "canonical")
(include-book "canonical-unsigned")
(include-book "state")


(include-book "register-readers-and-writers32")
(include-book "register-readers-and-writers64")
(include-book "readers-and-writers64")
(include-book "flags")
(include-book "conditions")
(include-book "zmm")

(include-book "support-bv")
(include-book "support-x86")
(include-book "x86-changes")
(include-book "support32")
(include-book "memory32")
(include-book "read-over-write-rules")
(include-book "write-over-write-rules")
(include-book "read-over-write-rules32")
(include-book "write-over-write-rules32")
(include-book "read-over-write-rules64")
(include-book "write-over-write-rules64")
(include-book "read-and-write")
(include-book "read-and-write2")
(include-book "read-bytes-and-write-bytes")
(include-book "bytes-loadedp")
(include-book "support2")
(include-book "alt-defs")

(include-book "assumptions")
(include-book "assumptions32")
(include-book "assumptions64")

(include-book "run-until-return")
(include-book "run-until-return2")
(include-book "run-until-return3")
(include-book "run-until-return4")
(include-book "separate")
(include-book "support")
