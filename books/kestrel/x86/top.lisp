; Top-level book for Kestrel x86 library
;
; Copyright (C) 2021-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "portcullis")
(include-book "parsers/top")
(include-book "tools/top")

(include-book "linear-memory")
(include-book "register-readers-and-writers32")
(include-book "register-readers-and-writers64")
(include-book "readers-and-writers64")
(include-book "flags")
(include-book "conditions")

(include-book "support-bv")
(include-book "support-x86")
(include-book "support32")
(include-book "read-over-write-rules")
(include-book "write-over-write-rules")
(include-book "read-over-write-rules32")
(include-book "write-over-write-rules32")
(include-book "read-over-write-rules64")
(include-book "write-over-write-rules64")
(include-book "read-and-write")
(include-book "support0")
(include-book "support2")

(include-book "assumptions")
(include-book "assumptions32")
(include-book "assumptions64")

(include-book "run-until-return")
(include-book "separate")
(include-book "support")
