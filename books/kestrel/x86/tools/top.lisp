; Top book for Kestrel's x86 tools directory
;
; Copyright (C) 2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Roughly ordered by according to dependencies:
(include-book "portcullis")
(include-book "bitops")
(include-book "linear-memory")
(include-book "register-readers-and-writers")
(include-book "flags")
(include-book "conditions")

(include-book "support-x86")
(include-book "support32")
(include-book "read-over-write-rules")
(include-book "write-over-write-rules")
