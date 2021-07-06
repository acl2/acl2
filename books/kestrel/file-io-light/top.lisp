; Top book of the file-io library
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "open-input-channel")
(include-book "open-output-channel")
(include-book "open-output-channel-bang")

(include-book "read-byte-dollar")
(include-book "read-object")

(include-book "write-byte-dollar")
(include-book "write-bytes-to-channel")
(include-book "write-bytes-to-file")
(include-book "write-bytes-to-file-bang")

(include-book "princ-dollar")
(include-book "write-strings-to-channel")
(include-book "write-strings-to-file")
(include-book "write-strings-to-file-bang")

(include-book "print-object-dollar")
(include-book "write-objects-to-channel")
(include-book "write-objects-to-file")
(include-book "write-objects-to-file-bang")

(include-book "file-write-date-dollar")
(include-book "file-length-dollar")
(include-book "file-is-newer-thanp")

(include-book "read-object-from-file")
(include-book "read-file-into-byte-list")
(include-book "read-file-into-character-list")
(include-book "read-file-into-stobj")

(include-book "doc")
