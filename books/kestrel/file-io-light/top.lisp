; Top book of the file-io library
;
; Copyright (C) 2017-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")


;; Books about built-in functions:
(include-book "open-input-channel")
(include-book "open-output-channel")
(include-book "open-output-channel-bang")
(include-book "read-byte-dollar") ; reading a byte
(include-book "read-char-dollar") ; reading a character
(include-book "read-object") ; reading an object
(include-book "write-byte-dollar") ; writing a byte
(include-book "princ-dollar") ; writing an atom (e.g., a character)
(include-book "print-object-dollar") ; writing an object

;; Functions defined in this library:

(include-book "read-object-from-file") ; reading a single object
(include-book "read-objects-from-file")
(include-book "read-file-into-byte-list")
(include-book "read-file-into-character-list")
(include-book "read-file-into-byte-array-stobj")
(include-book "read-file-into-character-array-stobj")

(include-book "write-bytes-to-channel")
(include-book "write-bytes-to-file")
(include-book "write-bytes-to-file-bang")

(include-book "write-strings-to-channel")
(include-book "write-strings-to-file")
(include-book "write-strings-to-file-bang")

(include-book "write-objects-to-channel")
(include-book "write-objects-to-file")
(include-book "write-objects-to-file-bang")

(include-book "file-write-date-dollar")
(include-book "file-length-dollar")
(include-book "file-is-newer-thanp")

(include-book "doc")
