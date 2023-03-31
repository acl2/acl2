; Top book of the file-io library
;
; Copyright (C) 2017-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "typed-io-listp")
(include-book "channels")

;; Built-in channel functions:
(include-book "open-input-channel")
(include-book "open-output-channel")
(include-book "open-output-channel-bang")

;; Built-in read functions (one for each kind of channel):
(include-book "read-byte-dollar")
(include-book "read-char-dollar")
(include-book "read-object")

;; Built-in write functions:
(include-book "write-byte-dollar")
(include-book "princ-dollar") ; can write any atom
(include-book "print-object-dollar-fn")
(include-book "print-object-dollar")

(include-book "prin1-with-slashes1")
(include-book "prin1-with-slashes")
(include-book "prin1-dollar")

;; Functions defined in this library:

(include-book "read-object-from-file") ; reading a single object
(include-book "read-objects-from-file")
(include-book "read-file-into-byte-list")
(include-book "read-file-into-character-list")
(include-book "read-file-into-byte-array-stobj")
(include-book "read-file-into-byte-array-stobj2")
(include-book "read-file-into-character-array-stobj")

(include-book "write-bytes-to-channel")
(include-book "write-bytes-to-file")
(include-book "write-bytes-to-file-bang")

(include-book "write-strings-to-channel") ; uses princ$
(include-book "write-strings-to-file")
(include-book "write-strings-to-file-bang")

(include-book "write-objects-to-channel")
(include-book "write-objects-to-file")
(include-book "write-objects-to-file-bang")

(include-book "file-write-date-dollar")
(include-book "file-length-dollar")
(include-book "file-is-newer-thanp")

(include-book "doc")
