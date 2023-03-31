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

;; TODO: Consider using "print" instead of "write" for the channel operations:

;; :byte channels:
(include-book "read-byte-dollar") ; read-byte$ is built-in
(include-book "write-byte-dollar") ; write-byte$ is built-in
(include-book "write-bytes-to-channel")

;; :character channels:
(include-book "read-char-dollar") ; read-char$ is built-in
(include-book "princ-dollar") ; can write any atom, princ$ is built-in
(include-book "prin1-with-slashes1") ; built-in
(include-book "prin1-with-slashes") ; built-in
(include-book "prin1-dollar") ; prin1$ is built-in, print an atom
(include-book "write-strings-to-channel") ; uses princ$

;; :object channels:
(include-book "read-object") ; built-in
(include-book "print-object-dollar-fn") ; print-object$-fn is built-in
(include-book "print-object-dollar") ; print-object$ is built-in
(include-book "write-objects-to-channel")

;; Functions defined in this library:

;; Reading/writing bytes:
(include-book "read-file-into-byte-list")
(include-book "read-file-into-byte-array-stobj")
(include-book "read-file-into-byte-array-stobj2")
(include-book "write-bytes-to-file")
(include-book "write-bytes-to-file-bang")

;; Reading/writing characters:
(include-book "read-file-into-character-list")
(include-book "read-file-into-character-array-stobj")
(include-book "write-strings-to-file")
(include-book "write-strings-to-file-bang")

;; Reading/writing objects:
(include-book "read-object-from-file") ; reading a single object
(include-book "read-objects-from-file")
(include-book "write-objects-to-file")
(include-book "write-objects-to-file-bang")

;; Misc file utilities:
(include-book "file-write-date-dollar")
(include-book "file-length-dollar")
(include-book "file-is-newer-thanp")

(include-book "doc")
