; Top book of the file-io library
;
; Copyright (C) 2017-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Users of file-io-light should generally not include this book, as it brings
;; in more than most users need.

;; Note that some of the books included below require trust tags.

(include-book "typed-io-listp")

(include-book "channels")

(include-book "iprint-oracle-updates")

;; Built-in channel functions:
(include-book "open-channels-p")
(include-book "open-input-channel-p")
(include-book "open-output-channel-p")
;; Opening channels:
(include-book "open-input-channel")
(include-book "open-output-channel")
(include-book "open-output-channel-bang")
;; Closing channels:
(include-book "close-input-channel")
(include-book "close-output-channel")

;; TODO: Consider using "print" instead of "write" for the channel operations:

;; Reading from :byte channels:
(include-book "read-byte-dollar") ; read-byte$ is built-in
(include-book "read-bytes-from-channel")
;; Writing to :byte channels:
(include-book "write-byte-dollar") ; write-byte$ is built-in
(include-book "write-bytes-to-channel")

;; Reading from :character channels:
(include-book "read-char-dollar") ; read-char$ is built-in
;; Writing to :character channels:
(include-book "princ-dollar") ; can write any atom, princ$ is built-in
(include-book "prin1-with-slashes1") ; built-in, supports prin1$
(include-book "prin1-with-slashes") ; built-in, supports prin1$
(include-book "prin1-dollar") ; prin1$ is built-in, print an atom
(include-book "write-strings-to-channel") ; uses princ$, todo: make a version for prin1$
(include-book "newline")

;; Reading from :object channels:
(include-book "read-object") ; built-in
(include-book "read-objects-from-channel")
;; Writing to :object channels:
(include-book "print-object-dollar-fn") ; print-object$-fn is built-in
(include-book "print-object-dollar") ; print-object$ is built-in
(include-book "write-objects-to-channel")

;; Operations on files:

;; Reading/writing bytes:
(include-book "read-file-into-byte-list")
(include-book "read-file-into-byte-array-stobj")
(include-book "read-file-into-byte-array-stobj2")
(include-book "write-bytes-to-file")
(include-book "write-bytes-to-file-bang")

;; Reading/writing characters:
(include-book "read-file-into-character-list")
(include-book "read-file-into-character-array-stobj")
(include-book "read-file-into-line-list")
(include-book "write-strings-to-file")
(include-book "write-strings-to-file-bang")

;; Reading/writing objects:
(include-book "read-object-from-file") ; reading a single object
(include-book "read-objects-from-file")
(include-book "read-objects-from-file-with-pkg")
(include-book "read-objects-from-book") ; using the package of the book
(include-book "write-objects-to-file")
(include-book "write-objects-to-file-bang")

;; Misc file utilities:
(include-book "file-write-date-dollar")
(include-book "file-length-dollar")
(include-book "file-is-newer-thanp")

(include-book "doc")
