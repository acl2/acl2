; Documentation for the file-io-light-library
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/gen-xdoc-for-file" :dir :system)
(include-book "output-theory-doc")

(defxdoc file-io-light
  :short "A lightweight library for file input and output."
  :parents (kestrel-books)
  ;; :long todo
  )

;; (depends-on "read-object-from-file.lisp")
(acl2::gen-xdoc-for-file
 "read-object-from-file.lisp"
 ((read-object-from-file "Read an ACL2 object from a file."))
 (io file-io-light))

;; (depends-on "read-objects-from-file.lisp")
(acl2::gen-xdoc-for-file
 "read-objects-from-file.lisp"
 ((read-objects-from-file "Read the ACL2 objects from a file."))
 (io file-io-light))

;; (depends-on "read-file-into-character-list.lisp")
(acl2::gen-xdoc-for-file
 "read-file-into-character-list.lisp"
 ((read-file-into-character-list "Read a file into a character-list."))
 (io file-io-light))

;; (depends-on "read-file-into-byte-list.lisp")
(acl2::gen-xdoc-for-file
 "read-file-into-byte-list.lisp"
 ((read-file-into-byte-list "Read a file into a list of bytes."))
 (io file-io-light))

;; (depends-on "read-file-into-byte-array-stobj.lisp")
(acl2::gen-xdoc-for-file
 "read-file-into-byte-array-stobj.lisp"
 ((read-file-into-byte-array-stobj "Read the bytes from a file into a stobj array."))
 (io file-io-light))

;; (depends-on "read-file-into-character-array-stobj.lisp")
(acl2::gen-xdoc-for-file
 "read-file-into-character-array-stobj.lisp"
 ((read-file-into-character-array-stobj "Read the characters from a file into a stobj array."))
 (io file-io-light))


;; (depends-on "write-bytes-to-channel.lisp")
(acl2::gen-xdoc-for-file
 "write-bytes-to-channel.lisp"
 ((write-bytes-to-channel "Write bytes to an output channel.")
  )
 (file-io-light))

;; (depends-on "write-bytes-to-file.lisp")
(acl2::gen-xdoc-for-file
 "write-bytes-to-file.lisp"
 ((write-bytes-to-file "Write bytes to a file.")
  )
 (file-io-light))

;; (depends-on "write-bytes-to-file-bang.lisp")
(acl2::gen-xdoc-for-file
 "write-bytes-to-file-bang.lisp"
 ((write-bytes-to-file! "Write bytes to a file when not allowed without a trust tag.")
  )
 (file-io-light))

;; (depends-on "write-strings-to-channel.lisp")
(acl2::gen-xdoc-for-file
 "write-strings-to-channel.lisp"
 ((write-strings-to-channel "Write strings to an output channel.")
  )
 (file-io-light))

;; (depends-on "write-strings-to-file.lisp")
(acl2::gen-xdoc-for-file
 "write-strings-to-file.lisp"
 ((write-strings-to-file "Write strings to a file.")
  )
 (file-io-light))

;; (depends-on "write-strings-to-file-bang.lisp")
(acl2::gen-xdoc-for-file
 "write-strings-to-file-bang.lisp"
 ((write-strings-to-file! "Write strings to a file when not allowed without a trust tag.")
  )
 (file-io-light))
