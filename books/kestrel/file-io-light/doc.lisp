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

(defxdoc file-io-light
  :short "A lightweight library for file input and output."
  :parents (kestrel-books)
  ;; :long todo
  )

;; (depends-on "read-file-into-character-list.lisp")
(acl2::gen-xdoc-for-file
 "read-file-into-character-list.lisp"
 (;; (read-file-into-character-list-fn "Read a file into a character-list.") ;; todo: I would like this to be on the same xdoc page as read-file-into-character-list but not be a separate topic
  (read-file-into-character-list "Read a file into a character-list.")
  )
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
