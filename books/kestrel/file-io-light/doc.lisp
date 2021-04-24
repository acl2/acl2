(in-package "ACL2")

(include-book "kestrel/utilities/gen-xdoc-for-file" :dir :system)

;; (depends-on read-file-into-character-list.lisp")
(acl2::gen-xdoc-for-file
 "read-file-into-character-list.lisp"
 (;; (read-file-into-character-list-fn "Read a file into a character-list.") ;; todo: I would like this to be on the same xdoc page as read-file-into-character-list but not be a separate topic
  (read-file-into-character-list "Read a file into a character-list.")
  )
 (io))
