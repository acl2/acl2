(in-package "ACL2")

(make-event
 (prog2$
  (cw "Note from books/system/io.lisp, this book is deprecated.  Use ~
       books/io/base.lisp instead")
  '(value-triple :invisible))
 :check-expansion t)

;; cert_param: (reloc_stub)
(include-book "std/io/base" :dir :system)
