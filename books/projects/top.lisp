; projects/top.lisp
;
; Previously, this book was called doc.lisp and collected xdoc.  But now we
; have top-doc.lisp to collect the xdoc.  So Eric Smith repurposed this book to
; be a regular 'top' book, intended to collect as much of the material from
; this projects/ directory as we can, for inclusion in books/top.lisp.

(in-package "ACL2")

(include-book "include-doc")

;; Brings in many top and doc books:
(include-projects-doc)

(include-book "projects/smtlink/top" :dir :system :ttags :all)

;; TODO: What else can be included here?
