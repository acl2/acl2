; Extract and export only Kestrel xdoc material
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/xdoc-archiving" :dir :system)

;; This book exports all the xdoc topics for the kestrel books (topics that
;; come in via the local include of doc.lisp and that were introduced in the
;; books/kestrel/ subtree).  It does not export definitions, theorems, etc.

(local (include-book "doc"))

(xdoc::archive-topics-for-books-tree "kestrel")
(xdoc::archive-current-resource-dirs)
