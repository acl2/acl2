; Documentation for typed-lists-light library
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/gen-xdoc-for-file" :dir :system)
(include-book "all-true-listp")

(defxdoc typed-lists-light
  :short "A lightweight library for lists of items of various types."
  :parents (kestrel-books)
  ;; :long todo
)

(gen-xdoc-for-file "all-true-listp.lisp"
                   ((all-true-listp "Recognize a list of true-lists"))
                   (typed-lists-light))

;; TODO: Add documentation for other files.
