; Tests of all-included-books
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note that these tests may fail if you LD this file and your
;; acl2-customization file brings in any books.

(include-book "all-included-books")

;; Assert that exactly one book is included:
;; TODO: Check the exact string, but it depends on the user's current directory
; Matt K. mod: The following assertion is false for certain "acl2data" runs.
#-acl2data
(assert-event
 (and (equal (len (all-included-books (w state)))
             1)
      (stringp (first (all-included-books (w state))))))

;; Include some other book:
(include-book "kestrel/lists-light/append" :dir :system)

;; Now there are 2 books included:
; Matt K. mod: The following assertion is false for certain "acl2data" runs.
#-acl2data
(assert-event
 (and (equal (len (all-included-books (w state)))
             2)
      (string-listp (all-included-books (w state)))))
