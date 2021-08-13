; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(defun book-of-event (name wrld)

; Evaluate (book-of-event NAME (w state)) to get the pathname of the book in
; which the event named NAME is introduced.  If that event exists but is not
; introduced in a book, return :top-level.  If that event doesn't exist, return
; nil.

  (declare (xargs :mode :program))
  (if (getpropc name 'predefined nil wrld)
      :built-in
    (let ((ev-wrld (decode-logical-name name wrld)))
      (and ev-wrld
           (let ((book-path
                  (getpropc 'include-book-path 'global-value nil ev-wrld)))
             (if book-path
                 (car book-path)
               :top-level))))))
