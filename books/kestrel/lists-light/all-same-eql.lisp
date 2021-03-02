; A variant of all-same that uses eql as the test.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-eql-dollar")

;todo: disable
;todo: improve guard
;; A variant of all-same that uses eql as the test.
(defun all-same-eql (lst)
  (declare (xargs :guard (and (true-listp lst)
                              (eqlablep (car lst)))))
  (or (atom lst)
      (all-eql$ (first lst) (rest lst))))
