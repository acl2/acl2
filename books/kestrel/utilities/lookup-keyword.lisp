; A function to look up a keyword in a keyword-value-list
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defun lookup-keyword (keyword l)
  (declare (xargs :guard (keyword-value-listp l)))
  (cadr (assoc-keyword keyword l)))

;ensures that the keyword is present
(defun lookup-keyword-safe (keyword l)
  (let ((res (assoc-keyword keyword l)))
    (if (not res)
        (er hard? 'lookup-keyword-safe "The keyword ~x0 is not present in the alist ~x1." keyword l)
      (cadr res))))
