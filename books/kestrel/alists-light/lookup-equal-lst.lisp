; Look up a list of keys, using LOOKUP-EQUAL
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "lookup-equal")

(defun lookup-equal-lst (keys alist)
  (declare (xargs :guard (and (true-listp keys)
                              (alistp alist))))
  (if (atom keys)
      nil
    (cons (lookup-equal (car keys) alist)
          (lookup-equal-lst (cdr keys) alist))))
