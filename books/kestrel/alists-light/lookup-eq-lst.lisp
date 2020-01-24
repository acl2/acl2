; Look up a list of keys, using LOOKUP-EQ.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "lookup-eq")

(defun lookup-eq-lst (keys alist)
  (declare (xargs :guard (if (symbol-listp keys)
                             (alistp alist)
                           (symbol-alistp alist))))
  (if (atom keys)
      nil
    (cons (lookup-eq (car keys) alist)
          (lookup-eq-lst (cdr keys) alist))))
