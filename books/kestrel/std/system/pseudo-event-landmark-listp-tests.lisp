; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "pseudo-event-landmark-listp")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun latest-event-landmark (wrld)
   (declare (xargs :guard (plist-worldp wrld)))
   (if (endp wrld)
       nil
     (let ((triple (car wrld)))
       (if (eq (car triple) 'event-landmark)
           (cddr triple)
         (latest-event-landmark (cdr wrld))))))
 (assert!
  (pseudo-event-landmark-listp (list (latest-event-landmark (w state))))))
