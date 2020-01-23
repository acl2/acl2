; System Utilities -- World Queries -- Tests
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "world-queries")
(include-book "kestrel/utilities/testing" :dir :system)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun latest-command-landmark (wrld)
   (declare (xargs :guard (plist-worldp wrld)))
   (if (endp wrld)
       nil
     (let ((triple (car wrld)))
       (if (eq (car triple) 'command-landmark)
           (cddr triple)
         (latest-command-landmark (cdr wrld))))))
 (comp t) ; seems to be needed for Allegro CL (but isn't for LispWorks; hmm...)
 (assert!
  (pseudo-command-landmark-listp (list (latest-command-landmark (w state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun f (x) x)
 (assert-equal (event-landmark-names (cddr (nth 0 (w state)))) '(f)))

(must-succeed*
 (defun f (x) x)
 (verify-guards f)
 (assert-equal (event-landmark-names (cddr (nth 0 (w state)))) nil))

(must-succeed*
 (mutual-recursion
  (defun f (term)
    (if (variablep term)
        0
      (if (fquotep term)
          0
        (1+ (f-lst (fargs term))))))
  (defun f-lst (terms)
    (if (endp terms)
        0
      (+ (f (car terms))
         (f-lst (cdr terms))))))
 (assert-equal (event-landmark-names (cddr (nth 0 (w state))))
               '(f f-lst)))
