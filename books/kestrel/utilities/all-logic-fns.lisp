; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(defun all-logic-fns-1 (wrld-tail wrld acc)
  (declare (xargs :guard (and (plist-worldp wrld-tail)
                              (plist-worldp wrld)
                              (symbol-listp acc))))
  (cond
   ((endp wrld-tail) (remove-duplicates-eq acc))
   (t (all-logic-fns-1
       (cdr wrld-tail)
       wrld
       (let ((trip (car wrld-tail)))
         (cond
          ((and (eq (cadr trip) 'formals)
; The following should ensure that the function's definition wasn't erased.
                (member-eq (getpropc (car trip) 'symbol-class nil wrld)
                           '(:ideal :common-lisp-compliant)))
           (cons (car trip) acc))
          (t acc)))))))

(defun all-logic-fns (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (all-logic-fns-1 wrld wrld nil))
