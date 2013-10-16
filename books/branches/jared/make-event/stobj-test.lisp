; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book tests the interaction of make-event with stobjs.  Up through ACL2
; 3.0.1 this book failed to certify, as explained in the "Technical remark"
; below.

(in-package "ACL2")

(defstobj st fld)

(make-event
 (let ((st (update-fld 23 st)))
   (pprogn (princ$ "EXECUTING FIRST MAKE-EVENT." *standard-co* state)
           (newline *standard-co* state)
           (mv-let (erp val state)
                   (defun bar (x) x)
                   (declare (ignore erp val))
                   (mv nil '(value-triple 100) state st))))
 :check-expansion t)

; Technical remark (for implementors rather than users): The following
; value-triple fails if the make-event expansion just above causes reverting to
; the beginning of the book, as explained in a comment in the call of
; find-longest-common-retraction in the definition set-w! in the ACL2 sources.
(value-triple (or (equal (fld st) 23)
                  (er hard 'top "OUCH")))

(make-event
 (let ((st (update-fld 17 st)))
   (pprogn (princ$ "EXECUTING SECOND MAKE-EVENT." *standard-co* state)
           (newline *standard-co* state)
           (mv-let (erp val state)
                   (defun bar (x) x)
                   (declare (ignore erp val))
                   (mv nil '(value-triple 100) state st)))))

; The following succeeds during certification (well, at least when writing the
; .acl2x file) and is ignored during include-book.
(value-triple (or (not (f-get-global 'write-acl2x state))
                  (prog2$ (cw "CHECKING LAST VALUE-TRIPLE~%")
                          (or (equal (fld st) 17)
                              (er hard 'top "OUCH")))))
