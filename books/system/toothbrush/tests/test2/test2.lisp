; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann, November, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Here we test stobjs.  We also check that generated toothbrush application
; files include ACL2 definitions of system functions not included in the system
; toothbrush files.

(in-package "ACL2")

(defstobj st fld1 fld2)

(verify-termination symbol-name-equal) ; and guards

(defun foo (y)
  (declare (xargs :guard t))
  (if (symbol-name-equal y "A")
      'a-changed
    y))

(defun my-update (x st)

; Note: symbol-name-equal is defined in ACL2 source file other-events.lisp.

  (declare (xargs :stobjs st))
  (let ((st (update-fld1 (foo x) st)))
    (update-fld2 (foo 'a) st)))

(defun top (x st)
  (declare (xargs :stobjs st))
  (my-update x st))
