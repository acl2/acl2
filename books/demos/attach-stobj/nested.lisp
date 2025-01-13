; Copyright (C) 2024, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See README.txt for an overview of this example.

(in-package "ACL2")

(include-book "mem")

(defstobj st
  (fld :type mem))

(defun st-lookup (i st)
; Read the mem field of st.
  (declare (xargs :stobjs st
                  :guard (mem-indexp i)))
  (stobj-let ((mem (fld st)))
             (v)
             (lookup i mem)
             v))

(defun st-update (i v st)
; Write the mem field of st.
  (declare (xargs :stobjs st
                  :guard (mem-indexp i)))
  (stobj-let ((mem (fld st)))
             (mem)
             (update i v mem)
             st))

; This little test at certification time is skipped by include-book:
(value-triple (st-update 5 'five st)
              :stobjs-out '(st))

; This little test at certification time is skipped by include-book:
(assert-event (equal (st-lookup 5 st)
                     'five))
