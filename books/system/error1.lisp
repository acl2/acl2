; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore, July-August 2023
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "fmt-support")
; For abbrev-evisc-tuple and maybe others:
(include-book "system/verified-termination-and-guards" :dir :system)

(local (include-book "error1-support"))

(verify-termination fmt-abbrev1) ; and guards
(verify-termination fmt-abbrev) ; and guards
(verify-termination fmt-ctx) ; and guards
(verify-termination fmt-in-ctx) ; and guards
(verify-termination er-off-p1) ; and guards
(verify-termination er-off-p) ; and guards
(verify-termination error-fms-channel) ; and guards
(verify-termination standard-co) ; and guards
(verify-termination error-fms) ; and guards
(verify-termination error1-state-p) ; and guards
(verify-termination error1) ; and guards
(verify-termination error1-safe) ; and guards

; Examples:

(local (progn

(defun foo (x state)
  (declare (xargs :stobjs state
                  :guard (error1-state-p state)))
  (er soft 'my-top "Ouch: ~x0" x))

(assert-event (mv-let (erp val state)
                (foo (make-list 20) state)
                (declare (ignore val))
                (value erp))
              :stobjs-out '(nil nil state))

(defun foo2 (x state)
  (declare (xargs :stobjs state
                  :guard (error1-state-p state)))
  (er very-soft 'my-top "Ouch: ~x0" x))

(assert-event (mv-let (erp val state)
                (foo2 (make-list 20) state)
                (declare (ignore val))
                (value (null erp)))
              :stobjs-out '(nil nil state))
))
