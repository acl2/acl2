(in-package "ACL2")

(set-state-ok t)

; The first four events below show that we need state-p to be in the guard for
; execution purposes.  (Implementation note: In ACL2 Version 7.4 and probably
; before, oneify-cltl-code failed to pick up (state-p state) in the guard for
; the second definition below.)

(defun my-set-print-radix-ok (x state)
  (declare (xargs :stobjs state
                  :verify-guards t))
  (set-print-radix x state))

(defthm thm-ok
  (equal (my-set-print-radix-ok t 3)
         (put-global 'print-radix t 3)))

(defun my-set-print-radix-problem (x state)
  (declare (xargs :verify-guards t))
  (set-print-radix x state))

(defthm thm-problem
  (equal (my-set-print-radix-problem t 3)
         (put-global 'print-radix t 3)))

; The following events show the importance of including (state-p state) in the
; guard in support of guard verification.

(defun my-table-alist-example-ok (state)
  (declare (xargs :guard t :stobjs state))
  (table-alist 'some-table (w state)))

(set-state-ok t) ; redundant

(defun my-table-alist-example-problem (state)
  (declare (xargs :guard t))
  (table-alist 'some-table (w state)))

(assert-event (equal (guard 'my-table-alist-example-problem nil (w state))
                     '(state-p state)))
