; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book includes MUCH faster after mid-February 2021.  With *big-size-def*
; reduced to 10000, I observed the include-book time to be 0.4 seconds after
; mid-February 2021 but 10.24 seconds before then.  The discrepancy disappears
; when the local form below is included.

; Below, "big-def" comes from the filename.

(in-package "ACL2")

;(local (defun h (x) x))

(defun f (n)
  (declare (xargs :guard (natp n)))
  (cond ((zp n) nil)
        (t (hons (make-list n :initial-element n)
                 (f (1- n))))))

(make-event `(defun big-def1 ()
               (declare (xargs :guard t))
               ',(f 1000)))

(make-event `(defconst *big-def2*
               ',(f 1000)))

(defconst *big-size-def* 10000000)

(defconst *big-def1-list*
  (make-list *big-size-def* :initial-element (big-def1)))

(defconst *big-def2-list*
  (make-list *big-size-def* :initial-element *big-def2*))

(assert-event (equal *big-def1-list* *big-def2-list*)
              :on-skip-proofs t)
