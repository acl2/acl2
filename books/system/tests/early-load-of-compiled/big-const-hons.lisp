; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; I think that some variant of this test had a much faster include of the
; certified book after mid-February 2021 than before.  This book does not
; exhibit such a difference, but is a good test nonetheless that we are
; honsing constants when expected using make-event.

; That said: this book includes somewhat faster after mid-February 2021.  0.84
; seconds vs. 1.32 seconds.  The discrepancy disappears when the local form
; below is included.

; Below, "big-ch" comes from the filename.

(in-package "ACL2")

;(local (defun h (x) x))

(defun big-ch (n)
  (declare (xargs :guard (natp n)))
  (cond ((zp n) nil)
        (t (hons (make-list n :initial-element n)
                 (big-ch (1- n))))))

(make-event `(defconst *big-ch1*
               ',(big-ch 1000)))

(make-event `(defconst *big-ch2*
               ',(big-ch 1000)))

(defconst *big-ch-size* 10000000)

(defconst *big-ch1-list*
  (make-list *big-ch-size* :initial-element *big-ch1*))

(defconst *big-ch2-list*
  (make-list *big-ch-size* :initial-element *big-ch2*))

(assert-event (equal *big-ch1-list* *big-ch2-list*)
              :on-skip-proofs t)
