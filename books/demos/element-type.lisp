; Copyright (C) 2024, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See :DOC defstobj-element-type for relevant explanation.

(in-package "ACL2")

(defconst *ar-size* (expt 10 8))

(defstobj st1
  (ar1 :type (array double-float (*ar-size*))
       :element-type t ; Omit this line to compare times with or without it.
       :initially 0)
; Optional:
  :inline t)

(defun reads-st1 (st1 n)
  (declare (xargs :stobjs st1
                  :guard (and (natp n)
                              (<= n *ar-size*))))
  (cond ((zp n) t)
        (t (let ((n (1- n)))
             (or (df= (ar1i n st1) 1)
                 (reads-st1 st1 n))))))

(defun writes-st1 (st1 d n)
  (declare (xargs :stobjs st1
                  :dfs d
                  :guard (and (natp n)
                              (<= n *ar-size*))))
  (cond ((zp n) st1)
        (t (let ((n (1- n)))
             (let ((st1 (update-ar1i n d st1)))
               (writes-st1 st1 d n))))))

; NOTE: SBCL (or at least some versions of it) cannot handle the argument below
; of *ar-size*, as of this writing (mid-May, 2025).  Consider smaller sizes
; when running the forms below, e.g., (/ *ar-size* 100) or (/ *ar-size* 200).
; (time$ (reads-st1 st1 *ar-size*))
; (time$ (writes-st1 st1 (to-df 2) *ar-size*))
