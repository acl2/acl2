; Copyright (C) 2024, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See README.txt for an overview of this example.

; This book provides support for the :LOGIC functions of the abstract stobj,
; mem, introduced in mem.lisp.

(in-package "ACL2")

(defconst *mem-len* 1000) ; 1000 is rather arbitrary.

(defun mem$ap (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (= (length x) *mem-len*)))

(defun create-mem$a ()
  (declare (xargs :guard t))
  (make-list *mem-len*))

(defun mem-indexp (n)
  (declare (xargs :guard t))
  (and (natp n)
       (< n *mem-len*)))

(defun lookup$a (n x)
  (declare (xargs :guard (and (mem-indexp n)
                              (mem$ap x))))
  (nth n x))

(defun update$a (n val x)
  (declare (xargs :guard (and (mem-indexp n)
                              (mem$ap x))))
  (update-nth n val x))
