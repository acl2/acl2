; More utilities for printing DAG arrays
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This one depends on dag-size2.lisp

(include-book "dag-array-printing")
(include-book "dag-size2")

;; Print the term represented by NODENUM-OR-QUOTEP in the DAG, as a term if it
;; won't be too big, otherwise as the relevant nodes from the DAG.
(defun print-dag-node-nicely (nodenum-or-quotep dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (dargp-less-than nodenum-or-quotep dag-len))))
  (if (consp nodenum-or-quotep) ;test for quotep
      (cw "~x0~%" nodenum-or-quotep)
    ;; it's a nodenum:
    (let ((nodenum nodenum-or-quotep))
      (let ((term-size (nfix (size-of-node nodenum dag-array-name dag-array dag-len)))) ;todo: drop the nfix
        (if (< term-size 200)
            (cw "~x0~%" (dag-to-term-aux-array dag-array-name dag-array nodenum))
          (print-dag-only-supporters dag-array-name dag-array nodenum))))))
