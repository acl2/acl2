; Helpers for manipulating MV-LET terms
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; General form: (mv-let <vars> <term> ...declares... <body>)

;; TERM should be an MV-LET.
(defun mv-let-vars (term)
  (declare (xargs :guard (true-listp term)))
  (first (fargs term)))

;; TERM should be an MV-LET.
(defun mv-let-term (term)
  (declare (xargs :guard (true-listp term)))
  (second (fargs term)))

(defun mv-let-declares (term)
  (declare (xargs :guard (true-listp term)))
  (butlast (rest (rest (fargs term))) 1))

(defun mv-let-body (term)
  (declare (xargs :guard (true-listp term)))
  (car (last (fargs term))))
