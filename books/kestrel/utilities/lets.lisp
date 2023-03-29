; Utilities for dealing with lets
;
; Copyright (C) 2015-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; A let looks like (let (...bindings...) ...declares... body)

;; Returns the bindings of TERM, which should be a LET.
(defun let-bindings (term)
  (declare (xargs :guard (true-listp term)))
  (first (rest term)))

;; Returns the declares of TERM, which should be a LET.  Returns a (possibly
;; empty) list.
(defun let-declares (term)
  (declare (xargs :guard (true-listp term)))
  (butlast (rest (fargs term)) 1))

;; Returns the body of TERM, which should be a LET.
(defun let-body (term)
  (declare (xargs :guard (true-listp term)))
  (car (last term)))
