; Utilities for dealing with lambdas
;
; Copyright (C) 2015-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; A let looks like (let (...bindings...) ...declares... body)

;; TERM should be a LET
(defun let-bindings (term)
  (declare (xargs :guard (true-listp term)))
  (first (rest term)))

;; TERM should be a LET
;; Returns a possibly-empty list of declares
(defun let-declares (term)
  (declare (xargs :guard (true-listp term)))
  (butlast (rest (fargs term)) 1))

;; TERM should be a LET
(defun let-body (term)
  (declare (xargs :guard (true-listp term)))
  (car (last term)))
