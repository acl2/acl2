; Utilities for dealing with lambdas
;
; Copyright (C) 2015-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Returns a possibly-empty list of declares
;; TODO: Also make a let-bindings and a let-body?
(defun let-declares (term)
  (declare (xargs :guard (true-listp term)))
  (butlast (rest (fargs term)) 1))
