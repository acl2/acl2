; A lightweight utility to test whether a function is a primitive
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This version doesn't take WRLD.
(defun fn-primitivep-core (fn)
  (declare (xargs :guard (symbolp fn)))
  (if (assoc fn *primitive-formals-and-guards*) t nil))

;; This version takes WRLD and has a strong guard, for consistency with similar
;; functions.
(defund fn-primitivep (fn wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (plist-worldp wrld)
                              (function-symbolp fn wrld)))
           (ignore wrld))
  (fn-primitivep-core fn))
