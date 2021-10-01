; A recognizer for a true list of conses
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note that the cons-listp function from STD does not check that its argument
;; is a true-list, contrary to the convention that FOO-listp functions do so.
(defun cons-listp$ (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x))
           (cons-listp$ (cdr x)))
    (null x)))
