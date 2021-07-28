; A lightweight book that provides the function bit-listp.
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also bit-listp-rules.lisp

;; match the version in books/kestrel/utilities/typed-lists/bit-listp.
(defun bit-listp (x)
  (declare (xargs :normalize nil
                  :guard t))
  (let ((__function__ 'bit-listp))
    (declare (ignorable __function__))
    (if (consp x)
        (and (bitp (car x))
             (bit-listp (cdr x)))
      (null x))))
