; More utilities for messages (things satisfying msgp)
;
; Copyright (C) 2017-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Extract the string from a msgp
(defun message-string (msg)
  (declare (xargs :guard (msgp msg)))
  (if (stringp msg)
      msg
    (car msg)))

;; Extract the alist from a msgp
(defun message-alist (msg)
  (declare (xargs :guard (msgp msg)))
  (if (stringp msg)
      nil
    (cdr msg)))
