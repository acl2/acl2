; Printing an item to a string
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; todo: make this lowercase?
(defun print-to-string (item)
  (declare (xargs :mode :program))
  (mv-let (col string)
    (fmt1-to-string "~X01" (acons #\0 item (acons #\1 nil nil)) 0
                    :fmt-control-alist
                    `((fmt-soft-right-margin . 10000)
                      (fmt-hard-right-margin . 10000)))
    (declare (ignore col))
    string))
