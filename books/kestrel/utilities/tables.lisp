; Utilities involving tables
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Since TABLE and related functions can't be called from code.
;; Returns a new world.
;; TODO: What if the table has a guard?
(defun table-programmatic (table-name key-name value wrld)
  (declare (xargs :guard (and (symbolp table-name)
                              ;; no constraint on the key?
                              ;; no constraint on the value
                              (plist-worldp wrld))))
  (let ((old-alist (table-alist table-name wrld)))
    (if (not (alistp old-alist))
        (er hard? 'table-programmatic "Table-alist for ~x0 is not an alist: ~x1." table-name old-alist)
      (putprop table-name
               'table-alist
               (put-assoc-equal key-name value old-alist)
               wrld))))
