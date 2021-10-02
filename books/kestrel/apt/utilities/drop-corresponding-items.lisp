; A utility to drop items from a list
;
; Copyright (C) 2014-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Walk through the ITEMS and the KEYS in parallel, dropping any item whose
;; corresponding key is in KEYS-TO-DROP.  For example, the KEYS may be formals
;; of a function and the ITEMS may be actuals.
(defun drop-corresponding-items (items keys keys-to-drop)
  (declare (xargs :guard (and (true-listp items)
                              (symbol-listp keys)
                              (symbol-listp keys-to-drop))))
  (if (endp items)
      nil
    (let ((item (first items))
          (key (first keys)))
      (if (member-eq key keys-to-drop)
          (drop-corresponding-items (rest items) (rest keys) keys-to-drop)
        (cons item (drop-corresponding-items (rest items) (rest keys) keys-to-drop))))))
