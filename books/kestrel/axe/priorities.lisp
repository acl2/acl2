; A table to store axe rule priorities
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; We use this to avoid silent failures to update the correct table
;; when in other packages (or we could make the table name a keyword).
;; TODO: Use this more.
(defmacro set-axe-rule-priority (rule priority)
  (declare (xargs :guard (and (symbolp rule)
                              (rationalp priority))))
  `(table axe-rule-priorities-table ',rule ,priority))

;; Get the table with (table-alist 'axe-rule-priorities-table wrld)
