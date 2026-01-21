; Checking whether a list contains any of a given list of items
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Checks whether LIST contains any of the targets
;; May be faster than computing the intersection and checking it for emptiness.
(defund contains-anyp-eq (targets list)
  (declare (xargs :guard (and (symbol-listp targets)
                              (true-listp list))))
  (if (endp targets)
      nil
    (if (member-eq (first targets) list)
        t ; ensures the result is boolean
      (contains-anyp-eq (rest targets) list))))
