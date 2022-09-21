; Getting the members of a list that are not in some other list
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Keep the members of X that are not in Y.  Preserves the order.
(defund filter-non-members (x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y))))
  (if (endp x)
      nil
    (let ((x0 (first x)))
      (if (member-equal x0 y)
          (filter-non-members (rest x) y)
        (cons x0 (filter-non-members (rest x) y))))))
