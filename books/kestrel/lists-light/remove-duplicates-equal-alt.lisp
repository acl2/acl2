; A variant of remove-duplicates-equal that keeps earlier duplicated items
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "remove-equal"))

;; This version keeps the first of each set of duplicates.
(defund remove-duplicates-equal-alt (x)
  (declare (xargs :guard (true-listp x)))
  (if (endp x)
      nil
    (let ((item (first x)))
      (cons item
            (remove-duplicates-equal-alt
             (if (member-equal item (rest x))
                 (remove-equal item (rest x))
               (rest x)))))))
